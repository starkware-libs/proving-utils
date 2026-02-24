use std::collections::HashMap;
use std::path::PathBuf;

use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::get_ptr_from_var_name;
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::vm::errors::hint_errors::HintError;
use cairo_vm::vm::vm_core::VirtualMachine;
use starknet_types_core::felt::Felt;

use crate::hints::types::PrivacySimpleBootloaderInput;
use crate::hints::vars;
use crate::hints::SIMPLE_BOOTLOADER_INPUT;

use super::utils::get_program_input_value;

/// Loads privacy simple bootloader input from the program input.
/// Stores the inner `SimpleBootloaderInput` and the `output_preimage_dump_path` separately
/// in the execution scopes.
pub fn load_privacy_simple_bootloader_input(
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let privacy_input: PrivacySimpleBootloaderInput = get_program_input_value(exec_scopes)?;
    exec_scopes.insert_value(
        SIMPLE_BOOTLOADER_INPUT,
        privacy_input.simple_bootloader_input,
    );
    exec_scopes.insert_value(
        vars::OUTPUT_PREIMAGE_DUMP_PATH,
        privacy_input.output_preimage_dump_path,
    );
    Ok(())
}

/// Reads the output elements between `simple_bl_output_start` and `simple_bl_output` pointers
/// and dumps them as JSON to the file path stored in exec scopes under `OUTPUT_PREIMAGE_DUMP_PATH`.
pub fn dump_privacy_simple_bootloader_output_preimage(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let output_start = get_ptr_from_var_name("simple_bl_output_start", vm, ids_data, ap_tracking)?;
    let output_end = get_ptr_from_var_name("simple_bl_output", vm, ids_data, ap_tracking)?;
    let size = (output_end - output_start)?;

    let elements: Vec<Felt> = vm
        .get_integer_range(output_start, size)?
        .into_iter()
        .map(|v| v.into_owned())
        .collect();

    let dump_path: PathBuf = exec_scopes.get(vars::OUTPUT_PREIMAGE_DUMP_PATH)?;
    let json = serde_json::to_string_pretty(&elements).map_err(|e| {
        HintError::CustomHint(format!("Failed to serialize output preimage: {e}").into())
    })?;
    std::fs::write(&dump_path, json).map_err(|e| {
        HintError::CustomHint(
            format!("Failed to write output preimage to {dump_path:?}: {e}").into(),
        )
    })?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use cairo_vm::math_utils::signed_felt;
    use cairo_vm::serde::deserialize_program::ApTracking;
    use cairo_vm::types::exec_scope::ExecutionScopes;
    use cairo_vm::types::layout_name::LayoutName;
    use cairo_vm::types::program::Program;
    use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
    use cairo_vm::vm::vm_core::VirtualMachine;
    use cairo_vm::Felt252;
    use starknet_types_core::felt::Felt;
    use starknet_types_core::hash::Blake2Felt252;

    use super::*;
    use crate::hints::program_hash::compute_program_hash_chain;
    use crate::hints::types::{HashFunc, SimpleBootloaderInput};
    use crate::test_utils::prepare_non_continuous_ids_data_for_test;
    use crate::types::RunMode;
    use crate::{cairo_run_program, ProgramInput, PROGRAM_INPUT};

    #[test]
    fn test_load_privacy_simple_bootloader_input() {
        let mut exec_scopes = ExecutionScopes::new();

        let input_json = r#"{
            "tasks": [],
            "single_page": true,
            "fact_topologies_path": null,
            "output_preimage_dump_path": "/tmp/test_dump.json"
        }"#;
        exec_scopes.insert_value(PROGRAM_INPUT, ProgramInput::Json(input_json.to_string()));

        load_privacy_simple_bootloader_input(&mut exec_scopes).expect("Hint failed unexpectedly");

        let simple_bl_input: SimpleBootloaderInput = exec_scopes
            .get(vars::SIMPLE_BOOTLOADER_INPUT)
            .expect("SimpleBootloaderInput not found in exec scopes");
        assert!(simple_bl_input.tasks.is_empty());
        assert!(simple_bl_input.single_page);

        let dump_path: PathBuf = exec_scopes
            .get(vars::OUTPUT_PREIMAGE_DUMP_PATH)
            .expect("OUTPUT_PREIMAGE_DUMP_PATH not found in exec scopes");
        assert_eq!(dump_path, PathBuf::from("/tmp/test_dump.json"));
    }

    #[test]
    fn test_dump_privacy_simple_bootloader_output_preimage() {
        let expected_felts: Vec<Felt> =
            vec![Felt::from(10u64), Felt::from(20u64), Felt::from(30u64)];

        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();

        // Place two pointer values in memory at (1, 0) and (1, 1):
        //   simple_bl_output_start -> (0, 0)
        //   simple_bl_output       -> (0, n)
        vm.load_data(
            Relocatable::from((1, 0)),
            &[
                MaybeRelocatable::from((0, 0)),
                MaybeRelocatable::from((0, expected_felts.len())),
            ],
        )
        .expect("Failed to load pointer data");

        // Place output felts at (0, 0)..(0, n)
        let output_data: Vec<MaybeRelocatable> = expected_felts
            .iter()
            .map(|f| MaybeRelocatable::from(*f))
            .collect();
        vm.load_data(Relocatable::from((0, 0)), &output_data)
            .expect("Failed to load output data");

        // fp = 2 so that ids resolve: simple_bl_output_start at fp-2 = (1,0), simple_bl_output at
        // fp-1 = (1,1)
        vm.set_fp(2);

        let ids_data = prepare_non_continuous_ids_data_for_test(&[
            ("simple_bl_output_start", -2),
            ("simple_bl_output", -1),
        ]);
        let ap_tracking = ApTracking::new();

        let dump_file = tempfile::NamedTempFile::new().expect("Failed to create temp file");
        let dump_path = dump_file.path().to_path_buf();

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(vars::OUTPUT_PREIMAGE_DUMP_PATH, dump_path.clone());

        dump_privacy_simple_bootloader_output_preimage(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
        )
        .expect("Hint failed unexpectedly");

        let contents = std::fs::read_to_string(&dump_path).expect("Failed to read dump file");
        let felts: Vec<Felt> =
            serde_json::from_str(&contents).expect("Failed to parse dumped JSON");

        assert_eq!(felts, expected_felts);
    }

    /// Runs the privacy simple bootloader with a simple_output task using Blake hashing.
    /// Verifies that the single output felt equals the Blake hash of the preimage elements
    /// dumped to file, and that the preimage structure is correct.
    #[test]
    fn test_privacy_simple_bootloader_output_hash() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let privacy_bl_path = manifest_dir.join(
            "resources/compiled_programs/bootloaders/privacy_simple_bootloader_compiled.json",
        );
        let simple_output_path = manifest_dir
            .join("resources/compiled_programs/test_programs/simple_output_compiled.json");

        let privacy_bl_program = Program::from_file(privacy_bl_path.as_path(), Some("main"))
            .expect("Could not load privacy simple bootloader program.");
        let simple_output_program = Program::from_file(simple_output_path.as_path(), Some("main"))
            .expect("Could not load simple output program.");
        let stripped_program = simple_output_program
            .get_stripped_program()
            .expect("Could not get stripped program.");

        let dump_file = tempfile::NamedTempFile::new().expect("Failed to create temp file");
        let dump_path = dump_file.path().to_path_buf();

        let task_output: Vec<u64> = vec![0, 1, 2];
        let task_output_json: String = serde_json::to_string(&task_output).unwrap();

        let program_input_contents = format!(
            r#"{{
                "tasks": [
                    {{
                        "path": "{}",
                        "program_input": {{
                            "output": {task_output_json}
                        }},
                        "program_hash_function": "blake",
                        "type": "RunProgramTask"
                    }}
                ],
                "single_page": true,
                "output_preimage_dump_path": "{}"
            }}"#,
            simple_output_path.display(),
            dump_path.display(),
        );

        let cairo_run_config = RunMode::Proof {
            layout: LayoutName::starknet_with_keccak,
            dynamic_layout_params: None,
            disable_trace_padding: false,
            relocate_mem: true,
        }
        .create_config();

        let mut runner = cairo_run_program(
            &privacy_bl_program,
            Some(ProgramInput::Json(program_input_contents)),
            cairo_run_config,
            None,
        )
        .expect("Privacy simple bootloader run failed.");

        // Read the dumped preimage felts.
        let dump_contents =
            std::fs::read_to_string(&dump_path).expect("Failed to read output preimage dump file");
        let preimage_felts: Vec<Felt> =
            serde_json::from_str(&dump_contents).expect("Failed to parse preimage felts from JSON");

        // Validate preimage structure:
        //   [n_tasks, task_size, program_hash, ...task_output_elements]
        let expected_program_hash =
            compute_program_hash_chain(&stripped_program, 0, HashFunc::Blake)
                .expect("Failed to compute program hash.");
        let expected_task_size = 2 + task_output.len(); // task_size word + program_hash + output elements

        assert_eq!(
            preimage_felts[0],
            Felt::ONE,
            "First preimage element should be n_tasks = 1"
        );
        assert_eq!(
            preimage_felts[1],
            Felt::from(expected_task_size as u64),
            "Second preimage element should be task size = 2 + output len"
        );
        assert_eq!(
            preimage_felts[2], expected_program_hash,
            "Third preimage element should be the Blake program hash"
        );
        for (i, &expected_val) in task_output.iter().enumerate() {
            assert_eq!(
                preimage_felts[3 + i],
                Felt::from(expected_val),
                "Preimage element at index {} should match task output",
                3 + i
            );
        }
        assert_eq!(
            preimage_felts.len(),
            1 + expected_task_size,
            "Preimage length should be 1 + task_size (1 being n_tasks in this case)"
        );

        // Verify the bootloader output (single felt) equals Blake hash of the full preimage.
        let expected_hash = Blake2Felt252::encode_felt252_data_and_calc_blake_hash(&preimage_felts);

        let mut output_buffer = String::new();
        runner
            .vm
            .write_output(&mut output_buffer)
            .expect("Failed to write VM output.");

        let expected_hash_str =
            signed_felt(Felt252::from_bytes_be(&expected_hash.to_bytes_be())).to_string();
        let output_lines: Vec<&str> = output_buffer.lines().collect();
        assert_eq!(
            output_lines.len(),
            1,
            "Expected exactly 1 output line (blake hash). Got:\n{output_buffer}"
        );
        assert_eq!(
            output_lines[0], expected_hash_str,
            "Privacy bootloader output should equal Blake hash of dumped preimage",
        );
    }
}
