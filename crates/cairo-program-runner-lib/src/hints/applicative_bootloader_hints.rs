use std::collections::HashMap;

use cairo_vm::{
    hint_processor::{
        builtin_hint_processor::hint_utils::{get_ptr_from_var_name, insert_value_from_var_name},
        hint_processor_definition::HintReference,
    },
    serde::deserialize_program::ApTracking,
    types::exec_scope::ExecutionScopes,
    vm::{
        errors::hint_errors::HintError, runners::builtin_runner::OutputBuiltinState,
        vm_core::VirtualMachine,
    },
};

use crate::hints::{
    fact_topologies::{
        add_consecutive_output_pages, write_to_fact_topologies_file, GPS_FACT_TOPOLOGY,
    },
    types::BOOTLOADER_CONFIG_SIZE,
};

use super::{
    fact_topologies::FactTopology, vars, ApplicativeBootloaderInput, BootloaderInput,
    SimpleBootloaderInput, APPLICATIVE_BOOTLOADER_INPUT,
};

/// Implements
/// %{
///     from starkware.cairo.bootloaders.applicative_bootloader.objects import (
///         ApplicativeBootloaderInput,
///     )
///     from starkware.cairo.bootloaders.simple_bootloader.objects import SimpleBootloaderInput
///
///     # Create a segment for the aggregator output.
///     ids.aggregator_output_ptr = segments.add()
///
///     # Load the applicative bootloader input and the aggregator task.
///     applicative_bootloader_input = ApplicativeBootloaderInput.Schema().load(program_input)
///     # TODO(Rei, 01/06/2024): aggregator_task gets use_poseidon from outside? Think about this.
///     aggregator_task = applicative_bootloader_input.aggregator_task
///
///     # Create the simple bootloader input.
///     simple_bootloader_input = SimpleBootloaderInput(
///         tasks=[aggregator_task], fact_topologies_path=None, single_page=True
///     )
///
///     # Change output builtin state to a different segment in preparation for running the
///     # aggregator task.
///     applicative_output_builtin_state = output_builtin.get_state()
///     output_builtin.new_state(base=ids.aggregator_output_ptr)
/// %}
pub fn prepare_aggregator_simple_bootloader_output_segment(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_input: &String = exec_scopes.get_ref(vars::PROGRAM_INPUT)?;
    let applicative_bootloader_input: ApplicativeBootloaderInput =
        serde_json::from_str(program_input).unwrap();
    // Python: ids.aggregator_output_ptr = segments.add()
    let new_segment_base = vm.add_memory_segment();
    insert_value_from_var_name(
        "aggregator_output_ptr",
        new_segment_base,
        vm,
        ids_data,
        ap_tracking,
    )?;

    // Python:
    // applicative_bootloader_input = ApplicativeBootloaderInput.Schema().load(program_input)
    // simple_bootloader_input = SimpleBootloaderInput(
    //     tasks=[aggregator_task], fact_topologies_path=None, single_page=True
    // )

    let simple_bootloader_input: SimpleBootloaderInput = SimpleBootloaderInput {
        tasks: vec![applicative_bootloader_input.aggregator_task.clone()],
        fact_topologies_path: None,
        single_page: true,
    };

    exec_scopes.insert_value(APPLICATIVE_BOOTLOADER_INPUT, applicative_bootloader_input);
    exec_scopes.insert_value(vars::SIMPLE_BOOTLOADER_INPUT, simple_bootloader_input);

    // Python:
    // applicative_output_builtin_state = output_builtin.get_state()
    // output_builtin.new_state(base=ids.aggregator_output_ptr)
    let output_builtin = vm.get_output_builtin_mut()?;
    let applicative_output_builtin_state = output_builtin.get_state();
    output_builtin.new_state(new_segment_base.segment_index as usize, 0, true);
    exec_scopes.insert_value(
        vars::APPLICATIVE_OUTPUT_BUILTIN_STATE,
        applicative_output_builtin_state,
    );

    insert_value_from_var_name(
        "aggregator_output_ptr",
        new_segment_base,
        vm,
        ids_data,
        ap_tracking,
    )?;

    Ok(())
}

/// Implements
///%{
///    from starkware.cairo.bootloaders.bootloader.objects import BootloaderInput
///
///    # Save the aggregator's fact_topologies before running the bootloader.
///    aggregator_fact_topologies = fact_topologies
///    fact_topologies = []
///
///    # Create a segment for the bootloader output.
///    ids.bootloader_output_ptr = segments.add()
///
///    # Create the bootloader input.
///    bootloader_input = BootloaderInput(
///        tasks=applicative_bootloader_input.tasks,
///        fact_topologies_path=None,
///        bootloader_config=applicative_bootloader_input.bootloader_config,
///        packed_outputs=applicative_bootloader_input.packed_outputs,
///        single_page=True,
///    )
///
///    # Change output builtin state to a different segment in preparation for running the
///    # bootloader.
///    output_builtin.new_state(base=ids.bootloader_output_ptr)
///%}
pub fn prepare_root_task_unpacker_bootloader_output_segment(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    // Python: aggregator_fact_topologies = fact_topologies
    //    fact_topologies = []
    let fact_topologies: Vec<FactTopology> = exec_scopes.get(vars::FACT_TOPOLOGIES)?;
    exec_scopes.insert_value(vars::AGGREGATOR_FACT_TOPOLOGIES, fact_topologies);
    exec_scopes.insert_value(vars::FACT_TOPOLOGIES, Vec::<FactTopology>::new());

    // Python: ids.bootloader_output_ptr = segments.add()
    let new_segment_base = vm.add_memory_segment();
    insert_value_from_var_name(
        "bootloader_output_ptr",
        new_segment_base,
        vm,
        ids_data,
        ap_tracking,
    )?;

    let applicative_bootloader_input: &ApplicativeBootloaderInput =
        exec_scopes.get_ref(vars::APPLICATIVE_BOOTLOADER_INPUT)?;

    //    Python: bootloader_input = BootloaderInput(
    //        tasks=applicative_bootloader_input.tasks,
    //        fact_topologies_path=None,
    //        bootloader_config=applicative_bootloader_input.bootloader_config,
    //        packed_outputs=applicative_bootloader_input.packed_outputs,
    //        single_page=True,
    //    )

    let simple_bootloader_input = SimpleBootloaderInput {
        tasks: applicative_bootloader_input
            .bootloader_input
            .simple_bootloader_input
            .tasks
            .clone(),
        fact_topologies_path: None,
        single_page: true,
    };

    let bootloader_input = BootloaderInput {
        simple_bootloader_input,
        bootloader_config: applicative_bootloader_input
            .bootloader_input
            .bootloader_config
            .clone(),
        packed_outputs: applicative_bootloader_input
            .bootloader_input
            .packed_outputs
            .clone(),
    };

    exec_scopes.insert_value(vars::BOOTLOADER_INPUT, bootloader_input);

    // Python: output_builtin.new_state(base=ids.bootloader_output_ptr)
    let output_builtin = vm.get_output_builtin_mut()?;
    output_builtin.new_state(new_segment_base.segment_index as usize, 0, true);

    Ok(())
}

/// Implements
///%{
///     # Restore the output builtin state.
///     output_builtin.set_state(applicative_output_builtin_state)
/// %}
pub fn restore_applicative_output_state(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
) -> Result<(), HintError> {
    let output_builtin_state: OutputBuiltinState =
        exec_scopes.get(vars::APPLICATIVE_OUTPUT_BUILTIN_STATE)?;
    vm.get_output_builtin_mut()?.set_state(output_builtin_state);

    Ok(())
}

/// Implements
///%{
///    from starkware.cairo.bootloaders.fact_topology import GPS_FACT_TOPOLOGY, FactTopology
///    from starkware.cairo.bootloaders.simple_bootloader.utils import (
///        add_consecutive_output_pages,
///        write_to_fact_topologies_file,
///    )
///
///    assert len(aggregator_fact_topologies) == 1
///    # Subtract the bootloader output length from the first page's length. Note that the
///    # bootloader output is always fully contained in the first page.
///    original_first_page_length = aggregator_fact_topologies[0].page_sizes[0]
///    # The header contains the program hash and bootloader config.
///    header_size = 1 + ids.BOOTLOADER_CONFIG_SIZE
///    first_page_length = (
///        original_first_page_length - ids.bootloader_tasks_output_length + header_size
///    )
///
///    # Update the first page's length to account for the removed bootloader output, and the
///    # added program hash and bootloader config.
///    fact_topology = FactTopology(
///        tree_structure=aggregator_fact_topologies[0].tree_structure,
///        page_sizes=[first_page_length] + aggregator_fact_topologies[0].page_sizes[1:]
///    )
///    output_builtin.add_attribute(
///        attribute_name=GPS_FACT_TOPOLOGY,
///        attribute_value=aggregator_fact_topologies[0].tree_structure
///    )
///
///    # Configure the memory pages in the output builtin, based on plain_fact_topologies.
///    add_consecutive_output_pages(
///        page_sizes=fact_topology.page_sizes[1:],
///        output_builtin=output_builtin,
///        cur_page_id=1,
///        output_start=ids.output_start + fact_topology.page_sizes[0],
///    )
///
///    # Dump fact topologies to a json file.
///    if applicative_bootloader_input.fact_topologies_path is not None:
///        write_to_fact_topologies_file(
///            fact_topologies_path=applicative_bootloader_input.fact_topologies_path,
///            fact_topologies=[fact_topology],
///        )
///%}
pub fn finalize_fact_topologies_and_pages(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let aggregator_fact_topologies: Vec<FactTopology> =
        exec_scopes.get(vars::AGGREGATOR_FACT_TOPOLOGIES)?;

    if aggregator_fact_topologies.len() != 1 {
        return Err(HintError::CustomHint(
            "Expected exactly one fact topology for the aggregator task".into(),
        ));
    }
    let aggregator_fact_topology = aggregator_fact_topologies.first().unwrap();
    let original_first_page_length = aggregator_fact_topology.page_sizes[0];
    let header_size = 1 + BOOTLOADER_CONFIG_SIZE;
    let bootloader_output_end =
        get_ptr_from_var_name("bootloader_output_end", vm, ids_data, ap_tracking)?;
    let bootloader_output_start =
        get_ptr_from_var_name("bootloader_tasks_output_ptr", vm, ids_data, ap_tracking)?;

    // Because of how limited the LambdaClass reference parser is, we can't take the value straight
    // from the reference "bootloader_tasks_output_length" and have to calculate it manually
    // with simple references that the parser can handle.
    // i.e. fn `parse_value`` can't handle the reference `cast([fp + 14] - ([fp + 3] + 3), felt)`,
    // so we take [fp + 14] and ([fp + 3] + 3) separately and calculate the value manually.
    // Think if we want to invest time in fixing this.
    let bootloader_tasks_output_length =
        bootloader_output_end.offset - bootloader_output_start.offset;

    let first_page_length =
        original_first_page_length - bootloader_tasks_output_length + header_size;

    let fact_topology = vec![FactTopology {
        tree_structure: aggregator_fact_topology.tree_structure.clone(),
        page_sizes: vec![first_page_length]
            .into_iter()
            .chain(aggregator_fact_topology.page_sizes[1..].to_vec())
            .collect(),
    }];

    let output_start = get_ptr_from_var_name("output_start", vm, ids_data, ap_tracking)?;
    let output_builtin = vm.get_output_builtin_mut()?;
    output_builtin.add_attribute(
        GPS_FACT_TOPOLOGY.into(),
        fact_topology[0].tree_structure.clone(),
    );

    let output_start = (output_start + fact_topology[0].page_sizes[0])?;
    let _ = add_consecutive_output_pages(
        &fact_topology[0].page_sizes[1..],
        output_builtin,
        1, // Starting page ID
        output_start,
    )?;

    let applicative_bootloader_input: &ApplicativeBootloaderInput =
        exec_scopes.get_ref(vars::APPLICATIVE_BOOTLOADER_INPUT)?;

    if let Some(path) = &applicative_bootloader_input
        .bootloader_input
        .simple_bootloader_input
        .fact_topologies_path
    {
        write_to_fact_topologies_file(path.as_path(), &fact_topology)
            .map_err(Into::<HintError>::into)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::hints::fact_topologies::FactTopology;
    use crate::hints::types::{BootloaderConfig, SimpleBootloaderInput};
    use crate::hints::types::{Cairo0Executable, Task, TaskSpec};
    use crate::hints::vars;
    use crate::test_utils::prepare_ids_data_for_test;
    use crate::types::HashFunc;
    use cairo_vm::hint_processor::builtin_hint_processor::hint_utils::insert_value_from_var_name;
    use cairo_vm::hint_processor::hint_processor_definition::HintReference;
    use cairo_vm::serde::deserialize_program::ApTracking;
    use cairo_vm::types::exec_scope::ExecutionScopes;
    use cairo_vm::types::program::Program;
    use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
    use cairo_vm::vm::errors::hint_errors::HintError;
    use cairo_vm::vm::runners::builtin_runner::BuiltinRunner;
    use cairo_vm::vm::vm_core::VirtualMachine;
    use cairo_vm::Felt252;
    use num_traits::ToPrimitive;
    use rstest::{fixture, rstest};
    use std::collections::HashMap;

    #[fixture]
    fn concat_aggregator() -> Program {
        let program_content = include_bytes!(
            "../../resources/compiled_programs/test_programs/concat_aggregator_compiled.json"
        )
        .to_vec();

        Program::from_bytes(&program_content, Some("main"))
            .expect("Loading example program failed unexpectedly")
    }

    #[fixture]
    fn applicative_bootloader_input() -> String {
        let aggregator_program_exec = Cairo0Executable {
            program: concat_aggregator(),
            program_input: None,
        };
        let task = Task::Cairo0Program(aggregator_program_exec);
        let bootloader_input = crate::hints::types::BootloaderInput {
            simple_bootloader_input: crate::hints::types::SimpleBootloaderInput {
                tasks: vec![TaskSpec {
                    task: task.clone(),
                    program_hash_function: HashFunc::Poseidon,
                }],
                fact_topologies_path: None,
                single_page: true,
            },
            bootloader_config: BootloaderConfig {
                supported_simple_bootloader_hash_list: vec![
                    Felt252::from(1234),
                    Felt252::from(5678),
                ],
                supported_applicative_bootloader_program_hash: Felt252::from(2222),
                supported_cairo_verifier_program_hash_list: vec![
                    Felt252::from(3333),
                    Felt252::from(4444),
                    Felt252::from(5555),
                ],
            },
            packed_outputs: vec![],
        };
        let applicative_bootloader_input = crate::hints::types::ApplicativeBootloaderInput {
            aggregator_task: TaskSpec {
                task: task.clone(),
                program_hash_function: HashFunc::Poseidon,
            },
            bootloader_input,
        };

        serde_json::to_string(&applicative_bootloader_input).unwrap()
    }

    #[test]
    fn test_prepare_aggregator_simple_bootloader_output_segment() {
        let mut vm = VirtualMachine::new(false, false);
        vm.add_memory_segment();
        vm.add_memory_segment();
        let mut exec_scopes = ExecutionScopes::new();
        let mut ids_data = prepare_ids_data_for_test(&["aggregator_output_ptr"]);
        let ap_tracking = ApTracking::default();
        vm.set_fp(1);
        vm.set_ap(1);

        exec_scopes.insert_value(vars::PROGRAM_INPUT, applicative_bootloader_input());

        prepare_aggregator_simple_bootloader_output_segment(
            &mut vm,
            &mut exec_scopes,
            &mut ids_data,
            &ap_tracking,
        )
        .expect("Failed to run hint");

        // Assert that a new segment was added for the aggregator output.
        assert_eq!(vm.segments.num_segments(), 3);
        let aggregator_output_ptr: Relocatable =
            vm.get_relocatable(Relocatable::from((1, 0))).unwrap();
        assert_eq!(aggregator_output_ptr, Relocatable::from((2, 0)));

        // Assert that the applicative bootloader input and simple bootloader input are correctly
        // set in exec_scopes.
        let expected_applicative_bootloader_input = applicative_bootloader_input();

        let _applicative_bootloader_input: ApplicativeBootloaderInput = exec_scopes
            .get(vars::APPLICATIVE_BOOTLOADER_INPUT)
            .expect("Failed to get applicative_bootloader_input");
        let _simple_bootloader_input: SimpleBootloaderInput = exec_scopes
            .get(vars::SIMPLE_BOOTLOADER_INPUT)
            .expect("Failed to get simple_bootloader_input");
        assert_eq!(
            serialize_applicative_bootloader_input(&_applicative_bootloader_input),
            expected_applicative_bootloader_input
        );
    }
}
