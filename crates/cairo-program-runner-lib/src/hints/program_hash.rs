use cairo_vm::types::builtin_name::BuiltinName;
use cairo_vm::types::relocatable::MaybeRelocatable;
use cairo_vm::vm::runners::cairo_pie::StrippedProgram;
use cairo_vm::Felt252;
use starknet_crypto::{pedersen_hash, poseidon_hash_many, Felt};
use starknet_types_core::hash::Blake2Felt252;
use std::iter::once;

use super::types::HashFunc;

type HashFunction = fn(&Felt, &Felt) -> Felt;

#[derive(thiserror_no_std::Error, Debug)]
pub enum HashChainError {
    #[error("Data array must contain at least one element.")]
    EmptyData,
}

#[derive(thiserror_no_std::Error, Debug)]
pub enum ProgramHashError {
    #[error(transparent)]
    HashChain(#[from] HashChainError),

    #[error(
        "Invalid program builtin: builtin name too long to be converted to field element: {0}"
    )]
    InvalidProgramBuiltin(&'static str),

    #[error("Invalid program data: data contains relocatable(s)")]
    InvalidProgramData,

    /// Conversion from Felt252 to Felt failed. This is unlikely to happen
    /// unless the implementation of Felt252 changes and this code is not updated properly.
    #[error("Conversion from Felt252 to Felt failed")]
    Felt252ToFeltConversionFailed,
}
/*
 Computes a hash chain over the data, in the following order:
     h(data[0], h(data[1], h(..., h(data[n-2], data[n-1])))).

 Reimplements this Python function:
 def compute_hash_chain(data, hash_func=pedersen_hash):
     assert len(data) >= 1, f"len(data) for hash chain computation must be >= 1; got: {len(data)}."
     return functools.reduce(lambda x, y: hash_func(y, x), data[::-1])
*/
fn compute_hash_chain<'a, I>(data: I, hash_func: HashFunction) -> Result<Felt, HashChainError>
where
    I: Iterator<Item = &'a Felt> + DoubleEndedIterator,
{
    match data.copied().rev().reduce(|x, y| hash_func(&y, &x)) {
        Some(result) => Ok(result),
        None => Err(HashChainError::EmptyData),
    }
}

/// Creates an instance of `Felt` from a builtin name.
///
/// Converts the builtin name to bytes then attempts to create a field element from
/// these bytes. This function will fail if the builtin name is over 31 characters.
fn builtin_to_felt(builtin: &BuiltinName) -> Result<Felt, ProgramHashError> {
    // The Python implementation uses the builtin name without suffix
    let builtin_name = builtin.to_str();

    // TODO(idanh): not sure if this check is correct, documentation of Felt::from_bytes_be_slice
    // works in chunks of 32 bytes and not 31...
    if builtin_name.len() > 31 {
        return Err(ProgramHashError::InvalidProgramBuiltin(builtin.to_str()));
    }
    Ok(Felt::from_bytes_be_slice(builtin_name.as_bytes()))
}

/// The `value: Felt` is `pub(crate)` and there is no accessor.
/// This function converts a `Felt252` to a `Felt` using a safe, albeit inefficient,
/// method.
fn felt252_to_felt(felt: &Felt252) -> Result<Felt, ProgramHashError> {
    let bytes = felt.to_bytes_be();
    // Check if bytes length is over 31
    if bytes.len() > 32 {
        return Err(ProgramHashError::Felt252ToFeltConversionFailed);
    }
    Ok(Felt::from_bytes_be(&bytes))
}

/// Converts a `MaybeRelocatable` into a `Felt` value.
///
/// Returns `InvalidProgramData` if `maybe_relocatable` is not an integer
fn maybe_relocatable_to_felt(
    maybe_relocatable: &MaybeRelocatable,
) -> Result<Felt, ProgramHashError> {
    let felt = maybe_relocatable
        .get_int_ref()
        .ok_or(ProgramHashError::InvalidProgramData)?;
    felt252_to_felt(felt)
}

/// Computes the program hash chain using the selected hash function.
/// This implementation takes into account the program header in addition to the program data,
/// which aligns with how the bootloader computes the program hash of its subtasks.
pub fn compute_program_hash_chain(
    program: &StrippedProgram,
    bootloader_version: usize,
    program_hash_function: HashFunc,
) -> Result<Felt, ProgramHashError> {
    let program_main = program.main;
    let program_main = Felt::from(program_main);

    // Convert builtin names to field elements
    let builtin_list: Result<Vec<Felt>, _> = program.builtins.iter().map(builtin_to_felt).collect();
    let builtin_list = builtin_list?;

    let program_header = vec![
        Felt::from(bootloader_version),
        program_main,
        Felt::from(program.builtins.len()),
    ];

    let program_data: Result<Vec<_>, _> =
        program.data.iter().map(maybe_relocatable_to_felt).collect();
    let program_data = program_data?;

    let data_without_len: Vec<Felt> = [&program_header, &builtin_list, &program_data]
        .iter()
        .flat_map(|&v| v.iter().copied())
        .collect();

    let hash = match program_hash_function {
        HashFunc::Pedersen => {
            let data_chain_len_felt = Felt::from(data_without_len.len());
            compute_hash_chain(
                once(&data_chain_len_felt).chain(data_without_len.iter()),
                pedersen_hash,
            )?
        }
        HashFunc::Poseidon => poseidon_hash_many(&data_without_len),
        HashFunc::Blake => {
            Blake2Felt252::encode_felt252_data_and_calc_blake_hash(&data_without_len)
        }
    };
    Ok(hash)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use cairo_vm::math_utils::signed_felt;
    use cairo_vm::types::layout_name::LayoutName;
    use cairo_vm::types::program::Program;
    use cairo_vm::Felt252;
    use rstest::rstest;
    use starknet_crypto::pedersen_hash;

    use crate::types::RunMode;
    use crate::{cairo_run_program, ProgramInput};

    use super::*;

    #[test]
    fn test_compute_hash_chain() {
        let data: Vec<Felt> = vec![Felt::from(1u64), Felt::from(2u64), Felt::from(3u64)];
        let expected_hash = pedersen_hash(
            &Felt::from(1u64),
            &pedersen_hash(&Felt::from(2u64), &Felt::from(3u64)),
        );
        let computed_hash = compute_hash_chain(data.iter(), pedersen_hash)
            .expect("Hash computation failed unexpectedly");

        assert_eq!(computed_hash, expected_hash);
    }

    #[rstest]
    // Expected hashes generated with `cairo-hash-program`
    #[case::fibonacci(
        "resources/compiled_programs/test_programs/fibonacci_compiled.json",
        "0x4f028ea2f2568d9b71509641f65cd3879482a371ab2a18d20ca7528d960dd45"
    )]
    #[case::builtin_usage(
        "resources/compiled_programs/test_programs/builtin_usage_compiled.json",
        "0x4b91dbb7dc2f33ff104023b86e8dac0b94382695bcdcca4a352e6a51ef522c7"
    )]
    // TODO(idanh): try to compute the hashchain seperately as well to see that this function works
    // correctly. if neccessary, change the expected hashes.
    fn test_compute_program_hash_chain(
        #[case] program_path: PathBuf,
        #[case] expected_program_hash: String,
    ) {
        let program =
            Program::from_file(program_path.as_path(), Some("main"))
                .expect("Could not load program. Did you compile the sample programs? Run `make test` in the root directory.");
        let stripped_program = program.get_stripped_program().unwrap();
        let bootloader_version = 0;

        let program_hash =
            compute_program_hash_chain(&stripped_program, bootloader_version, HashFunc::Pedersen)
                .expect("Failed to compute program hash.");

        let program_hash_hex = format!("{program_hash:#x}");

        assert_eq!(program_hash_hex, expected_program_hash);
    }

    /// Runs the simple bootloader with a fibonncci program task with each of the 3 hash func
    /// variants, and asserts that the program hash at output buffer index 2 (third element) matches
    /// the Rust `compute_program_hash_chain` result.
    #[rstest]
    #[case::pedersen(HashFunc::Pedersen)]
    #[case::poseidon(HashFunc::Poseidon)]
    #[case::blake(HashFunc::Blake)]
    fn test_bootloader_program_hash_matches_rust_impl(#[case] hash_func: HashFunc) {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let simple_bootloader_path = manifest_dir
            .join("resources/compiled_programs/bootloaders/simple_bootloader_compiled.json");
        let fibonacci_path = manifest_dir.join("examples/fibonacci.json");

        let simple_bootloader_program =
            Program::from_file(simple_bootloader_path.as_path(), Some("main"))
                .expect("Could not load simple bootloader program.");
        let fibonacci_program = Program::from_file(fibonacci_path.as_path(), Some("main"))
            .expect("Could not load fibonacci program.");
        let stripped_program = fibonacci_program
            .get_stripped_program()
            .expect("Could not get stripped program.");

        let program_hash_function_str = match hash_func {
            HashFunc::Pedersen => "pedersen",
            HashFunc::Poseidon => "poseidon",
            HashFunc::Blake => "blake",
        };
        let program_input_contents = format!(
            r#"{{
                "tasks": [
                    {{
                        "path": "{}",
                        "program_hash_function": "{}",
                        "type": "RunProgramTask"
                    }}
                ],
                "single_page": true
            }}"#,
            fibonacci_path.display(),
            program_hash_function_str,
        );

        let cairo_run_config = RunMode::Proof {
            layout: LayoutName::starknet_with_keccak,
            dynamic_layout_params: None,
            disable_trace_padding: false,
            relocate_mem: true,
        }
        .create_config();

        let mut runner = cairo_run_program(
            &simple_bootloader_program,
            Some(ProgramInput::Json(program_input_contents)),
            cairo_run_config,
            None,
        )
        .expect("Bootloader run failed.");

        let expected_hash = compute_program_hash_chain(&stripped_program, 0, hash_func)
            .expect("Failed to compute program hash in Rust.");
        let mut output_buffer = String::new();
        runner
            .vm
            .write_output(&mut output_buffer)
            .expect("Failed to write VM output.");

        // write_output renders integers as signed felt decimals.
        let expected_hash_output_format =
            signed_felt(Felt252::from_bytes_be(&expected_hash.to_bytes_be())).to_string();
        let output_lines: Vec<&str> = output_buffer.lines().collect();
        assert!(
            output_lines.len() > 2,
            "Expected at least 3 output lines (n_tasks, n_task_words, program_hash). Got:\n{output_buffer}"
        );
        assert_eq!(
            output_lines[2],
            expected_hash_output_format,
            "Bootloader output program hash should match compute_program_hash_chain for {hash_func:?}",
        );
    }
}
