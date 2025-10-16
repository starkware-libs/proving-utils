use crate::hints::types::Task;
use crate::hints::vars;
use cairo_vm::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::HintProcessorData;
use cairo_vm::hint_processor::hint_processor_definition::HintExtension;
use cairo_vm::hint_processor::hint_processor_definition::HintReference;
use cairo_vm::serde::deserialize_program::ApTracking;
use cairo_vm::types::exec_scope::ExecutionScopes;
use cairo_vm::types::relocatable::MaybeRelocatable;
use cairo_vm::types::relocatable::Relocatable;
use cairo_vm::vm::vm_core::VirtualMachine;

/// Test helper: Create a HashMap of HintReferences for testing.
/// Output:
/// {
///     0: HintReference::new_simple(-num),
///     1: HintReference::new_simple(-num + 1),
///     ...
///     num - 1: HintReference::new_simple(-1),
///     num: HintReference::new_simple(0),
/// }
pub fn prepare_refrences_for_test(num: i32) -> std::collections::HashMap<usize, HintReference> {
    let mut references = std::collections::HashMap::<usize, HintReference>::new();
    for i in 0..num {
        references.insert(i as usize, HintReference::new_simple(i - num));
    }
    references
}

/// Test helper: Create a HashMap of HintReferences for testing, keyed by name.
/// Output:
/// {
///     "name1": HintReference::new_simple(-num),
///     "name2": HintReference::new_simple(-num + 1),
///     ...
///     "nameN": HintReference::new_simple(-1),
/// }
/// where num is the length of names.
pub fn fill_ids_data_for_test(names: &[&str]) -> std::collections::HashMap<String, HintReference> {
    let references = prepare_refrences_for_test(names.len() as i32);
    let mut ids_data = std::collections::HashMap::<String, HintReference>::new();
    for (i, name) in names.iter().enumerate() {
        ids_data.insert(name.to_string(), references.get(&i).unwrap().clone());
    }
    ids_data
}

/// Test helper: Create a HashMap of HintReferences for testing, keyed by name and offset.
/// example output: (notice that some offsets are skipped)
/// {
/// "name1": HintReference::new_simple(-1),
/// "name2": HintReference::new_simple(-3),
/// "name3": HintReference::new_simple(-10)
/// ...
/// },
pub fn prepare_non_continuous_ids_data_for_test(
    pairs: &[(&str, i32)],
) -> std::collections::HashMap<String, HintReference> {
    let mut ids_data = std::collections::HashMap::<String, HintReference>::new();
    for (name, offset) in pairs {
        ids_data.insert(name.to_string(), HintReference::new_simple(*offset));
    }
    ids_data
}

/// Utility function to extract all hint code strings from a HintExtension at a given PC.
pub fn get_hint_codes_at_pc(hint_extension: &HintExtension, pc: Relocatable) -> Vec<&str> {
    hint_extension
        .get(&pc)
        .expect("Hint extension should contain the hint at the given PC")
        .iter()
        .map(|hint_any| {
            hint_any
                .downcast_ref::<HintProcessorData>()
                .expect("Hint at PC is not a HintProcessorData")
                .code
                .as_str()
        })
        .collect()
}

/// Utility: Prepares a VM, ids_data, exec_scopes, ap_tracking, and pointers for bootloader tests.
/// After this function is executed the VM has 3 segments, and the program header is at (2, 0).
/// The `task` is inserted into the execution scopes. `load_program_hint` should succeed after this
/// function.
pub fn prepare_vm_for_load_program_loading_test(
    task: Task,
) -> (
    VirtualMachine,
    std::collections::HashMap<String, HintReference>,
    ExecutionScopes,
    ApTracking,
    usize,       // expected_program_data_segment_index
    Relocatable, // program_header_ptr
    Task,
) {
    let mut vm = VirtualMachine::new(false, false);
    vm.set_fp(3);
    vm.segments.add();
    vm.segments.add();
    let _ = vm.segments.load_data(
        Relocatable::from((1, 0)),
        &[
            MaybeRelocatable::from((2, 0)),
            MaybeRelocatable::from((2, 0)),
            MaybeRelocatable::from((2, 0)),
        ],
    );

    let ids_data =
        fill_ids_data_for_test(&["program_segment_ptr", "program_header", "program_data_ptr"]);
    let expected_program_data_segment_index = vm.segments.num_segments();
    let program_header_ptr = Relocatable::from((2, 0));
    let mut exec_scopes = ExecutionScopes::new();
    exec_scopes.insert_value(vars::TASK, task.clone());
    exec_scopes.insert_value(vars::PROGRAM_DATA_BASE, program_header_ptr);
    let ap_tracking = ApTracking::new();
    (
        vm,
        ids_data,
        exec_scopes,
        ap_tracking,
        expected_program_data_segment_index,
        program_header_ptr,
        task,
    )
}
