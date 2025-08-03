%builtins output range_check poseidon

from aggregator_tasks_utils import parse_tasks
from starkware.cairo.common.cairo_builtins import PoseidonBuiltin

// Simple aggregation program that concatenates task outputs. Used for tests. It is not sound.
//
// Hint arguments:
// program_input - List of task outputs, in the format of the bootloader output.
func main{output_ptr: felt*, range_check_ptr, poseidon_ptr: PoseidonBuiltin*}() {
    alloc_locals;

    let n_tasks = parse_tasks();
    local output_start: felt* = output_ptr;

    // Output the concatenated task outputs.
    output_concatenated_output(n_tasks=n_tasks);

    %{
        from starkware.python.math_utils import div_ceil

        output_length = ids.output_ptr - ids.output_start
        page_size = 10
        next_page_start = min(ids.output_start + page_size, ids.output_ptr)
        next_page_id = 1
        while next_page_start < ids.output_ptr:
            output_builtin.add_page(
                page_id=next_page_id,
                page_start=next_page_start,
                page_size=min(ids.output_ptr - next_page_start, page_size),
            )
            next_page_start += page_size
            next_page_id += 1
        if next_page_id == 1:
            # Single page. Use trivial fact topology.
            output_builtin.add_attribute('gps_fact_topology', [
                1,
                0,
            ])
        else:
            output_builtin.add_attribute('gps_fact_topology', [
                next_page_id,
                next_page_id - 1,
                0,
                2,
            ])
    %}
    return ();
}

// Outputs the task outputs, without the output sizes.
func output_concatenated_output{output_ptr: felt*}(n_tasks: felt) {
    alloc_locals;
    if (n_tasks == 0) {
        return ();
    }

    local output_size: felt;

    %{
        task_index = len(tasks_outputs) - ids.n_tasks
        segments.load_data(ptr=ids.output_ptr, data=tasks_outputs[task_index])
        ids.output_size = len(tasks_outputs[task_index])
    %}

    let output_ptr = output_ptr + output_size;

    return output_concatenated_output(n_tasks=n_tasks - 1);
}
