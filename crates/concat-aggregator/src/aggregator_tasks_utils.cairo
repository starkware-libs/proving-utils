// Parses the task outputs from the bootloader output. Writes their outputs to the output_ptr.
// Returns the number of tasks.
func parse_tasks{output_ptr: felt*}() -> felt {
    alloc_locals;

    local n_tasks: felt;

    %{
        def parse_bootloader_tasks_outputs(output):
            """
            Parses the output of the bootloader, returning the raw outputs of the tasks.
            """
            output_iter = iter(output)
            # Skip the bootloader_config.
            [next(output_iter) for _ in range(3)]

            n_tasks = next(output_iter)
            tasks_outputs = []
            for _ in range(n_tasks):
                task_output_size = next(output_iter)
                tasks_outputs.append([next(output_iter) for _ in range(task_output_size - 1)])

            assert next(output_iter, None) is None, "Bootloader output wasn't fully consumed."

            return tasks_outputs

        tasks_outputs = parse_bootloader_tasks_outputs(program_input["bootloader_output"])
        assert len(tasks_outputs) > 0, "No tasks found in the bootloader output."
        ids.n_tasks = len(tasks_outputs)
    %}

    assert [output_ptr] = n_tasks;
    let output_ptr = output_ptr + 1;

    // Output the task outputs as they are.
    output_tasks(n_tasks=n_tasks);

    return n_tasks;
}

// Outputs the task outputs, each with the size of the output (to match the bootloader output
// format).
func output_tasks{output_ptr: felt*}(n_tasks: felt) {
    if (n_tasks == 0) {
        return ();
    }

    let output_size = output_ptr[0];
    let output_ptr = output_ptr + 1;

    %{
        task_index = len(tasks_outputs) - ids.n_tasks
        segments.load_data(ptr=ids.output_ptr, data=tasks_outputs[task_index])
        ids.output_size = len(tasks_outputs[task_index]) + 1
    %}

    let output_ptr = output_ptr + output_size - 1;

    return output_tasks(n_tasks=n_tasks - 1);
}
