//! Writing the three root-layer output files.

use std::path::Path;

use crate::RecursiveTreeError;
use crate::fold::LayerEntry;

/// Writes the root-layer outputs to the caller-configured paths:
/// - `proof_path`: the serialized root circuit `Proof<QM31>` (the root node's in-memory proof bytes
///   — a folded multiverifier proof, or the leaf proof for a single-leaf tree).
/// - `program_output`: the root node's output values, as a JSON array of `[u32; 4]` QM31 limbs.
/// - `packed_output_path`: the nested `PackedNode` JSON tree mirroring the whole fold.
pub fn write_root_outputs(
    root: &LayerEntry,
    proof_path: &Path,
    program_output: &Path,
    packed_output_path: &Path,
) -> Result<(), RecursiveTreeError> {
    std::fs::write(proof_path, &root.proof_bytes)
        .map_err(|e| RecursiveTreeError::PathIO(e, proof_path.to_path_buf()))?;

    std::fs::write(
        program_output,
        sonic_rs::to_string(&root.packed_output.output_values)?,
    )
    .map_err(|e| RecursiveTreeError::PathIO(e, program_output.to_path_buf()))?;

    std::fs::write(
        packed_output_path,
        serde_json::to_string(&root.packed_output)?,
    )
    .map_err(|e| RecursiveTreeError::PathIO(e, packed_output_path.to_path_buf()))?;
    Ok(())
}
