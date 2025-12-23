//! Optimized Cairo PIE reader with pre-allocated memory parsing.
//!
//! This module provides an optimized `CairoPieMemory` parser that pre-allocates
//! based on input size, fixing the O(log n) reallocation issue in cairo-vm's
//! `from_bytes` implementation.

use std::fs::File;
use std::io::{BufReader, Read};
use std::path::Path;

use cairo_vm::types::relocatable::MaybeRelocatable;
use cairo_vm::vm::runners::cairo_pie::{CairoPie, CairoPieMemory};
use cairo_vm::Felt252;
use zip::ZipArchive;

// Constants for memory binary format (must match cairo-vm).
const ADDR_BYTE_LEN: usize = 8;
const FIELD_BYTE_LEN: usize = 32;
const CELL_BYTE_LEN: usize = ADDR_BYTE_LEN + FIELD_BYTE_LEN; // 40 bytes per entry

/// Error type for PIE reading operations.
#[derive(thiserror::Error, Debug)]
pub enum PieReaderError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("ZIP error: {0}")]
    Zip(#[from] zip::result::ZipError),

    #[error("JSON parsing error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("Missing file in PIE archive: {0}")]
    MissingFile(String),

    #[error("Failed to parse PIE: {0}")]
    PieParseError(String),

    #[error("Invalid memory format: {0}")]
    InvalidMemoryFormat(String),
}

/// Reads a file from a ZIP archive (standard, no pre-allocation).
fn read_zip_entry<R: Read + std::io::Seek>(
    archive: &mut ZipArchive<R>,
    name: &str,
) -> Result<Vec<u8>, PieReaderError> {
    let mut file = archive
        .by_name(name)
        .map_err(|_| PieReaderError::MissingFile(name.to_string()))?;

    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;

    Ok(buffer)
}

/// Parses CairoPieMemory from bytes with pre-allocated capacity.
///
/// This is an optimized version of `cairo_vm::vm::runners::cairo_pie::CairoPieMemory::from_bytes`
/// that pre-allocates the result Vec based on input size, avoiding O(log n) reallocations.
///
/// ## The Problem
///
/// The cairo-vm implementation uses:
/// ```ignore
/// let mut res = vec![];  // Empty Vec
/// for cell_bytes in bytes.chunks(CELL_BYTE_LEN) {
///     res.push((addr, value));  // Repeated push causes reallocations
/// }
/// ```
///
/// For a 3GB memory.bin file (~75M entries), this causes:
/// - ~27 reallocations (log2(75M))
/// - Peak memory of ~2x the final size due to realloc copying
///
/// ## The Fix
///
/// By calculating `num_entries = bytes.len() / CELL_BYTE_LEN` upfront and using
/// `Vec::with_capacity(num_entries)`, we eliminate all reallocations.
fn parse_cairo_pie_memory_preallocated(bytes: &[u8]) -> Result<CairoPieMemory, PieReaderError> {
    if bytes.len() % CELL_BYTE_LEN != 0 {
        return Err(PieReaderError::InvalidMemoryFormat(format!(
            "Memory size {} is not a multiple of cell size {}",
            bytes.len(),
            CELL_BYTE_LEN
        )));
    }

    // KEY OPTIMIZATION: Calculate number of entries upfront and pre-allocate.
    let num_entries = bytes.len() / CELL_BYTE_LEN;
    let mut result = Vec::with_capacity(num_entries);

    // Helper to parse relocatable address from 8 bytes.
    let relocatable_from_bytes = |bytes: [u8; 8]| -> (usize, usize) {
        const N_SEGMENT_BITS: usize = 16;
        const N_OFFSET_BITS: usize = 47;
        const SEGMENT_MASK: u64 = ((1 << N_SEGMENT_BITS) - 1) << N_OFFSET_BITS;
        const OFFSET_MASK: u64 = (1 << N_OFFSET_BITS) - 1;

        let addr = u64::from_le_bytes(bytes);
        let segment = (addr & SEGMENT_MASK) >> N_OFFSET_BITS;
        let offset = addr & OFFSET_MASK;
        (segment as usize, offset as usize)
    };

    for cell_bytes in bytes.chunks(CELL_BYTE_LEN) {
        let addr_bytes: [u8; ADDR_BYTE_LEN] = cell_bytes[0..ADDR_BYTE_LEN]
            .try_into()
            .map_err(|_| PieReaderError::InvalidMemoryFormat("Invalid address bytes".into()))?;
        let addr = relocatable_from_bytes(addr_bytes);

        let field_bytes = &cell_bytes[ADDR_BYTE_LEN..CELL_BYTE_LEN];

        // Check the last bit to determine if it is a Relocatable or Felt value.
        let value = if (field_bytes[field_bytes.len() - 1] & 0x80) != 0 {
            // Relocatable value.
            let field_addr_bytes: [u8; ADDR_BYTE_LEN] = field_bytes[0..ADDR_BYTE_LEN]
                .try_into()
                .map_err(|_| {
                    PieReaderError::InvalidMemoryFormat("Invalid relocatable field bytes".into())
                })?;
            let (segment, offset) = relocatable_from_bytes(field_addr_bytes);
            MaybeRelocatable::from((segment as isize, offset))
        } else {
            // Felt value.
            MaybeRelocatable::from(Felt252::from_bytes_le_slice(field_bytes))
        };

        result.push((addr, value));
    }

    Ok(CairoPieMemory(result))
}

/// Reads a Cairo PIE from a ZIP file with optimized memory parsing.
///
/// This function uses the standard ZIP reading but replaces cairo-vm's
/// `CairoPieMemory::from_bytes` with an optimized version that pre-allocates.
///
/// # Arguments
/// * `path` - Path to the PIE ZIP file.
///
/// # Returns
/// * `Ok(CairoPie)` - The parsed Cairo PIE.
/// * `Err(PieReaderError)` - If reading or parsing fails.
pub fn read_cairo_pie_preallocated(path: &Path) -> Result<CairoPie, PieReaderError> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let mut archive = ZipArchive::new(reader)?;

    // Read metadata.json.
    let metadata_bytes = read_zip_entry(&mut archive, "metadata.json")?;
    let metadata = serde_json::from_slice(&metadata_bytes)?;

    // Read memory.bin.
    let memory_bytes = read_zip_entry(&mut archive, "memory.bin")?;

    // Parse memory using our optimized parser with pre-allocation.
    // This is the KEY OPTIMIZATION - fixes cairo-vm's O(log n) reallocation issue.
    let memory = parse_cairo_pie_memory_preallocated(&memory_bytes)?;

    // Read additional_data.json.
    let additional_data_bytes = read_zip_entry(&mut archive, "additional_data.json")?;
    let additional_data = serde_json::from_slice(&additional_data_bytes)?;

    // Read execution_resources.json.
    let execution_resources_bytes = read_zip_entry(&mut archive, "execution_resources.json")?;
    let execution_resources = serde_json::from_slice(&execution_resources_bytes)?;

    // Read version.json if present (optional in older PIE formats).
    let version = match read_zip_entry(&mut archive, "version.json") {
        Ok(bytes) => serde_json::from_slice(&bytes)?,
        Err(PieReaderError::MissingFile(_)) => {
            cairo_vm::vm::runners::cairo_pie::CairoPieVersion { cairo_pie: () }
        }
        Err(e) => return Err(e),
    };

    Ok(CairoPie {
        metadata,
        memory,
        additional_data,
        execution_resources,
        version,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn get_test_pie_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("resources/compiled_programs/test_programs/fibonacci_pie.zip")
    }

    #[test]
    fn test_read_pie_preallocated() {
        let path = get_test_pie_path();
        if !path.exists() {
            // Skip test if no test PIE available.
            return;
        }

        let pie = read_cairo_pie_preallocated(&path).expect("Failed to read PIE");

        // Basic sanity checks.
        assert!(!pie.memory.0.is_empty(), "PIE memory should not be empty");
    }
}
