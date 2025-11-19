use std::process::Command;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use walkdir::WalkDir; // A useful crate for walking directories
use std::env; // Import the env module
use anyhow::{Result, Context};

use cairo_compile_utils::compile_cairo_code;
use std::fs;

fn main() -> anyhow::Result<()> {

    // Get the current working directory of the Rust program
    let current_dir = env::current_dir()
    .context("Failed to get current working directory")?.join("crates").join("concat-aggregator").join("src");

    compile_cairo_code(&current_dir)?;
    
    Ok(())
}
