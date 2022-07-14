//! Build file for the `hash-pipeline` crate. This simply inlines the
//! executable version into the executable.

use std::path::PathBuf;

/// The location of a build directory of this package, this used to resolve
/// where the standard library is located at.
static BUILD_DIR: &str = env!("CARGO_MANIFEST_DIR");

/// This is run at compile time to compute some meta data about the produced
/// executable
fn main() {
    let stdlib_path: PathBuf = [BUILD_DIR, "..", "..", "stdlib"].iter().collect();
    println!("cargo:rustc-env=STDLIB_PATH={}", stdlib_path.as_path().to_str().unwrap());
}
