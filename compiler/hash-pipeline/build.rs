//! Build file for the `hash-pipeline` crate. This simply inlines needed
//! metadata about the standard library and the compiler itself.

use std::path::PathBuf;

/// The location of a build directory of this package, this used to resolve
/// where the standard library is located at.
static BUILD_DIR: &str = env!("CARGO_MANIFEST_DIR");

fn main() {
    inline_stdlib_info();
    inline_compuler_info();
}

/// Compute the path to the standard library and inline it into the build of
/// the compiler.
///
/// @@Future: We probably shouldn't do this because it will depend on each
/// installed system where the standard library is located. We should probably
/// define a "install" process that will copy the compiler and unpack the
/// standard library into a known location.
fn inline_stdlib_info() {
    let stdlib_path: PathBuf = [BUILD_DIR, "..", "..", "stdlib"].iter().collect();
    println!("cargo:rustc-env=STDLIB_PATH={}", stdlib_path.as_path().to_str().unwrap());
}

/// Compute the version of the compiler and inline it into the build of the
/// compiler. The version incluces the version of the `hash` crate, and the git
/// revision hash of the compiler itself.
fn inline_compuler_info() {
    let git_hash = String::from_utf8(
        std::process::Command::new("git")
            .args(["rev-parse", "HEAD"])
            .output()
            .expect("Failed to get git hash")
            .stdout,
    )
    .unwrap();

    let version = format!("{}-{}", env!("CARGO_PKG_VERSION"), git_hash);
    println!("cargo:rustc-env=COMPILER_VERSION={}", version);
}
