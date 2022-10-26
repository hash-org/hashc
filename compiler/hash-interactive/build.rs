//! Build file for the `hash-interactive` crate. This simply inlines the
//! executable version into the executable.
const VERSION: &str = env!("CARGO_PKG_VERSION");

/// This is run at compile time to compute some meta data about the produced
/// executable
fn main() {
    println!("cargo:rustc-env=EXECUTABLE_VERSION={VERSION}");
}
