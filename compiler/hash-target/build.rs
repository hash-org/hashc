//! This build script is used to compute the name of the
//! target in the form of a [target-triple][https://wiki.osdev.org/Target_Triplet]
//! string. This is used to properly configure the compilation target
//! for the code generation backends.

use std::env;

macro_rules! export_variable {
    ($name:ident, $value:expr) => {
        println!("cargo:rustc-env={}={}", stringify!($name), $value);
    };
}

/// Export the target triple as an environment variable.
fn main() {
    let target = env::var("TARGET").unwrap();
    export_variable!(TARGET_TRIPLE, target);

    // By default Cargo only runs the build script when a file changes.
    // This makes it re-run on target change
    println!("cargo:rerun-if-changed-env=TARGET")
}
