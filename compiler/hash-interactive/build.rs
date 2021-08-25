const VERSION: &str = env!("CARGO_PKG_VERSION");

/// This is run at compile time to compute some meta data about the produced executable
fn main() {
    if cfg!(feature = "use-pest") {
        println!(
            "cargo:rustc-env=EXECUTABLE_VERSION={}: \"(parser=pest)\"",
            VERSION
        );
    } else {
        println!(
            "cargo:rustc-env=EXECUTABLE_VERSION={}: \"(parser=self)\"",
            VERSION
        );
    }
}
