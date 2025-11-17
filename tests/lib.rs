#![feature(test)]
extern crate test;

pub mod reporting;
/// Modules to do with UI tests and running them
mod runner;

use std::{fs, path::Path};

use lazy_static::lazy_static;
use regex::Regex;

lazy_static! {
    /// Whether or not the UI tests should re-generate the output.
    pub static ref REGENERATE_OUTPUT: bool =
        str::parse::<bool>(std::option_env!("REGENERATE_OUTPUT").unwrap_or("false"))
            .unwrap_or(false);
}

/// This is the ANSI Regular expression matcher. This will match all the
/// specified ANSI escape codes that are used by the [`hash_reporting`] crate.
pub(crate) const ANSI_RE: &str =
    r"[\x1b\x9b]\[[()#;?]*(?:[0-9]{1,4}(?:;[0-9]{0,4})*)?[0-9A-ORZcf-nqry=><]";

lazy_static! {
    pub static ref ANSI_REGEX: Regex = Regex::new(ANSI_RE).unwrap();
}

/// Stub function for cargo to treat this as a library.
///
/// @@Future: this will become a command-line interface in order
/// to update test outputs rather than using the in-built `REGENERATE_OUTPUT`
/// flag.
fn main() {
    // We want to clean-up the `target` directory from any potential previous
    // test runs. This is because we want to ensure that the `target` directory
    // is as clean as possible before we run the tests.
    let target_dir = Path::new("./target").to_path_buf();

    // We want to clear the directory before we start running the test, so that
    // we don't have any old files lying around.
    if target_dir.exists() {
        fs::remove_dir_all(&target_dir).unwrap();
    }
}

// @@Todo: move this into `main.rs` within this crate
// so that we can edit each individual test case rather
// than using it as a constant.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn ensure_regenerate_output_is_disabled() {
        assert!(
            !*REGENERATE_OUTPUT,
            "
        Verify that the `REGENERATE_OUTPUT` module flag is not accidentally left
        on making all of the test cases that observe compiler output
        automatically overwrite old results with current ones.
        "
        );
    }
}
