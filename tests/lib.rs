#![feature(test)]
extern crate test;

pub mod parser;
pub mod test_runner;

use lazy_static::lazy_static;
use regex::Regex;

/// Whether or not the UI tests should re-generate the output.
pub const REGENERATE_OUTPUT: bool = false;

/// This is the ANSI Regular expression matcher. This will match all the
/// specified ANSI escape codes that are used by the [`hash_reporting`] crate.
pub(crate) const ANSI_RE: &str =
    r"[\x1b\x9b]\[[()#;?]*(?:[0-9]{1,4}(?:;[0-9]{0,4})*)?[0-9A-ORZcf-nqry=><]";

lazy_static! {
    pub static ref ANSI_REGEX: Regex = Regex::new(ANSI_RE).unwrap();
}

/// Stub function for the
fn main() {}

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
            !REGENERATE_OUTPUT,
            "
        Verify that the `REGENERATE_OUTPUT` module flag is not accidentally left
        on making all of the test cases that observe compiler output
        automatically overwrite old results with current ones.
        "
        );
    }
}
