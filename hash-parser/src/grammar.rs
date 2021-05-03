//! Hash language grammar implementation
//
// All rights reserved 2021 (c) The Hash Language authors

/// Language parser, created via [pest]
#[allow(clippy::upper_case_acronyms)]
mod derived {
    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "hash.pest"] // relative to src
    pub struct HashParser;
}

pub use derived::{HashParser, Rule};
