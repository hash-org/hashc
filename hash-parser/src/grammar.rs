//! Hash language grammar implementation
//
// All rights reserved 2021 (c) The Hash Language authors

/// Language parser, created via [pest]
#[derive(Parser)]
#[grammar = "hash.pest"] // relative to src
pub struct HashParser;
