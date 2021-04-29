// use pest::Parser;
// const _GRAMMAR: &'static = include_str!("hash.pest"); // relative to this file

#[derive(Parser)]
#[grammar = "pest_parser/hash.pest"] // relative to src
pub struct HashParser;
