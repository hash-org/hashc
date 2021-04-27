// use pest::Parser;

#[derive(Parser)]
#[grammar = "pest_parser/hash.pest"] // relative to src
pub struct HashParser;
