//! Hash compiler module for converting from tokens to an AST tree
//
// All rights reserved 2021 (c) The Hash Language authors
use crate::ast::*;
use crate::error::ParseError;
use crate::grammar::{HashParser, Rule};

// use pest::iterators::{Pair, Pairs};
use pest::Parser;

pub fn module(source: &str) -> Result<Module, ParseError> {
    let result = HashParser::parse(Rule::module, source);

    match result {
        Ok(_pairs) => {
            // here is where we do all the ast-ification
            let vec = Vec::new();
            Ok(Module { contents: vec })
        }
        Err(err) => Err(ParseError::from(err)),
    }
}
