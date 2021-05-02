//! Hash compiler module for converting from tokens to an AST tree
//
// All rights reserved 2021 (c) The Hash Language authors
use crate::{ast::*, location::Location};
use crate::error::ParseError;
use crate::grammar::{HashParser, Rule};

// use pest::iterators::{Pair, Pairs};
use pest::Parser;

pub fn module(source: &str) -> Result<Module, ParseError> {
    let result = HashParser::parse(Rule::module, source);

    match result {
        Ok(_pairs) => {
            // @@Incomplete: here is where we do all the ast-ification
            let vec = Vec::new();
            Ok(Module { contents: vec })
        }
        Err(err) => Err(ParseError::from(err)),
    }
}


/// Function to parse an individual statement. This function is primarily used for the interactive
/// mode where only statements are accepted.
pub fn statement(source: &str) -> Result<AstNode<Statement>, ParseError> {
    let result = HashParser::parse(Rule::statement, source);

    match result {
        Ok(pairs) => {
            
            let rules: Vec<Location>  = pairs
                .take_while(|pair| pair.as_rule() != Rule::EOI)
                .map(Location::from)
                .collect();

            let temp = rules.get(0).unwrap_or_else(|| panic!("Couldn't convert nodes into positions")).clone();

            // @@Incomplete: actully convert the item into an ast-node
            Ok(AstNode::<Statement> {
                body: Box::new(Statement::Continue),
                pos: temp,
                module: 0,
            })
        }
        Err(err) => Err(ParseError::from(err)),
    }
}
