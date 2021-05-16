//! Hash compiler module for converting from tokens to an AST tree
use std::time::Instant;

//
// All rights reserved 2021 (c) The Hash Language authors
use crate::ast::*;
use crate::error::ParseError;
use crate::grammar::{HashParser, Rule};

// use pest::iterators::{Pair, Pairs};
use pest::Parser;

pub fn module(source: &str) -> Result<Module, ParseError> {
    let before = Instant::now();

    let result = HashParser::parse(Rule::module, source);
    println!("tokenise: {:.2?}", before.elapsed());

    match result {
        Ok(pairs) => {
            let after_token = Instant::now();

            let contents = pairs
                .take_while(|p| p.as_rule() != Rule::EOI)
                .map(|p| p.into_ast())
                .collect();

            println!("ast: {:.2?}", after_token.elapsed());

            Ok(Module { contents })
        }
        Err(err) => Err(ParseError::from(err)),
    }
}

/// Function to parse an individual statement. This function is primarily used for the interactive
/// mode where only statements are accepted.
pub fn statement(source: &str) -> Result<AstNode<Statement>, ParseError> {
    let mut result = HashParser::parse(Rule::statement, source)?;

    // @Temp: this is only temporary to display the parsed result for testing
    println!("{:#?}", result);

    let body: AstNode<Statement> = result.next().unwrap().into_ast();
    Ok(body)
}
