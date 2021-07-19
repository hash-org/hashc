use std::path::Path;

use hash_ast::{
    ast::{self, AstNode, BodyBlock},
    error::ParseResult,
    location::Location,
    parse::{ModuleResolver, ParserBackend},
};
use hash_utils::timed;

use crate::{lexer::tokenise, token::Token};

pub struct HashParser;

impl ParserBackend for HashParser {
    fn parse_module(
        &self,
        _resolver: &mut impl ModuleResolver,
        _path: &Path,
        contents: &str,
    ) -> ParseResult<ast::Module> {
        let _tokens = timed(
            || {
                let _tokens = tokenise(contents).collect::<Vec<Token>>();
                // println!("tokens: {:#?}", tokens); //tokeniser.collect::<Vec<Token>>());
            },
            log::Level::Debug,
            |elapsed| println!("tokenise: {:?}", elapsed),
        );

        todo!()
    }

    fn parse_interactive(
        &self,
        _resolver: &mut impl ModuleResolver,
        contents: &str,
    ) -> ParseResult<ast::AstNode<ast::BodyBlock>> {
        let tokens = tokenise(contents);

        // println!("tokens: {:#?}", tokens); //tokeniser.collect::<Vec<Token>>());
        for token in tokens {
            println!("{}", token);
        }

        Ok(AstNode::new(
            BodyBlock {
                statements: vec![],
                expr: None,
            },
            Location::span(0, 0),
        ))
    }
}
