//! Self hosted hash parser, this function contains the implementations for `hash-ast`
//! which provides a general interface to write a parser.
//!
//! All rights reserved 2021 (c) The Hash Language authors
use std::path::Path;

use hash_ast::ast::{self};
use hash_ast::{error::ParseResult, parse::ParserBackend, resolve::ModuleResolver};
use hash_utils::timed;

use crate::{gen::AstGen, lexer::tokenise};

pub struct HashParser;

impl ParserBackend for HashParser {
    fn parse_module(
        &self,
        resolver: &mut impl ModuleResolver,
        _path: &Path,
        contents: &str,
    ) -> ParseResult<ast::Module> {
        let tokens = timed(
            || tokenise(contents).collect::<Vec<_>>(),
            log::Level::Debug,
            |elapsed| println!("tokenise:    {:?}", elapsed),
        );

        let mut gen = AstGen::new(tokens, resolver);

        timed(
            || gen.parse_module(),
            log::Level::Debug,
            |elapsed| println!("translation: {:?}", elapsed),
        )
    }

    fn parse_interactive(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &str,
    ) -> ParseResult<ast::AstNode<ast::BodyBlock>> {
        let tokens = tokenise(contents).collect::<Vec<_>>();
        let mut gen = AstGen::new(tokens.clone(), resolver);

        for token in tokens.into_iter() {
            println!("{}", token);
        }

        gen.parse_expression_from_interactive()
    }
}
