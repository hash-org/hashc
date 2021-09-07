//! Self hosted hash parser, this function contains the implementations for `hash-ast`
//! which provides a general interface to write a parser.
//!
//! All rights reserved 2021 (c) The Hash Language authors
use std::path::Path;

use hash_alloc::Castle;
use hash_ast::ast;
use hash_ast::{error::ParseResult, parse::ParserBackend, resolve::ModuleResolver};
use hash_utils::timed;

use crate::gen::AstGen;
use crate::lexer::Lexer;

pub struct HashParser<'c> {
    castle: &'c Castle,
}

impl<'c> HashParser<'c> {
    pub fn new(castle: &'c Castle) -> Self {
        Self { castle }
    }
}

impl<'c> ParserBackend<'c> for HashParser<'c> {
    fn parse_module(
        &self,
        resolver: impl ModuleResolver,
        _path: &Path,
        contents: &str,
    ) -> ParseResult<ast::Module<'c>> {
        let wall = self.castle.wall();

        let tokens = timed(
            || Lexer::new(contents, &wall).tokenise(),
            log::Level::Debug,
            |elapsed| println!("tokenise:    {:?}", elapsed),
        );

        let gen = AstGen::new(&tokens, &resolver, wall);

        timed(
            || gen.parse_module(),
            log::Level::Debug,
            |elapsed| println!("translation: {:?}", elapsed),
        )
    }

    fn parse_interactive(
        &self,
        resolver: impl ModuleResolver,
        contents: &str,
    ) -> ParseResult<ast::AstNode<'c, ast::BodyBlock<'c>>> {
        let wall = self.castle.wall();

        let tokens = Lexer::new(contents, &wall).tokenise();
        let gen = AstGen::new(&tokens, &resolver, wall);

        // for token in tokens.into_iter() {
        //     println!("{}", token);
        // }

        gen.parse_expression_from_interactive()
    }
}

#[cfg(test)]
mod tests {
    use hash_ast::resolve::ParModuleResolver;

    use super::*;

    #[test]
    fn type_size() {
        println!("{:?}", std::mem::size_of::<ParModuleResolver<HashParser>>());
    }
}
