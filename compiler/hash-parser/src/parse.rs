use std::path::Path;

use hash_ast::{
    ast::{self, AstNode, BodyBlock},
    error::ParseResult,
    location::Location,
    parse::{ModuleResolver, ParserBackend},
};
use hash_utils::timed;

use crate::{lexer::tokenise, token::Token};

pub struct HashParser {}

impl ParserBackend for HashParser {
    fn parse_module(
        &self,
        _resolver: &mut impl ModuleResolver,
        _path: &Path,
        contents: &str,
    ) -> ParseResult<ast::Module> {
        let _tokens = timed(
            || {
                let tokeniser = tokenise(contents);

                println!("tokens: {:#?}", tokeniser.collect::<Vec<Token>>());
            },
            log::Level::Debug,
            |elapsed| println!("pest: {:?}", elapsed),
        );

        todo!()

        // timed(
        //     || {
        //         Ok(ast::Module {
        //             contents: pest_result
        //                 .map(|x| builder.transform_statement(x))
        //                 .collect::<Result<_, _>>()?,
        //         })
        //     },
        //     log::Level::Debug,
        //     |elapsed| println!("translation: {:?}", elapsed),
        // )
    }

    fn parse_interactive(
        &self,
        _resolver: &mut impl ModuleResolver,
        contents: &str,
    ) -> ParseResult<ast::AstNode<ast::BodyBlock>> {
        // let mut lexer = lexer::Lexer::new(contents);
        let tokeniser = tokenise(contents);

        println!("tokens: {:#?}", tokeniser.collect::<Vec<Token>>());

        Ok(AstNode::new(
            BodyBlock {
                statements: vec![],
                expr: None,
            },
            Location::span(0, 0),
        ))
    }
}
