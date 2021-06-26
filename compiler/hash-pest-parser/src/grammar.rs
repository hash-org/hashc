//! Hash language grammar implementation using pest
//
// All rights reserved 2021 (c) The Hash Language authors

/// Language parser, created via [pest]
#[allow(clippy::upper_case_acronyms)]
mod derived {
    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "grammar.pest"] // relative to src
    pub struct HashGrammar;
}

use std::path::Path;

pub use derived::{HashGrammar, Rule};
use pest::Parser;

use hash_ast::{
    ast,
    error::{ParseError, ParseResult},
    parse::{timed, ModuleResolver, ParserBackend},
};

use crate::{error::PestError, translate::PestAstBuilder};

pub type HashPair<'a> = pest::iterators::Pair<'a, Rule>;

impl ParserBackend for HashGrammar {
    fn parse_module(
        &self,
        resolver: &mut impl ModuleResolver,
        path: &Path,
        contents: &str,
    ) -> ParseResult<ast::Module> {
        let mut builder = PestAstBuilder::new(resolver);
        let pest_result = timed(
            || HashGrammar::parse(Rule::module, contents),
            log::Level::Debug,
            |elapsed| println!("pest: {:?}", elapsed),
        )
        .map_err(|e| ParseError::from(PestError::from((path.to_owned(), e))))?;

        timed(
            || {
                Ok(ast::Module {
                    contents: pest_result
                        .map(|x| builder.transform_statement(x))
                        .collect::<Result<_, _>>()?,
                })
            },
            log::Level::Debug,
            |elapsed| println!("translation: {:?}", elapsed),
        )
    }

    fn parse_interactive(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &str,
    ) -> ParseResult<ast::AstNode<ast::BodyBlock>> {
        let mut builder = PestAstBuilder::new(resolver);
        match HashGrammar::parse(Rule::interactive, contents) {
            Ok(mut result) => {
                let pair = result.next().unwrap();
                let ab = builder.builder_from_pair(&pair);
                Ok(ab.node(builder.transform_body_block(pair)?))
            }
            // @@TODO: use constant for "interactive"
            Err(e) => Err(ParseError::from(PestError::from(("interactive".into(), e)))),
        }
    }
}
