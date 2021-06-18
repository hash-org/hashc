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
    ast::{self, AstAllocator},
    error::{ParseError, ParseResult},
    parse::{timed, ModuleResolver, ParserBackend},
};

use crate::{error::PestError, translate::PestAstBuilder};

pub type HashPair<'a> = pest::iterators::Pair<'a, Rule>;

impl ParserBackend for HashGrammar {
    fn parse_module<'ast, 'alloc>(
        &self,
        resolver: &mut impl ModuleResolver,
        path: &Path,
        contents: &str,
        allocator: &'alloc impl AstAllocator<'ast, 'alloc>,
    ) -> ParseResult<ast::Module<'ast>>
    where
        'ast: 'alloc,
    {
        let mut builder = PestAstBuilder::new(resolver, allocator);
        let pest_result = timed(
            || HashGrammar::parse(Rule::module, contents),
            log::Level::Debug,
            |elapsed| println!("pest: {:?}", elapsed),
        )
        .map_err(|e| ParseError::from(PestError::from((path.to_owned(), e))))?;

        timed(
            || {
                Ok(ast::Module {
                    contents: allocator
                        .try_alloc_slice(pest_result.map(|x| builder.transform_statement(x)))?,
                })
            },
            log::Level::Debug,
            |elapsed| println!("translation: {:?}", elapsed),
        )
    }

    fn parse_statement<'ast, 'alloc>(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &str,
        allocator: &'alloc impl AstAllocator<'ast, 'alloc>,
    ) -> ParseResult<ast::AstNode<'ast, ast::Statement<'ast>>>
    where
        'ast: 'alloc,
    {
        let mut builder = PestAstBuilder::new(resolver, allocator);
        match HashGrammar::parse(Rule::statement, contents) {
            Ok(mut result) => builder.transform_statement(result.next().unwrap()),
            // TODO: use constant for "interactive"
            Err(e) => Err(ParseError::from(PestError::from(("interactive".into(), e)))),
        }
    }
}
