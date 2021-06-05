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

pub use derived::{HashGrammar, Rule};
use pest::Parser;

use hash_ast::{ast::{self, AstAllocator}, error::{ParseError, ParseResult}, location::Location, parse::{ModuleResolver, ParserBackend}};

use crate::translate::{PestAstBuilder};

pub type HashPair<'a> = pest::iterators::Pair<'a, Rule>;

impl ParserBackend for HashGrammar {
    fn parse_module<'ast>(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &str,
        allocator: &'ast impl AstAllocator,
    ) -> ParseResult<ast::Module<'ast>> {
        let builder = PestAstBuilder::new(resolver, allocator);
        match HashGrammar::parse(Rule::module, contents) {
            Ok(result) => Ok(ast::Module {
                contents: allocator.alloc_ast_nodes(result
                    .map(|x| builder.transform_statement(x))),
            }),
            Err(e) => Err(e.into()),
        }
    }

    fn parse_statement<'ast>(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &str,
        allocator: &'ast impl AstAllocator,
    ) -> ParseResult<ast::AstNode<'ast, ast::Statement<'ast>>> {
        match HashGrammar::parse(Rule::statement, contents) {
            Ok(mut result) => HashPair::from_inner(result.next().unwrap()).into_ast(resolver),
            Err(e) => Err(e.into()),
        }
    }
}
