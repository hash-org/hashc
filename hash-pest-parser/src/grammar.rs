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

use hash_ast::{
    ast,
    error::{ParseError, ParseResult},
    location::Location,
    parse::{ModuleResolver, ParserBackend},
};

pub type HashPair<'a> = pest::iterators::Pair<'a, Rule>;

impl<'a> ParserBackend<'a> for HashGrammar {
    fn parse_module(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &'a str,
        bump: &Bump,
    ) -> ParseResult<ast::Module> {
        let builder = PestAstBuilder::new(resolver, bump);
        match HashGrammar::parse(Rule::module, contents) {
            Ok(result) => Ok(ast::Module {
                contents: result
                    .take_while(|x| x.as_rule() != Rule::EOI)
                    .map(|x| builder.transform_statement(x))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            Err(e) => Err(PestError(e).into()),
        }
    }

    fn parse_statement(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &'a str,
        bump: &Bump,
    ) -> ParseResult<ast::AstNode<ast::Statement>> {
        match HashGrammar::parse(Rule::statement, contents) {
            Ok(mut result) => HashPair::from_inner(result.next().unwrap()).into_ast(resolver),
            Err(e) => Err(PestError(e).into()),
        }
    }
}
