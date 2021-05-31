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
    parse::{IntoAstNode, ModuleResolver, ParserBackend},
};

pub struct HashPair<'a>(pest::iterators::Pair<'a, Rule>);

#[allow(dead_code)]
impl<'a> HashPair<'a> {
    pub(crate) fn from_inner(pair: pest::iterators::Pair<'a, Rule>) -> Self {
        HashPair(pair)
    }

    pub(crate) fn into_inner(self) -> pest::iterators::Pair<'a, Rule> {
        self.0
    }

    pub(crate) fn inner(&self) -> &pest::iterators::Pair<'a, Rule> {
        &self.0
    }

    pub(crate) fn inner_mut(&mut self) -> &mut pest::iterators::Pair<'a, Rule> {
        &mut self.0
    }
}
pub struct PestError(pest::error::Error<Rule>);

impl From<pest::error::Error<Rule>> for PestError {
    fn from(pairs: pest::error::Error<Rule>) -> Self {
        PestError(pairs)
    }
}

#[allow(dead_code)]
impl PestError {
    pub(crate) fn into_inner(self) -> pest::error::Error<Rule> {
        self.0
    }

    pub(crate) fn inner(&self) -> &pest::error::Error<Rule> {
        &self.0
    }

    pub(crate) fn inner_mut(&mut self) -> &mut pest::error::Error<Rule> {
        &mut self.0
    }
}

impl From<PestError> for ParseError {
    fn from(error: PestError) -> Self {
        match error.inner().variant {
            pest::error::ErrorVariant::ParsingError { .. } => ParseError::Parsing {
                location: match error.inner().location {
                    pest::error::InputLocation::Pos(x) => Location::Pos(x),
                    pest::error::InputLocation::Span((x, y)) => Location::Span(x, y),
                },
            },
            _ => unreachable!(),
        }
    }
}

impl<'a> ParserBackend<'a> for HashGrammar {
    fn parse_module(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &'a str,
    ) -> ParseResult<ast::Module> {
        match HashGrammar::parse(Rule::module, contents) {
            Ok(result) => Ok(ast::Module {
                contents: result
                    .take_while(|x| x.as_rule() != Rule::EOI)
                    .map(HashPair::from_inner)
                    .map(|x| x.into_ast(resolver))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            Err(e) => Err(PestError(e).into()),
        }
    }

    fn parse_statement(
        &self,
        resolver: &mut impl ModuleResolver,
        contents: &'a str,
    ) -> ParseResult<ast::AstNode<ast::Statement>> {
        match HashGrammar::parse(Rule::statement, contents) {
            Ok(mut result) => HashPair::from_inner(result.next().unwrap()).into_ast(resolver),
            Err(e) => Err(PestError(e).into()),
        }
    }
}
