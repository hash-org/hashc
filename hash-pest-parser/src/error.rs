use crate::grammar::Rule;
use hash_ast::{error::ParseError, location::Location};
pub(crate) struct PestError(pub pest::error::Error<Rule>);

impl From<pest::error::Error<Rule>> for PestError {
    fn from(pairs: pest::error::Error<Rule>) -> Self {
        PestError(pairs)
    }
}

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
                message: error.into_inner().to_string(),
            },
            _ => unreachable!(),
        }
    }
}
