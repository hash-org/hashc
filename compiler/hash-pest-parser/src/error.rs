use std::path::{Path, PathBuf};

use crate::grammar::Rule;
use hash_ast::{
    error::ParseError,
    location::{Location, SourceLocation},
    module::ModuleIdx,
};

pub(crate) struct PestError(pest::error::Error<Rule>, PathBuf);

impl From<(PathBuf, pest::error::Error<Rule>)> for PestError {
    fn from((path, pairs): (PathBuf, pest::error::Error<Rule>)) -> Self {
        PestError(pairs, path)
    }
}

impl PestError {
    pub(crate) fn into_inner(self) -> pest::error::Error<Rule> {
        self.0
    }

    pub(crate) fn inner(&self) -> &pest::error::Error<Rule> {
        &self.0
    }

    #[allow(dead_code)]
    pub(crate) fn path(&self) -> &Path {
        &self.1
    }
}

impl From<PestError> for ParseError {
    fn from(error: PestError) -> Self {
        // let path = error.path().to_owned();

        match error.inner().variant {
            pest::error::ErrorVariant::ParsingError { .. } => ParseError::Parsing {
                src: match error.inner().location {
                    pest::error::InputLocation::Pos(x) => Some(SourceLocation {
                        location: Location::pos(x),
                        module_index: ModuleIdx(0),
                    }),
                    pest::error::InputLocation::Span((x, y)) => Some(SourceLocation {
                        location: Location::span(x, y),
                        module_index: ModuleIdx(0),
                    }),
                },
                message: error.into_inner().to_string(),
            },
            _ => unreachable!(),
        }
    }
}
