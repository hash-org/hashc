use std::{
    fmt,
    path::{Path, PathBuf},
};

use crate::grammar::Rule;
use hash_ast::{
    error::ParseError,
    location::{Location, SourceLocation},
    module::ModuleIdx,
};
use hash_utils::printing::SliceDisplay;

#[derive(Debug)]
pub(crate) struct PestError(pest::error::Error<Rule>, PathBuf);

impl From<(PathBuf, pest::error::Error<Rule>)> for PestError {
    fn from((path, pairs): (PathBuf, pest::error::Error<Rule>)) -> Self {
        PestError(pairs, path)
    }
}

impl PestError {
    pub(crate) fn inner(&self) -> &pest::error::Error<Rule> {
        &self.0
    }

    #[allow(dead_code)]
    pub(crate) fn path(&self) -> &Path {
        &self.1
    }
}

struct PestRule(Rule);

impl fmt::Display for PestRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // @@Improvement: For now we will rely on the debug display implementation, but at later stages
        // we can add custom labels for rules when unifying behaviour between parser backends.
        write!(f, "{:?}", self.0)
    }
}

impl From<PestError> for ParseError {
    fn from(error: PestError) -> Self {
        match &error.inner().variant {
            pest::error::ErrorVariant::ParsingError { positives, .. } => {
                let rules = positives
                    .to_vec()
                    .iter()
                    .map(|x| PestRule(*x))
                    .collect::<Vec<_>>();
                let pos_wrapper = SliceDisplay(rules.as_slice());
                // let neg_wrapper = ErrorRuleVec(negatives); // TODO: deal with this, can it even be non-empty?

                ParseError::Parsing {
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
                    message: format!("Expected {}", pos_wrapper),
                }
            }
            _ => unreachable!(),
        }
    }
}
