//! Compiler error reporting
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::{grammar::Rule, location::Location};
use std::{fmt, path::PathBuf};

/// Error message prefix
const ERR: &str = "\x1b[31m\x1b[1merror\x1b[0m";

/// Hash ParseError enum represnting the variants of possible errors.
#[derive(Debug, Clone)]
pub enum ParseError {
    IoError {
        filename: PathBuf,
        err: String,
    },
    Parsing {
        positives: Vec<Rule>,
        negatives: Vec<Rule>,
        location: Location,
    },
    AstGeneration {
        rule: Rule,
        location: Location,
    },
    ImportError {
        import_name: PathBuf,
        location: Location,
    },
}

/// Convert a [pest::error::Error] into a [ParseError]
impl From<pest::error::Error<Rule>> for ParseError {
    fn from(pest: pest::error::Error<Rule>) -> Self {
        // @@Incomplete: Remove when we have real error formatting.
        println!("{}: Failed to parse:\n{}", ERR, pest);

        match pest.variant {
            pest::error::ErrorVariant::ParsingError {
                positives,
                negatives,
            } => ParseError::Parsing {
                positives,
                negatives,
                location: Location::from(pest.location),
            },
            _ => unreachable!(),
        }
    }
}

/// Format trait implementation for a ParseError
impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
