//! Compiler error reporting
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::{grammar::Rule, location::Location};
use std::fmt;

/// Error message prefix
const ERR: &str = "\x1b[31m\x1b[1merror\x1b[0m";

/// Hash ParseError enum represnting the variants of possible errors.
#[derive(Debug, Clone)]
pub enum ParseError {
    IoError {
        filename: String,
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
}

/// Convert a [pest::error::Error] into a [ParseError]
impl<'a> From<pest::error::Error<Rule>> for ParseError {
    fn from(pest: pest::error::Error<Rule>) -> Self {
        match pest.variant {
            pest::error::ErrorVariant::ParsingError {
                ref positives,
                ref negatives,
            } => {
                // @@Incomplete: Remove when we have real error formatting.
                println!("{}: Failed to parse:\n{}", ERR, pest);
                ParseError::Parsing {
                    positives: positives.clone(),
                    negatives: negatives.clone(),
                    location: Location::from(pest.location),
                }
            }
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

// impl<'a> Error for ParseError {}

// /// Function that is used to report a general compiler error
// pub fn report_error(err_type: ErrorType, err_msg: String) {
//     let prefix = match err_type {
//         ErrorType::ParseError => "Failed to parse\n",
//         // ErrorType::CicrularDependency => "Failed to import",
//         ErrorType::IoError => "Failed to read file",
//         ErrorType::InternalError => "Internal Panic", // @@TODO: add an internal panic function
//     };

//     println!("{}: {}{}", ERR, prefix, err_msg);
//     exit(-1);
// }
