//! Compiler error reporting
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::location::Location;
use std::{fmt, io, path::PathBuf};

/// Error message prefix
// const ERR: &str = "\x1b[31m\x1b[1merror\x1b[0m";

/// Hash ParseError enum represnting the variants of possible errors.
#[derive(Debug, Clone)]
pub enum ParseError {
    IoError {
        filename: PathBuf,
        err: String,
    },
    Parsing {
        message: String,
        location: Location,
    },
    AstGeneration {
        message: String,
        location: Location,
    },
    ImportError {
        import_name: PathBuf,
        location: Option<Location>,
    },
}

pub type ParseResult<T> = Result<T, ParseError>;

impl From<(io::Error, PathBuf)> for ParseError {
    fn from((err, filename): (io::Error, PathBuf)) -> Self {
        ParseError::IoError {
            err: err.to_string(),
            filename,
        }
    }
}

/// Format trait implementation for a ParseError
impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
