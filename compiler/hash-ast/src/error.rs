//! Compiler AST error data types for reporting
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::location::SourceLocation;
use std::{io, path::PathBuf};
use thiserror::Error;

/// Hash ParseError enum representing the variants of possible errors.
#[derive(Debug, Clone)]
pub enum ParseError {
    Parsing {
        message: String,
        src: SourceLocation,
    },
    Token {
        message: String,
        src: SourceLocation,
    },
}

pub type ParseResult<T> = Result<T, ParseError>;

/// Import error is an abstraction to represent errors that are in relevance to IO
/// operations rather than parsing operations.
#[derive(Debug, Clone, Error)]
#[error("Couldn't import module '{filename}': {message}")]
pub struct ImportError {
    pub filename: PathBuf,
    pub message: String,
    pub src: Option<SourceLocation>,
}

impl From<(io::Error, PathBuf)> for ImportError {
    fn from((err, filename): (io::Error, PathBuf)) -> Self {
        ImportError {
            message: err.to_string(),
            filename,
            src: None,
        }
    }
}

impl From<ImportError> for ParseError {
    fn from(err: ImportError) -> Self {
        ParseError::Parsing {
            message: err.to_string(),
            src: err.src.unwrap_or_else(SourceLocation::interactive),
        }
    }
}
