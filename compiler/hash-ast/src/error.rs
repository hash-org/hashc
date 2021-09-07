//! Compiler error reporting
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::location::SourceLocation;
use std::{io, path::PathBuf};
use thiserror::Error;

/// Hash ParseError enum representing the variants of possible errors.
#[derive(Debug, Clone, Error)]
pub enum ParseError {
    #[error("An IO error occurred when reading {filename}: {message}")]
    IoError { filename: PathBuf, message: String },
    #[error("Parse error at {src}:\n{message}")]
    Parsing {
        message: String,
        src: SourceLocation,
    },
    #[error("Tokeniser error at {src}:\n{message}")]
    Token {
        message: String,
        src: SourceLocation,
    },
    #[error("Cannot locate module {import_name} at {src}")]
    ImportError {
        import_name: PathBuf,
        src: SourceLocation,
    },
}

impl ParseError {
    pub fn into_message(self) -> String {
        match self {
            ParseError::IoError {
                filename: _,
                message,
            } => message,
            ParseError::Parsing { message, src: _ } | ParseError::Token { message, src: _ } => {
                message
            }
            ParseError::ImportError {
                import_name: _,
                src: _,
            } => todo!(),
        }
    }
}

pub type ParseResult<T> = Result<T, ParseError>;

impl From<(io::Error, PathBuf)> for ParseError {
    fn from((err, filename): (io::Error, PathBuf)) -> Self {
        ParseError::IoError {
            message: err.to_string(),
            filename,
        }
    }
}
