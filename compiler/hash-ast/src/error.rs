//! Compiler error reporting
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::location::SourceLocation;
use std::{io, num::{ParseFloatError, ParseIntError}, path::PathBuf};
use thiserror::Error;

/// Hash ParseError enum represnting the variants of possible errors.
#[derive(Debug, Clone, Error)]
pub enum ParseError {
    #[error("An IO error occurred when reading {filename}: {err}")]
    IoError { filename: PathBuf, err: String },
    #[error("Parse error at {src}:\n{message}")]
    Parsing {
        message: String,
        src: SourceLocation,
    },
    #[error("Cannot locate module {import_name} at {src}")]
    ImportError {
        import_name: PathBuf,
        src: SourceLocation,
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

impl From<ParseIntError> for ParseError {
    fn from(_: ParseIntError) -> Self {
        todo!()
    }
}

impl From<ParseFloatError> for ParseError {
    fn from(_: ParseFloatError) -> Self {
        todo!()
    }
}
