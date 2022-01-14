//! Compiler AST error data types for reporting
//!
//! All rights reserved 2021 (c) The Hash Language authors

use hash_reporting::{
    errors::ErrorCode,
    reporting::{Report, ReportBuilder, ReportCodeBlock, ReportElement, ReportKind, ReportNote},
};
use hash_source::location::SourceLocation;
use std::{io, path::PathBuf};
use thiserror::Error;

/// Hash ParseError enum representing the variants of possible errors.
#[derive(Debug, Clone)]
pub enum ParseError {
    Parsing {
        message: String,
        src: Option<SourceLocation>,
    },
    Token {
        message: String,
        src: SourceLocation,
    },
}

impl ParseError {
    pub fn create_report(self) -> Report {
        let mut builder = ReportBuilder::new();
        builder
            .with_kind(ReportKind::Error)
            .with_message("Failed to parse")
            .with_error_code(ErrorCode::Parsing);

        match self {
            ParseError::Parsing {
                message,
                src: Some(src),
            }
            | ParseError::Token { message, src } => {
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "here")))
                    .add_element(ReportElement::Note(ReportNote::new("note", message)));
            }
            // When we don't have a source for the error, just add a note
            ParseError::Parsing { message, src: None } => {
                builder.with_message(message);
            }
        };

        // @@ErrorReporting: we might want to properly handle incomplete reports?
        builder.build().unwrap()
    }
}

pub type ParseResult<T> = Result<T, ParseError>;

/// Import error is an abstraction to represent errors that are in relevance to IO
/// operations rather than parsing operations.
#[derive(Debug, Clone, Error)]
#[error("Couldn't import module '{filename}':\n {message}")]
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
            src: err.src,
        }
    }
}
