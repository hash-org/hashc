//! Hash Compiler error and warning reporting module
//!
//! All rights reserved 2021 (c) The Hash Language authors

use hash_ast::error::ParseError;
use std::fmt;
use std::{io, process::exit};
use thiserror::Error;

use crate::{
    highlight::{highlight, Colour},
    reporting::{Report, ReportBuilder, ReportCodeBlock, ReportElement, ReportKind, ReportNote},
};

/// Enum representing the variants of error that can occur when running an interactive session
#[derive(Error, Debug)]
pub enum InteractiveCommandError {
    #[error("Unknown command `{0}`.")]
    UnrecognisedCommand(String),

    #[error("Command `{0}` does not take any arguments.")]
    ZeroArguments(String),

    // @Future: Maybe provide a second parameter to support multiple argument command
    #[error("Command `{0}` requires one argument.")]
    ArgumentMismatchError(String),

    #[error("Unexpected error: `{0}`")]
    InternalError(String),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[repr(u32)]
pub enum ErrorCode {
    Parsing = 1,
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:0>4}", *self as u32)
    }
}

impl From<ParseError> for Report {
    fn from(error: ParseError) -> Self {
        let mut builder = ReportBuilder::new();
        builder
            .with_kind(ReportKind::Error)
            .with_message("Failed to parse")
            .with_error_code(ErrorCode::Parsing);

        match error {
            ParseError::Parsing { message, src } | ParseError::Token { message, src } => {
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "here")))
                    .add_element(ReportElement::Note(ReportNote::new("note", message)));
            }
        };

        // @@ErrorReporting: we might want to properly handle incomplete reports?
        builder.build().unwrap()
    }
}

/// Errors that might occur when attempting to compile and or interpret a
/// program.
#[derive(Debug, Error)]
pub enum CompilerError {
    #[error("{0}")]
    IoError(#[from] io::Error),
    #[error("{message}")]
    ArgumentError { message: String },
    #[error("{0}")]
    InterpreterError(#[from] InteractiveCommandError),
}

impl CompilerError {
    pub fn report_and_exit(&self) -> ! {
        self.report();
        exit(-1);
    }

    pub fn report(&self) {
        println!("{}: {}", highlight(Colour::Red, "error"), self);
    }
}
