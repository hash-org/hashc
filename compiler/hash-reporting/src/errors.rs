//! Hash Compiler error and warning reporting module.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use hash_ast::error::ParseError;
use hash_typecheck::{error::TypecheckError, storage::GlobalStorage};
use std::fmt;
use std::{io, process::exit};
use thiserror::Error;

use crate::{
    highlight::{highlight, Colour, Modifier},
    reporting::{Report, ReportBuilder, ReportCodeBlock, ReportElement, ReportKind, ReportNote},
};

/// Enum representing the variants of error that can occur when running an interactive session
#[derive(Error, Debug)]
pub enum InteractiveCommandError {
    /// Encountering an unknown command.
    #[error("Unknown command `{0}`.")]
    UnrecognisedCommand(String),
    /// When a command received arguments it wasn't expecting.
    #[error("Command `{0}` does not take any arguments.")]
    ZeroArguments(String),
    /// When a command received an invalid number of arguments.
    // @Future: Maybe provide a second parameter to support multiple argument command
    #[error("Command `{0}` requires one argument.")]
    ArgumentMismatchError(String),
    /// An unknown error occurred.
    #[error("Unexpected error: `{0}`")]
    InternalError(String),
}

/// General enumeration of all reportable errors with associated error codes.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[repr(u32)]
pub enum ErrorCode {
    Parsing = 1,
    Typecheck = 2, // @@Temporary
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:0>4}", *self as u32)
    }
}

impl From<(TypecheckError, GlobalStorage<'_, '_, '_>)> for Report {
    fn from((error, storage): (TypecheckError, GlobalStorage<'_, '_, '_>)) -> Self {
        let mut builder = ReportBuilder::new();
        builder
            .with_kind(ReportKind::Error)
            .with_message("Failed to typecheck")
            .with_error_code(ErrorCode::Typecheck); // @@ErrorReporting: Get the correct typecheck code

        match error {
            TypecheckError::TypeMismatch(_, _) => todo!(),
            TypecheckError::UsingBreakOutsideLoop(_) => todo!(),
            TypecheckError::UsingContinueOutsideLoop(_) => todo!(),
            TypecheckError::UsingReturnOutsideFunction(_) => todo!(),
            TypecheckError::RequiresIrrefutablePattern(_) => todo!(),
            TypecheckError::UnresolvedSymbol(symbol) => {}
            TypecheckError::TryingToNamespaceType(_) => todo!(),
            TypecheckError::TryingToNamespaceVariable(_) => todo!(),
            TypecheckError::UsingVariableInTypePos(_) => todo!(),
            TypecheckError::UsingTypeInVariablePos(_) => todo!(),
            TypecheckError::TypeIsNotStruct(_) => todo!(),
            TypecheckError::UnresolvedStructField {
                struct_type,
                field_name,
                location,
            } => todo!(),
            TypecheckError::InvalidPropertyAccess {
                struct_type,
                struct_defn_location,
                field_name,
                access_location,
            } => todo!(),
            TypecheckError::ExpectingBooleanInCondition { found, location } => todo!(),
            TypecheckError::MissingStructField {
                struct_type,
                field_name,
                struct_lit_location,
            } => todo!(),
            TypecheckError::BoundRequiresStrictlyTypeVars => todo!(),
        }

        // @@ErrorReporting: we might want to properly handle incomplete reports?
        builder.build().unwrap()
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

/// Errors that might occur when attempting to compile and or interpret a
/// program.
#[derive(Debug, Error)]
pub enum CompilerError {
    /// Generic IO error.
    #[error("{0}")]
    IoError(#[from] io::Error),
    /// Error when arguments to a particular command occur.
    #[error("{message}")]
    ArgumentError { message: String },
    /// Errors that occur when running a command.
    #[error("{0}")]
    InterpreterError(#[from] InteractiveCommandError),
}

impl CompilerError {
    pub fn report_and_exit(&self) -> ! {
        self.report();
        exit(-1);
    }

    pub fn report(&self) {
        println!(
            "{}: {}",
            highlight(Colour::Red, "error"),
            highlight(Modifier::Bold, self.to_string())
        );
    }
}
