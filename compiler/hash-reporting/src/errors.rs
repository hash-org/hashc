//! Hash Compiler error and warning reporting module.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use hash_ast::{error::ParseError, ident::IDENTIFIER_MAP};
use hash_typecheck::{error::TypecheckError, storage::GlobalStorage, writer::TypeWithStorage};
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
            TypecheckError::TypeMismatch(left, right) => {
                let left_ty = TypeWithStorage::new(left, &storage);
                let right_ty = TypeWithStorage::new(right, &storage);

                // @@TODO: we want to print the location of the lhs_expression where the type mismatches
                //         and the right hand side
                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    format!(
                        "Types mismatch, got a `{}`, but wanted a `{}`.",
                        left_ty, right_ty
                    ),
                )));
            }
            TypecheckError::UsingBreakOutsideLoop(src) => {
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "here")))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        "You can't use a `break` clause outside of a loop.",
                    )));
            }
            TypecheckError::UsingContinueOutsideLoop(src) => {
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "here")))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        "You can't use a `continue` clause outside of a loop.",
                    )));
            }
            TypecheckError::UsingReturnOutsideFunction(src) => {
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "here")))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        "You can't use a `return` clause outside of a function body.",
                    )));
            }
            TypecheckError::RequiresIrrefutablePattern(src) => {
                builder
                .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "This pattern isn't refutable")))
                .add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    "Destructuring statements in `let` or `for` statements must use an irrefutable pattern.",
                )));
            }
            TypecheckError::UnresolvedSymbol(symbol) => {
                let ident_path = symbol.get_ident();
                let formatted_symbol = format!("{}", IDENTIFIER_MAP.get_path(ident_path));

                if let Some(location) = symbol.location() {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "Unresolved symbol",
                    )));
                }

                // At-least we can print the symbol that wasn't found...
                builder.add_element(ReportElement::Note(ReportNote::new(
                    "note",
                    format!(
                        "Symbol `{}` is not defined in the current scope.",
                        formatted_symbol
                    ),
                )));
            }
            TypecheckError::TryingToNamespaceType(_) => todo!(),
            TypecheckError::TryingToNamespaceVariable(_) => todo!(),
            TypecheckError::UsingVariableInTypePos(_) => todo!(),
            TypecheckError::UsingTypeInVariablePos(_) => todo!(),
            TypecheckError::TypeIsNotStruct {
                ty,
                location,
                ty_def_location,
            } => {
                let ty = TypeWithStorage::new(ty, &storage);

                // Print where the original type is defined with an annotation.
                if let Some(ty_def_location) = ty_def_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        ty_def_location,
                        format!("The type `{}` is defined here.", ty),
                    )));
                }

                // Print where the literal being created...
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "Not a struct",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!("This type `{}` isn't a struct.", ty),
                    )));
            }
            TypecheckError::UnresolvedStructField {
                ty_def_location,
                ty_def_name,
                field_name,
                location,
            } => {
                let name = IDENTIFIER_MAP.get_ident(field_name);
                let ty_name = IDENTIFIER_MAP.get_ident(ty_def_name);

                // If we have the location of the definition, we can print it here
                if let Some(ty_def_location) = ty_def_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        ty_def_location,
                        format!("The struct `{}` is defined here.", ty_name),
                    )));
                }

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "Unknown field",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!("The field `{}` doesn't exist on struct `{}`.", name, name),
                    )));
            }
            TypecheckError::ExpectingBooleanInCondition { found, location } => {
                let found_ty = TypeWithStorage::new(found, &storage);

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "Expression should be of `boolean` type",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!("In `if` statements, the condition must be explicitly of `boolean` type, however the expression was found to be of `{}` type.", found_ty),
                    )));
            }
            TypecheckError::MissingStructField {
                ty_def_location,
                ty_def_name,
                field_name,
                field_location,
            } => {
                let name = IDENTIFIER_MAP.get_ident(field_name);
                let ty_name = IDENTIFIER_MAP.get_ident(ty_def_name);

                // If we have the location of the definition, we can print it here
                if let Some(ty_def_location) = ty_def_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        ty_def_location,
                        format!("The struct `{}` is defined here.", ty_name),
                    )));
                }

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        field_location,
                        "Struct is missing field",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!("The struct `{}` is missing the field `{}`.", ty_name, name),
                    )));
            }
            TypecheckError::BoundRequiresStrictlyTypeVars => todo!(),
            TypecheckError::InvalidPropertyAccess {
                field_name,
                location,
                ty_def_name,
                ty_def_location,
            } => {
                let name = IDENTIFIER_MAP.get_ident(field_name);
                let ty_name = IDENTIFIER_MAP.get_ident(ty_def_name);

                // If we have the location of the definition, we can print it here
                if let Some(ty_def_location) = ty_def_location {
                    builder.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        ty_def_location,
                        format!("The struct `{}` is defined here.", ty_name),
                    )));
                }

                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                        location,
                        "unknown field",
                    )))
                    .add_element(ReportElement::Note(ReportNote::new(
                        "note",
                        format!("The field `{}` doesn't exist on type `{}`.", name, ty_name),
                    )));
            }
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
