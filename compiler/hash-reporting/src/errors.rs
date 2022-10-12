//! Hash Compiler error and warning reporting module.
//!
//! @@Todo: clean this up, it's a mess.
use std::{io, process::exit};

use thiserror::Error;

use crate::highlight::{highlight, Colour, Modifier};

/// Enum representing the variants of error that can occur when running an
/// interactive session
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
