//! Hash Compiler error and warning reporting module
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::{io, process::exit};
use thiserror::Error;

use hash_ast::error::ParseError;

/// Enum representing the variants of error that can occur when running an interactive session
#[derive(Error, Debug)]
pub enum InteractiveCommandError {
    #[error("Unkown command `{0}`.")]
    UnrecognisedCommand(String),

    #[error("Command `{0}` does not take any arguments.")]
    ZeroArguments(String),

    // @Future: Maybe provide a second paramater to support multiple argument command
    #[error("Command `{0}` requires one argument.")]
    ArgumentMismatchError(String),

    #[error("Unexpected error: `{0}`")]
    InternalError(String),
}

/// Error message prefix
const ERR: &str = "\x1b[31m\x1b[1merror\x1b[0m";

/// Errors that might occur when attempting to compile and or interpret a
/// program.
#[derive(Debug, Error)]
pub enum CompilerError {
    #[error("{0}")]
    IoError(#[from] io::Error),
    #[error("Sorry :^(\nInternal panic: {message}\n{}", match .extra_info {
        Some(x) => &x,
        None => "",
    })]
    #[allow(dead_code)]
    InternalError {
        message: String,
        extra_info: Option<String>,
    },
    #[error("{0}")]
    ParseError(#[from] ParseError),
    #[error("{0}")]
    InterpreterError(#[from] InteractiveCommandError),
}

impl CompilerError {
    pub fn report_and_exit(&self) -> ! {
        self.report();
        exit(-1);
    }

    pub fn report(&self) {
        println!("{}: {}", ERR, self);
    }
}
