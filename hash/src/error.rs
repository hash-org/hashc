//! Compiler general error reporting
//
// All rights reserved 2021 (c) The Hash Language authors

use std::{io, process::exit};

use hash_ast::error::ParseError;
use thiserror::Error;

use crate::interactive::error::InterpreterError;

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
    InterpreterError(#[from] InterpreterError),
}

pub type CompilerResult<T> = Result<T, CompilerError>;

impl CompilerError {
    pub fn report_and_exit(&self) -> ! {
        self.report();
        exit(-1);
    }

    pub fn report(&self) {
        println!("{}: {}", ERR, self);
    }
}
