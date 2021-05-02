//! Hash interactive mode error reporting
//
// All rights reserved 2021 (c) The Hash Language authors

/// Enum representing the variants of error that can occur when running an interactive session
pub enum InterpreterError {
    ArgumentError,
}

/// Error message prefix
const ERR: &str = "\x1b[31m\x1b[1merror\x1b[0m";

/// Function that is used by the interpeter ro report interpreter errors
pub fn report_interp_error(err: InterpreterError, msg: &str) {
    match err {
        InterpreterError::ArgumentError => {
            println!("{}: {}", ERR, msg);
        }
    };
}
