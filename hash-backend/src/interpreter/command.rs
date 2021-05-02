//! Hash interactive mode commands
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::interpreter::error::{report_interp_error, InterpreterError};

#[derive(Debug, Clone)]
pub enum InteractiveCommand {
    /// Quit the current interactive session
    Quit,
    /// Clear the console
    Clear,
    /// Get the type of the expression
    // @@Incomplete: This variant should store an AstNode<Expression> so that we can use the typer to get the type from the passed expression
    Type(String),
    /// Just prints the version of the current interactive mode
    Version,
}

impl InteractiveCommand {
    /// Attempt to convert a string into an interactive command
    pub fn from(input: &str) -> Option<InteractiveCommand> {
        match input {
            ":q" => Some(InteractiveCommand::Quit),
            ":c" | ":cls" | ":clear" => Some(InteractiveCommand::Clear),
            ":v" => Some(InteractiveCommand::Version),
            _ => {
                if input.len() > 3 {
                    let (command, arg) = input.split_at(3);
                    // check here if it begins with either a ':t' or a ':p' and then take an expression
                    if command == ":t " {
                        return Some(InteractiveCommand::Type(String::from(arg)));
                    }
                }

                None
            }
        }
    }

    /// Function used to report an error for a given string
    pub fn report_error(input: &str) {
        let mut args = input.split_ascii_whitespace();

        let command = args
            .next()
            .unwrap_or_else(|| panic!("Unable to report error for interactive command"));

        match command {
            ":c" | ":cls" | ":clear" | ":v" | ":q" => report_interp_error(
                InterpreterError::ArgumentError,
                &format!("Command '{}' does not take any arguments.", command),
            ),
            ":t" => {
                match args.next() {
                    Some(_) => unreachable!(), // if it did include a whitespace prior, it should of been caught in InteractiveCommand::from
                    None => report_interp_error(
                        InterpreterError::ArgumentError,
                        &format!("Command '{}' requires one argument.", command),
                    ),
                }
            }
            _ => report_interp_error(
                InterpreterError::ArgumentError,
                &format!("Unkown command '{}'.", command),
            ),
        }
    }
}
