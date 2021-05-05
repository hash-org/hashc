//! Hash interactive mode commands
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::interpreter::error::InterpreterError;

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

    /// A string representing a statement that will be executed
    Code(String),
}

impl InteractiveCommand {
    /// Attempt to convert a string into an interactive command
    pub fn from(input: &str) -> Result<InteractiveCommand, InterpreterError> {
        if !input.starts_with(':') {
            // @@Efficiency: redudant copying here!
            return Ok(InteractiveCommand::Code(input.to_string()));
        }

        match input {
            ":q" => Ok(InteractiveCommand::Quit),
            ":c" | ":cls" | ":clear" => Ok(InteractiveCommand::Clear),
            ":v" => Ok(InteractiveCommand::Version),
            _ => {
                let arg = input.strip_prefix(":t ");

                match arg {
                    None => {
                        let mut args = input.split_ascii_whitespace();

                        let command = args.next().unwrap_or_else(|| {
                            panic!("Unable to report error for interactive command")
                        });

                        match command {
                            ":c" | ":cls" | ":clear" | ":v" | ":q" => {
                                Err(InterpreterError::ZeroArguments(format!("{}", command)))
                            }
                            ":t" => {
                                match args.next() {
                                    Some(_) => unreachable!(), // if it did include a whitespace prior, it should of been caught in InteractiveCommand::from
                                    None => Err(InterpreterError::ArgumentMismatchError(format!(
                                        "{}",
                                        command
                                    ))),
                                }
                            }
                            _ => Err(InterpreterError::UnrecognisedCommand(format!(
                                "{}",
                                command
                            ))),
                        }
                    }
                    Some(expr) => Ok(InteractiveCommand::Type(expr.to_string())),
                }
            }
        }
    }
}
