//! Hash interactive mode commands
//
// All rights reserved 2021 (c) The Hash Language authors

use crate::interactive::error::InterpreterError;

#[derive(Debug, Clone)]
pub enum InteractiveCommand<'i> {
    /// Quit the current interactive session
    Quit,
    /// Clear the console
    Clear,
    /// Get the type of the expression
    Type(&'i str),
    /// Count the nodes in the expression
    Count(&'i str),
    /// Display the node tree of the expression
    Display(&'i str),
    /// Just prints the version of the current interactive mode
    Version,
    /// A string representing a statement that will be executed
    Code(&'i str),
}

struct CommandDelegator<'i> {
    command: &'i str,
    arg: Option<&'i str>,
}

impl<'i> CommandDelegator<'i> {
    fn new(command: &'i str, arg: Option<&'i str>) -> Self {
        Self { command, arg }
    }

    fn with_arg(&self, f: impl FnOnce(&'i str) -> InteractiveResult<'i>) -> InteractiveResult<'i> {
        match self.arg {
            None => Err(InterpreterError::ArgumentMismatchError(
                self.command.to_string(),
            )),
            Some(arg) => f(arg),
        }
    }

    fn without_arg(&self, command: InteractiveCommand<'i>) -> InteractiveResult<'i> {
        match self.arg {
            None => Ok(command),
            Some(_) => Err(InterpreterError::ZeroArguments(self.command.to_string())),
        }
    }
}

type InteractiveResult<'i> = Result<InteractiveCommand<'i>, InterpreterError>;

impl InteractiveCommand<'_> {
    /// Attempt to convert a string into an interactive command
    pub fn from(input: &str) -> InteractiveResult<'_> {
        if !input.starts_with(':') {
            // @@Efficiency: redudant copying here!
            return Ok(InteractiveCommand::Code(input));
        }

        let mut prefix = input.trim_start().split_ascii_whitespace();
        match prefix.next() {
            Some(command) => {
                let d = CommandDelegator::new(command, prefix.next());
                match command {
                    ":q" => d.without_arg(InteractiveCommand::Quit),
                    ":c" | ":cls" | ":clear" => d.without_arg(InteractiveCommand::Clear),
                    ":v" => d.without_arg(InteractiveCommand::Version),
                    ":t" => d.with_arg(|arg| Ok(InteractiveCommand::Type(arg))),
                    ":n" => d.with_arg(|arg| Ok(InteractiveCommand::Count(arg))),
                    ":d" => d.with_arg(|arg| Ok(InteractiveCommand::Display(arg))),
                    _ => Err(InterpreterError::UnrecognisedCommand(command.to_string())),
                }
            }
            _ => Ok(InteractiveCommand::Code(input)),
        }
    }
}
