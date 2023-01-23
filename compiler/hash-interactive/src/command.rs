//! Hash interactive mode commands.

use crate::error::{InteractiveError, InteractiveResult};

/// Enum representing the variants of command that can be executed in the
/// interactive mode.
///
/// N.B. The [`InteractiveCommand::Code`] variant is used to represent a string
/// that is not a command. This is used to execute statements in the interactive
/// mode.
#[derive(Debug, Clone)]
pub enum InteractiveCommand<'i> {
    /// Quit the current interactive session
    Quit,

    /// Clear the console
    Clear,

    /// Get the type of the expression
    Type(&'i str),

    /// Display the node tree of the expression
    Display(&'i str),

    /// Just prints the version of the current interactive mode
    Version,

    /// A string representing a statement that will be executed
    Code(&'i str),
}

struct CommandDelegator<'i> {
    /// The command to execute.
    command: &'i str,

    /// The code argument to the command.
    arg: &'i str,
}

impl<'i> CommandDelegator<'i> {
    fn new(command: &'i str, arg: &'i str) -> Self {
        Self { command, arg }
    }

    /// Delegate the command with a specified argument. If the argument
    /// is an empty string, this is considered to be an error.
    fn with_arg(
        &self,
        f: impl FnOnce(&'i str) -> InteractiveResult<InteractiveCommand<'i>>,
    ) -> InteractiveResult<InteractiveCommand<'i>> {
        match self.arg {
            "" => Err(InteractiveError::MissingOperand(self.command.to_string())),
            arg => f(arg),
        }
    }

    /// Delegate the command without a specified argument. If the argument
    /// is not an empty string, this is considered to be an error.
    fn without_arg(
        &self,
        command: InteractiveCommand<'i>,
    ) -> InteractiveResult<InteractiveCommand<'i>> {
        match self.arg {
            "" => Ok(command),
            _ => Err(InteractiveError::UnexpectedArgument(self.command.to_string())),
        }
    }
}

impl<'a> TryFrom<&'a str> for InteractiveCommand<'a> {
    type Error = InteractiveError;

    fn try_from(input: &'a str) -> Result<Self, Self::Error> {
        if !input.starts_with(':') {
            return Ok(InteractiveCommand::Code(input));
        }

        // get the index of the first white space character
        let index = input.trim_start().find(char::is_whitespace).unwrap_or(input.len());
        let (command, rest) = input.split_at(index);

        let d = CommandDelegator::new(command, rest);
        match command {
            ":q" => d.without_arg(InteractiveCommand::Quit),
            ":c" | ":cls" | ":clear" => d.without_arg(InteractiveCommand::Clear),
            ":v" => d.without_arg(InteractiveCommand::Version),
            ":t" => d.with_arg(|arg| Ok(InteractiveCommand::Type(arg))),
            ":d" => d.with_arg(|arg| Ok(InteractiveCommand::Display(arg))),
            _ => Err(InteractiveError::UnrecognisedCommand(command.to_string())),
        }
    }
}
