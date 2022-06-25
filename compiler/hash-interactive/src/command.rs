//! Hash interactive mode commands.

use hash_pipeline::settings::{CompilerJobParams, CompilerMode};
use hash_reporting::errors::InteractiveCommandError;

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

impl From<&InteractiveCommand<'_>> for CompilerJobParams {
    fn from(command: &InteractiveCommand<'_>) -> Self {
        // Here, we don't care about all of the other modes except `Type` and `Display`
        // since these will either be pre-emptively handled by the REPL, or it will
        // execute the full stage.
        match command {
            InteractiveCommand::Display(_) => CompilerJobParams::new(CompilerMode::Parse, true),
            InteractiveCommand::Type(_) => CompilerJobParams::new(CompilerMode::Typecheck, true),
            _ => CompilerJobParams::default(),
        }
    }
}

struct CommandDelegator<'i> {
    command: &'i str,
    arg: &'i str,
}

impl<'i> CommandDelegator<'i> {
    fn new(command: &'i str, arg: &'i str) -> Self {
        Self { command, arg }
    }

    fn with_arg(&self, f: impl FnOnce(&'i str) -> InteractiveResult<'i>) -> InteractiveResult<'i> {
        match self.arg {
            "" => Err(InteractiveCommandError::ArgumentMismatchError(self.command.to_string())),
            arg => f(arg),
        }
    }

    fn without_arg(&self, command: InteractiveCommand<'i>) -> InteractiveResult<'i> {
        match self.arg {
            "" => Ok(command),
            _ => Err(InteractiveCommandError::ZeroArguments(self.command.to_string())),
        }
    }
}

type InteractiveResult<'i> = Result<InteractiveCommand<'i>, InteractiveCommandError>;

impl InteractiveCommand<'_> {
    /// Attempt to convert a string into an interactive command
    pub fn from(input: &str) -> InteractiveResult<'_> {
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
            _ => Err(InteractiveCommandError::UnrecognisedCommand(command.to_string())),
        }
    }
}
