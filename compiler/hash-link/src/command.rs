//! This file defines a wrapper around [std::process::Command] in order to add
//! additional functionality and to build up a command for the linker to invoke.
//! Additionally, this file defines some utilities for "escaping" the output
//! command in the event that the command has to be written to a file on
//! Windows, which needs to be escaped for MSVC to be able to parse it.

use core::fmt;
use std::{
    ffi::{OsStr, OsString},
    io, mem,
    process::{Command, Output},
};

use hash_target::{Platform, link::LldFlavour};

/// Defines what kind of program is being used to invoke the linker. For
/// [`LinkProgram::Normal`] this is just a path to the program that should
/// be run. For [`LinkProgram::Lld`] this is the path to the Lld executable
/// and the flavour of Lld that should be used.
#[derive(Clone, Debug)]
pub enum LinkProgram {
    /// Just a path to the program that should run.
    Normal(OsString),

    /// Lld has many "variants" of the same command, so we
    /// keep the path to Lld, and then the suffix that should
    /// be added to the specific Lld version.
    Lld(OsString, LldFlavour),
}

/// A wrapper around the [Command] type which allows us to
/// build up a command and read the arguments that are being
/// passed without having to go through the [Command].
#[derive(Clone, Debug)]
pub struct LinkCommand {
    /// The path to the command executable.
    command: LinkProgram,

    /// All of the arguments that should be passed to the command.
    args: Vec<OsString>,

    /// Any environment variables that should be set when running the command.
    env: Vec<(OsString, OsString)>,

    /// Any environment variables that need to be removed when running the
    /// command.
    omit_from_env: Vec<OsString>,
}

impl LinkCommand {
    /// Create a new [LinkCommand] which reference a link program
    /// that is specified by [`LinkProgram::Normal`].
    pub fn new(path: impl AsRef<OsStr>) -> Self {
        Self {
            command: LinkProgram::Normal(path.as_ref().to_owned()),
            args: Vec::new(),
            env: Vec::new(),
            omit_from_env: Vec::new(),
        }
    }

    /// Create a new [LinkCommand] that refers to a the `Lld` linker
    /// with a specific [LldFlavour].
    pub fn lld(path: impl AsRef<OsStr>, flavour: LldFlavour) -> Self {
        Self {
            command: LinkProgram::Lld(path.as_ref().to_owned(), flavour),
            args: Vec::new(),
            env: Vec::new(),
            omit_from_env: Vec::new(),
        }
    }

    /// Add an argument to the command.
    pub fn arg(&mut self, arg: impl AsRef<OsStr>) -> &mut Self {
        self.args.push(arg.as_ref().to_owned());
        self
    }

    /// Add a collection of arguments to the command.
    pub fn args(&mut self, args: impl IntoIterator<Item = impl AsRef<OsStr>>) -> &mut Self {
        self.args.extend(args.into_iter().map(|arg| arg.as_ref().to_owned()));
        self
    }

    /// Get the arguments that have been added to the command whilst
    /// also removing all of the arguments from the [LinkCommand].
    pub fn take_args(&mut self) -> Vec<OsString> {
        mem::take(&mut self.args)
    }

    /// Add an environment variable to the command.
    pub fn env(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) -> &mut Self {
        self.env.push((key.as_ref().to_owned(), value.as_ref().to_owned()));
        self
    }

    /// Remove an environment variable from the command.
    pub fn env_remove(&mut self, key: impl AsRef<OsStr>) -> &mut Self {
        self.omit_from_env.push(key.as_ref().to_owned());
        self
    }

    /// Convert the [LinkCommand] into a [`std::process::Command`].
    pub fn command(&self) -> Command {
        let mut cmd = match &self.command {
            LinkProgram::Normal(path) => Command::new(path),
            LinkProgram::Lld(path, flavour) => {
                let mut cmd = Command::new(path);
                cmd.arg("-flavor").arg(flavour.as_str());
                cmd
            }
        };

        // Add all of the arguments and the specified command-line
        // arguments.
        cmd.args(&self.args);
        cmd.envs(self.env.clone());

        // Remove all of the specified items from the command environment.
        for item in &self.omit_from_env {
            cmd.env_remove(item);
        }

        cmd
    }

    /// Produce the [Output] from the command.
    pub fn output(&mut self) -> io::Result<Output> {
        self.command().output()
    }

    /// This function is used to check whether the given command will
    /// potentially exceed the command spawn limit. If te command will likely
    /// exceed the spawn limit, then this function will return `true`, `false`
    /// otherwise.
    pub(crate) fn might_exceed_process_spawn_limit(&self) -> bool {
        if cfg!(unix) {
            return false;
        }

        // Lld doesn't support passing in the arguments via file anyway.
        if let LinkProgram::Lld(..) = self.command {
            return false;
        }

        // On `cmd.exe` then maximum buffer size is 8192 bytes anyway as documented on
        // `https://devblogs.microsoft.com/oldnewthing/?p=41553`, so we create a estimate
        // on what the true length of the command will be by measuring the length of the
        // arguments (assuming no escaping is required). This will only give us a
        // estimate of what the true size is, therefore we will use 6k as the
        // threshold for writing the link arguments to a file.
        const MAX_BUFFER_LIMIT: usize = 6 * 1024;

        let estimated_length = self.args.iter().map(|arg| arg.len()).sum::<usize>();
        estimated_length > MAX_BUFFER_LIMIT
    }
}

impl std::fmt::Display for LinkCommand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let command = self.command();

        // @@Todo: some kind of nice format here?
        write!(f, "{command:?}")
    }
}

/// This is an auxiliary struct that can be used to "escape" an argument
/// to the linker.
pub struct EscapeArg<'a> {
    /// The argument that is to be escaped.
    pub argument: &'a str,

    /// The host platform.
    pub platform: Platform,
}

impl fmt::Display for EscapeArg<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.platform.is_windows() {
            // As usual, this is not documented by Microsoft except that
            // you can pass in a file with arguments...
            write!(f, "\"")?;
            for c in self.argument.chars() {
                match c {
                    '"' => write!(f, "\\{c}")?,
                    c => write!(f, "{c}")?,
                }
            }

            write!(f, "\"")?;
        } else {
            // This is documented at <https://linux.die.net/man/1/ld>
            //
            // > Options in file are separated by whitespace. A whitespace
            // > character may be included in an option by surrounding the entire
            // > option in either single or double quotes. Any character
            // > (including a backslash) may be included by prefixing the
            // > character to be included with a backslash. The file may itself
            // > contain additional @file options; any such options will be
            // > processed recursively.
            for c in self.argument.chars() {
                match c {
                    ' ' | '\\' => write!(f, "\\{c}")?,
                    c => write!(f, "{c}")?,
                }
            }
        }

        Ok(())
    }
}
