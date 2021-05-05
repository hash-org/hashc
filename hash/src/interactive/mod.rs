//! Main module for Hash interactive mode.
//
// All rights reserved 2021 (c) The Hash Language authors

mod command;
mod error;

use command::InteractiveCommand;
use error::{report_interp_error, InterpreterError};
use hash_parser::parse;
use rustyline::error::ReadlineError;
use rustyline::Editor;
use std::process::exit;

/// Interactive backend version
const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Utility to print the version of the current interactive backend
#[inline(always)]
pub fn print_version() {
    println!("Version {}", VERSION);
}

/// Function that is called on a graceful interpreter exit
pub fn goodbye() {
    println!("Goodbye!");
    exit(0)
}

/// Function that initialises the interactive mode. Setup all the resources required to perform
/// execution of provided statements and then initiate the REPL.
pub fn init() {
    // Display the version on start-up
    print_version();

    let mut rl = Editor::<()>::new();

    loop {
        let line = rl.readline(">>> ");

        match line {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                execute(line.as_str());
            }
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => {
                println!("Exiting!");
                break;
            }
            Err(err) => {
                report_interp_error(InterpreterError::InternalError(format!("{:?}", err)));
                break;
            }
        }
    }
}

/// Function to process a single line of input from the REPL instance.
fn execute(input: &str) {
    if input.is_empty() {
        return;
    }

    let command = InteractiveCommand::from(&input);

    match command {
        Ok(InteractiveCommand::Quit) => goodbye(),
        Ok(InteractiveCommand::Clear) => {
            // check if this is either a unix/windows system and then execute
            // the appropriate clearing command
            if cfg!(target_os = "windows") {
                std::process::Command::new("cls").status().unwrap();
            } else {
                std::process::Command::new("clear").status().unwrap();
            }
        }
        Ok(InteractiveCommand::Version) => print_version(),
        Ok(InteractiveCommand::Code(expr)) => {
            // parse the input
            let _ = parse::statement(&expr);

            // Typecheck and execute...
        }
        Ok(InteractiveCommand::Type(expr)) => println!("typeof({})", expr),
        Err(e) => report_interp_error(e),
    }
}
