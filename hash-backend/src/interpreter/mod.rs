//! Main module for Hash interactive mode.
//
// All rights reserved 2021 (c) The Hash Language authors

mod command;
mod error;

use hash_parser::parse;
use rustyline::error::ReadlineError;
use rustyline::Editor;

use std::process::exit;

use command::InteractiveCommand;

/// Interactive backend version
const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Utility to print the version of the current interactive backend
#[inline(always)]
pub fn print_version() {
    println!("Version {}", VERSION);
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
            Err(ReadlineError::Interrupted) => {
                println!("^C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("^D"); // we like don't even need this event since it's interactive
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
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

    // check here if it is an 'interactive command', as in prefixed with a ':' and then some string
    if let Some(k) = InteractiveCommand::from(&input) {
        match k {
            InteractiveCommand::Quit => {
                println!("Goodbye!");
                exit(0)
            }
            InteractiveCommand::Version => print_version(),
            InteractiveCommand::Clear => {
                // check if this is either a unix/windows system and then execute
                // the appropriate clearing command
                if cfg!(target_os = "windows") {
                    std::process::Command::new("cls").status().unwrap();
                } else {
                    std::process::Command::new("clear").status().unwrap();
                }
            }
            InteractiveCommand::Type(expr) => println!("typeof({})", expr),
        }

        // skip parsing anything if it's an interactive command
        return;
    } else if input.starts_with(':') {
        // now let's get the right error reporting here
        InteractiveCommand::report_error(&input);
        return;
    }

    // parse the input
    let _ = parse::statement(&input);

    // Typecheck and execute...
}
