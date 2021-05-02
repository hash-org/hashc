//! Main module for Hash interactive mode.
//
// All rights reserved 2021 (c) The Hash Language authors

mod command;
mod error;

use std::{
    io::{self, Write},
    process::exit,
};

use hash_parser::parse;

use command::InteractiveCommand;

/// Interactive backend version
const VERSION: &'static str = env!("CARGO_PKG_VERSION");

/// Utility to print the version of the current interactive backend
#[inline(always)]
pub fn print_version() {
    println!("Version {}", VERSION);
}

pub fn start_interactive() -> ! {
    // firstly setup the vm here and any prior resources that are need to start the pipeline
    // ...

    // Display the version on start-up
    print_version();

    // Now just loop and try to fullfill the interactive pipeline
    loop {
        let input: String = get_input(">>> ");

        if input.len() == 0 {
            continue;
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
            continue;
        } else if input.starts_with(":") {
            // now let's get the right error reporting here
            InteractiveCommand::report_error(&input);
            continue;
        }

        // parse the input
        let _ = parse::statement(&input);

        // Typecheck and execute...
    }
}

/// Function to get a line from the console
pub fn get_input(prompt: &str) -> String {
    print!("{}", prompt);
    let _ = io::stdout().flush();

    let mut input = String::new();

    match io::stdin().read_line(&mut input) {
        Ok(_goes_into_input_above) => {}
        Err(_no_updates_is_fine) => {}
    }
    input.trim().to_string()
}
