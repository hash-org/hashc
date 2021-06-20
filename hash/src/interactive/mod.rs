//! Main module for Hash interactive mode.
//
// All rights reserved 2021 (c) The Hash Language authors

mod command;
pub(crate) mod error;

use bumpalo::Bump;
use command::InteractiveCommand;
use error::InterpreterError;
use hash_ast::count::NodeCount;
use hash_ast::parse::Parser;
use hash_pest_parser::grammar::HashGrammar;
use rustyline::error::ReadlineError;
use rustyline::Editor;
use std::env;
use std::process::exit;

use crate::error::CompilerError;
use crate::error::CompilerResult;

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
pub fn init() -> CompilerResult<()> {
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
                return Err(
                    InterpreterError::InternalError(format!("Unexpected error: {}", err)).into(),
                );
            }
        }
    }

    Ok(())
}

/// Function to process a single line of input from the REPL instance.
fn execute(input: &str) {
    if input.is_empty() {
        return;
    }

    let command = InteractiveCommand::from(&input);

    let allocator = Bump::new();
    // setup the parser
    let parser = Parser::sequential(HashGrammar, &allocator);

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
            let directory = env::current_dir().unwrap();
            let statement = parser.parse_statement(&expr, &directory);
            // println!("{:#?}", statement);

            if let Ok(st) = statement {
                let modules = st.get_modules();

                let node_count: usize = modules
                    .iter()
                    .map(|m| {
                        let mod_node_count: usize = m.contents.iter().map(|s| s.node_count()).sum();
                        mod_node_count
                    })
                    .sum();

                println!("node_count={}", node_count);
            }

            // Typecheck and execute...
        }
        Ok(InteractiveCommand::Type(expr)) => println!("typeof({})", expr),
        Err(e) => CompilerError::from(e).report(),
    }
}
