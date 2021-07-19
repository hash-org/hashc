//! Main module for Hash interactive mode.
//
// All rights reserved 2021 (c) The Hash Language authors

mod command;

use command::InteractiveCommand;
use hash_ast::ast::{AstNode, BodyBlock};
use hash_ast::count::NodeCount;
use hash_ast::module::Modules;
use hash_ast::parse::{ParParser, Parser};
use hash_pest_parser::backend::PestBackend;
use hash_reporting::errors::{CompilerError, InteractiveCommandError};

use rustyline::error::ReadlineError;
use rustyline::Editor;
use std::env;
use std::process::exit;

type CompilerResult<T> = Result<T, CompilerError>;

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
                return Err(InteractiveCommandError::InternalError(format!(
                    "Unexpected error: {}",
                    err
                ))
                .into());
            }
        }
    }

    Ok(())
}

fn parse_interactive(expr: &str) -> Option<(AstNode<BodyBlock>, Modules)> {
    // setup the parser
    let parser = ParParser::new(PestBackend);
    let directory = env::current_dir().unwrap();

    // parse the input
    match parser.parse_interactive(expr, &directory) {
        Ok(result) => Some(result),
        Err(e) => {
            CompilerError::from(e).report();
            None
        }
    }
}

/// Function to process a single line of input from the REPL instance.
fn execute(input: &str) {
    if input.is_empty() {
        return;
    }

    let command = InteractiveCommand::from(input);

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
            if parse_interactive(expr).is_some() {
                println!("running code...");
                // Typecheck and execute...
            }
        }
        Ok(InteractiveCommand::Type(expr)) => {
            if let Some((block, _)) = parse_interactive(expr) {
                println!("typeof({:#?})", block);
            }
        }
        Ok(InteractiveCommand::Display(expr)) => {
            if let Some((block, _)) = parse_interactive(expr) {
                println!("{}", block);
            }
        }
        Ok(InteractiveCommand::Count(expr)) => {
            if let Some((block, _)) = parse_interactive(expr) {
                println!("{} nodes", block.node_count());
            }
        }
        Err(e) => CompilerError::from(e).report(),
    }
}
