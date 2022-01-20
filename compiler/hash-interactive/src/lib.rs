//! Main module for Hash interactive mode.
//
// All rights reserved 2022 (c) The Hash Language authors

mod command;

use command::InteractiveCommand;
use hash_ast::{tree::AstTreeGenerator, visitor::AstVisitor};
use hash_pipeline::{sources::InteractiveBlock, Checker, Compiler, CompilerState, Parser};
use hash_reporting::errors::{CompilerError, InteractiveCommandError};
use hash_reporting::reporting::ReportWriter;
use hash_source::SourceId;
use hash_utils::tree_writing::TreeWriter;
use rustyline::{error::ReadlineError, Editor};
use std::env;
use std::process::exit;

type CompilerResult<T> = Result<T, CompilerError>;

/// Interactive backend version
pub const VERSION: &str = env!("EXECUTABLE_VERSION");

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
pub fn init<'c, P, C>(mut compiler: Compiler<P, C>) -> CompilerResult<()>
where
    P: Parser<'c>,
    C: Checker<'c>,
{
    // Display the version on start-up
    print_version();

    let mut rl = Editor::<()>::new();
    let mut compiler_state = compiler.create_state().unwrap();

    loop {
        let line = rl.readline(">>> ");

        match line {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                compiler_state = execute(line.as_str(), &mut compiler, compiler_state);
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

/// Function to process a single line of input from the REPL instance.
fn execute<'c, P, C>(
    input: &str,
    compiler: &mut Compiler<P, C>,
    mut compiler_state: CompilerState<'c, C>,
) -> CompilerState<'c, C>
where
    P: Parser<'c>,
    C: Checker<'c>,
{
    if input.is_empty() {
        return compiler_state;
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
        Ok(InteractiveCommand::Type(expr)) => {
            let new_interactive_block = InteractiveBlock::new(expr.to_string());
            let interactive_id = compiler_state
                .sources
                .add_interactive_block(new_interactive_block);

            let (result, new_state) =
                compiler.run_interactive_and_return_type(interactive_id, compiler_state);

            match result {
                Ok(value) => {
                    println!("= {value}");
                }
                Err(err) => {
                    println!("{}", ReportWriter::new(err, &new_state.sources));
                }
            }
            return new_state;
        }
        Ok(InteractiveCommand::Display(expr)) => {
            let new_interactive_block = InteractiveBlock::new(expr.to_string());
            let interactive_id = compiler_state
                .sources
                .add_interactive_block(new_interactive_block);

            let result = compiler.parse_source(
                SourceId::Interactive(interactive_id),
                &mut compiler_state.sources,
            );

            match result {
                Ok(()) => {
                    let block = compiler_state.sources.get_interactive_block(interactive_id);
                    let tree = AstTreeGenerator
                        .visit_body_block(&(), block.node())
                        .unwrap();

                    println!("{}", TreeWriter::new(&tree));
                }
                Err(err) => {
                    println!("{}", ReportWriter::new(err, &compiler_state.sources));
                }
            }
        }
        Ok(InteractiveCommand::Code(expr)) => {
            let new_interactive_block = InteractiveBlock::new(expr.to_string());
            let interactive_id = compiler_state
                .sources
                .add_interactive_block(new_interactive_block);

            let (result, new_state) = compiler.run_interactive(interactive_id, compiler_state);

            match result {
                Ok(()) => {}
                Err(err) => {
                    println!("{}", ReportWriter::new(err, &new_state.sources));
                }
            }
            return new_state;
        }
        Err(e) => CompilerError::from(e).report(),
    }

    compiler_state
}
