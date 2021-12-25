//! Main module for Hash interactive mode.
//
// All rights reserved 2021 (c) The Hash Language authors

mod command;

use command::InteractiveCommand;
use hash_alloc::Castle;
use hash_ast::ast::{AstNode, BodyBlock};
use hash_ast::count::NodeCount;
use hash_ast::module::Modules;
use hash_ast::parse::{ParParser, Parser};
use hash_reporting::errors::{CompilerError, InteractiveCommandError};
use hash_reporting::reporting::{Report, ReportWriter};

#[cfg(feature = "use-pest")]
use hash_pest_parser::backend::HashPestParser;

#[cfg(not(feature = "use-pest"))]
use hash_parser::backend::HashParser;

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

fn parse_interactive<'c>(
    expr: &str,
    castle: &'c Castle,
) -> Option<(AstNode<'c, BodyBlock<'c>>, Modules<'c>)> {
    let directory = env::current_dir().unwrap();

    // setup the parser
    let parser = ParParser::new(HashParser::new(castle), false);

    // parse the input
    match parser.parse_interactive(expr, &directory) {
        (Ok(result), modules) => Some((result, modules)),
        (Err(errors), modules) => {
            for report in errors.into_iter().map(Report::from) {
                let report_writer = ReportWriter::new(report, &modules);
                println!("{}", report_writer);
            }
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

    let castle = Castle::new();

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
            match parse_interactive(expr, &castle) {
                Some((block, modules)) => {
                    let wall = castle.wall();
                    let ctx = TypecheckCtx {
                        types: Types::new(),
                        type_defs: TypeDefs::new(),
                        type_vars: TypeVars::new(),
                        traits: Traits::new(),
                        state: TypecheckState::default(),
                        scopes: ScopeStack::new(),
                        modules: &modules,
                    };

                    let mut traverser = Traverser::new(ctx, wall);

                    match traverser.traverse_body_block(block.ast_ref()) {
                        Ok(block_ty) => {
                            let (ctx, _) = traverser.into_inner();
                            println!("{}", TypeWithCtx::new(block_ty, &ctx));
                        }
                        Err(err) => println!("Error: {:?}", err)
                    }

                }
                None => {},
            }
        }
        Ok(InteractiveCommand::Type(expr)) => {
            if let Some((block, _)) = parse_interactive(expr, &castle) {
                println!("typeof({:#?})", block);
            }
        }
        Ok(InteractiveCommand::Display(expr)) => {
            if let Some((block, _)) = parse_interactive(expr, &castle) {
                println!("{}", block);
            }
        }
        Ok(InteractiveCommand::Count(expr)) => {
            if let Some((block, _)) = parse_interactive(expr, &castle) {
                println!("{} nodes", block.node_count());
            }
        }
        Err(e) => CompilerError::from(e).report(),
    }
}
