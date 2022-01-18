//! Main module.
//
// All rights reserved 2021 (c) The Hash Language authors

#![feature(panic_info_message)]

mod crash_handler;
mod logger;

use clap::{AppSettings, Parser as ClapParser};
use hash_alloc::Castle;
use hash_parser::parser::HashParser;
use hash_pipeline::{fs::resolve_path, Compiler, Module};
use hash_reporting::{errors::CompilerError, reporting::ReportWriter};
use hash_typecheck::HashTypechecker;
use hash_utils::timed;
use log::LevelFilter;
use logger::CompilerLogger;
use std::num::NonZeroUsize;
use std::panic;
use std::{env, fs};

use crate::crash_handler::panic_handler;

/// CompilerOptions is a structural representation of what arguments the compiler
/// can take when running. Compiler options are well documented on the wiki page:
/// <https://hash-org.github.io/hash-arxiv/interpreter-options.html>
#[derive(ClapParser)]
#[clap(
    name = "Hash Interpreter",
    version,
    author = "Hash Language Authors",
    about = "Run and execute hash programs"
)]
#[clap(setting = AppSettings::DisableColoredHelp)]
struct CompilerOptions {
    //  Include a directory into runtime. The current directory is included by default
    // #[clap(short, long, multiple_values = true)]
    // includes: Vec<String>,
    /// Execute the passed script directly without launching interactive mode
    #[clap(short, long)]
    execute: Option<String>,

    // Set the maximum stack size for the current running instance.
    // #[clap(short, long, default_value = "10000")]
    // stack_size: u32,
    /// Run the compiler in debug mode
    #[clap(short, long)]
    debug: bool,

    /// Number of worker threads the compiler should use
    #[clap(short, long, default_value = Box::leak(num_cpus::get().to_string().into_boxed_str()))]
    worker_count: usize,

    /// Compiler mode
    #[clap(subcommand)]
    mode: Option<SubCmd>,
}

#[derive(ClapParser)]
enum SubCmd {
    AstGen(AstGen),
    IrGen(IrGen),
}

/// Generate AST from given input file
#[derive(ClapParser)]
struct AstGen {
    /// Input file to generate AST from
    #[clap(required = true)]
    filename: String,

    /// Visualise the generated AST
    #[clap(short, long)]
    visualise: bool,

    /// Run the AST generation in debug mode
    #[clap(short, long)]
    debug: bool,
}
/// Generate IR from the given input file
#[derive(ClapParser)]
struct IrGen {
    /// Input file to generate IR from
    #[clap(required = true)]
    filename: String,

    /// Visualise the generated IR
    #[clap(short, long)]
    _visualise: bool,

    /// Run the IR generation in debug mode
    #[clap(short, long)]
    debug: bool,
}

pub static CONSOLE_LOGGER: CompilerLogger = CompilerLogger;

fn execute(f: impl FnOnce() -> Result<(), CompilerError>) {
    match f() {
        Ok(()) => (),
        Err(e) => e.report_and_exit(),
    }
}

fn main() {
    // Initial grunt work, panic handler and logger setup...
    panic::set_hook(Box::new(panic_handler));
    log::set_logger(&CONSOLE_LOGGER).unwrap_or_else(|_| panic!("Couldn't initiate logger"));

    let opts: CompilerOptions = CompilerOptions::parse();

    // if debug is specified, we want to log everything that is debug level...
    if opts.debug {
        log::set_max_level(LevelFilter::Debug);
    }

    // check that the job count is valid...
    let worker_count = NonZeroUsize::new(opts.worker_count)
        .unwrap_or_else(|| {
            (CompilerError::ArgumentError {
                message: "Invalid number of worker threads".to_owned(),
            })
            .report_and_exit()
        })
        .into();

    // Create a castle for allocations in the pipeline
    let castle = Castle::new();

    let parser = HashParser::new(worker_count, &castle);
    let tc_wall = &castle.wall();
    let checker = HashTypechecker::new(tc_wall);
    let mut compiler = Compiler::new(parser, checker);
    let mut compiler_state = compiler.create_state().unwrap();

    execute(|| {
        match opts.execute {
            Some(path) => {
                let current_dir = env::current_dir()?;
                let filename = resolve_path(fs::canonicalize(&path)?, current_dir, None);

                if let Err(err) = filename {
                    println!(
                        "{}",
                        ReportWriter::new(err.create_report(), &compiler_state.sources)
                    );
                    return Ok(());
                };

                let module = Module::new(filename.unwrap());
                let module_id = compiler_state.sources.add_module(module);

                // Wrap the compilation job in timed to time the total time taken to run the job
                timed(
                    || {
                        let (result, new_state) = compiler.run_module(module_id, compiler_state);

                        // Report the error if one occurred...
                        if let Err(err) = result {
                            println!("{}", ReportWriter::new(err, &new_state.sources));
                        }
                    },
                    log::Level::Debug,
                    |elapsed| println!("total: {:?}", elapsed),
                );

                Ok(())
            }
            None => {
                hash_interactive::init(compiler)?;
                Ok(())
            }
        }
    })
}
