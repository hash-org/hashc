//! Main module.
//
// All rights reserved 2021 (c) The Hash Language authors

#![feature(panic_info_message)]

mod crash_handler;
mod logger;

use clap::{AppSettings, Parser as ClapParser};
use hash_alloc::Castle;
use hash_ast::module::Modules;
use hash_ast::parse::{ParParser, Parser, ParserBackend};
use hash_reporting::{
    errors::CompilerError,
    reporting::{Report, ReportWriter},
};
use hash_utils::timed;
use log::LevelFilter;
use logger::CompilerLogger;
use std::panic;
use std::path::PathBuf;
use std::{env, fs};
use std::{num::NonZeroUsize, process::exit};

#[cfg(not(feature = "use-pest"))]
use hash_parser::backend::HashParser;

#[cfg(feature = "use-pest")]
use hash_pest_parser::backend::PestBackend;

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

fn run_parsing<'c>(
    parser: ParParser<impl ParserBackend<'c>>,
    filename: PathBuf,
    directory: PathBuf,
) -> Modules<'c> {
    let (result, modules) = timed(
        || parser.parse(&filename, &directory),
        log::Level::Debug,
        |elapsed| println!("total: {:?}", elapsed),
    );

    match result {
        Ok(_) => modules,
        Err(errors) => {
            for report in errors.into_iter().map(Report::from) {
                let report_writer = ReportWriter::new(report, &modules);
                println!("{}", report_writer);
            }

            exit(-1)
        }
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
    let worker_count = NonZeroUsize::new(opts.worker_count).unwrap_or_else(|| {
        (CompilerError::ArgumentError {
            message: "Invalid number of worker threads".to_owned(),
        })
        .report_and_exit()
    });

    let castle = Castle::new();

    // determine the parser backend that we're using...
    #[cfg(feature = "use-pest")]
    let mut parser_backend =
        ParParser::new_with_workers(PestBackend::new(&castle), worker_count, false);

    #[cfg(not(feature = "use-pest"))]
    let mut parser_backend =
        ParParser::new_with_workers(HashParser::new(&castle), worker_count, false);

    execute(|| {
        let directory = env::current_dir().unwrap();

        // check here if we are operating in a special mode
        if let Some(mode) = opts.mode {
            let _modules = match mode {
                SubCmd::AstGen(settings) => {
                    let filename = fs::canonicalize(&settings.filename)?;

                    if settings.debug {
                        log::set_max_level(LevelFilter::Debug);
                    }

                    parser_backend.set_visualisation(settings.visualise);
                    run_parsing(parser_backend, filename, directory)
                }
                SubCmd::IrGen(i) => {
                    println!("Generating ir for: {} with debug={}", i.filename, i.debug);
                    todo!()
                }
            };

            return Ok(());
        }

        match opts.execute {
            Some(path) => {
                let filename = fs::canonicalize(&path)?;
                let _modules = run_parsing(parser_backend, filename, directory);

                Ok(())
            }
            None => {
                hash_interactive::init()?;
                Ok(())
            }
        }
    })
}
