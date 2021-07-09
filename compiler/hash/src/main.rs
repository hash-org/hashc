//! Main module.
//
// All rights reserved 2021 (c) The Hash Language authors

mod logger;

use backtrace::Backtrace;
use clap::{crate_version, AppSettings, Clap};
use hash_ast::parse::{ParParser, Parser};
use hash_pest_parser::grammar::HashGrammar;
use hash_reporting::errors::CompilerError;
use log::{log_enabled, LevelFilter};
use logger::CompilerLogger;
use std::panic;
use std::{
    env, fs,
    panic::PanicInfo,
    time::{Duration, Instant},
};

/// CompilerOptions is a structural representation of what arguments the compiler
/// can take when running. Compiler options are well documented on the wiki page:
/// https://hash-org.github.io/hash-arxiv/interpreter-options.html
#[derive(Clap)]
#[clap(
    name = "Hash Interpreter",
    version = crate_version!(),
    author = "Hash Language Authors",
    about = "Run and execute hash programs"
)]
#[clap(setting = AppSettings::ColorNever)]
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

#[derive(Clap)]
enum SubCmd {
    AstGen(AstGen),
    IrGen(IrGen),
}

/// Generate AST from given input file
#[derive(Clap)]
struct AstGen {
    /// Input file to generate AST from
    #[clap(required = true)]
    filename: String,

    /// Run the AST generation in debug mode
    #[clap(short, long)]
    debug: bool,
}
/// Generate IR from the given input file
#[derive(Clap)]
struct IrGen {
    /// Input file to generate IR from
    #[clap(required = true)]
    filename: String,

    /// Run the IR generation in debug mode
    #[clap(short, long)]
    debug: bool,
}

pub static CONSOLE_LOGGER: CompilerLogger = CompilerLogger;

fn panic_handler(info: &PanicInfo) {
    if let Some(s) = info.payload().downcast_ref::<&str>() {
        println!("Sorry :^(\nInternal Panic: {}\n", s);
    } else {
        println!("Sorry :^(\nInternal Panic\n");
    }

    // Display the location if we can...
    if let Some(location) = info.location() {
        println!(
            "Occurred in file '{}' at {}:{}",
            location.file(),
            location.line(),
            location.column()
        );
    }

    // print the backtrace
    println!("Backtrace:\n{:?}", Backtrace::new());

    let msg = "This is an interpreter bug, please file a bug report at";
    let uri = "https://github.com/hash-org/lang/issues";

    println!("{}\n\n{:^len$}\n", msg, uri, len = msg.len());
}

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

    execute(|| {
        // check here if we are operating in a special mode...
        if let Some(mode) = opts.mode {
            match mode {
                SubCmd::AstGen(a) => {
                    println!("Generating ast for: {} with debug={}", a.filename, a.debug)
                }
                SubCmd::IrGen(i) => {
                    println!("Generating ir for: {} with debug={}", i.filename, i.debug)
                }
            }

            return Ok(());
        }

        match opts.execute {
            Some(path) => {
                let filename = fs::canonicalize(&path)?;
                let parser = ParParser::new_with_workers(HashGrammar, opts.worker_count);
                let directory = env::current_dir().unwrap();

                let result = timed(
                    || parser.parse(&filename, &directory),
                    log::Level::Debug,
                    |elapsed| println!("total: {:?}", elapsed),
                );

                if let Err(e) = result {
                    CompilerError::from(e).report_and_exit();
                }

                Ok(())
            }
            None => {
                hash_interactive::init()?;
                Ok(())
            }
        }
    })
}

#[inline(always)]
fn timed<T>(op: impl FnOnce() -> T, level: log::Level, on_elapsed: impl FnOnce(Duration)) -> T {
    if log_enabled!(level) {
        let begin = Instant::now();
        let result = op();
        on_elapsed(begin.elapsed());
        result
    } else {
        op()
    }
}
