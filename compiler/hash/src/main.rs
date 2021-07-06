//! Main module.
//
// All rights reserved 2021 (c) The Hash Language authors

use backtrace::Backtrace;
use clap::{crate_version, AppSettings, Clap};
use hash_ast::parse::{Parser, SeqParser};
use hash_interactive::init;
use hash_pest_parser::grammar::HashGrammar;
use hash_reporting::errors::CompilerError;
use log::log_enabled;
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
    ///  Include a directory into runtime. The current directory is included by default
    #[clap(short, long, multiple_values = true)]
    includes: Vec<String>,

    /// Execute the passed script directly without launching interactive mode
    #[clap(short, long)]
    execute: Option<String>,

    /// Set the maximum stack size for the current running instance.
    #[clap(short, long, default_value = "10000")]
    stack_size: u32,

    /// Run the compiler in debug mode
    #[clap(short, long)]
    debug: bool,

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

fn main() {
    // Setup our panic handler
    panic::set_hook(Box::new(panic_handler));

    fn execute(f: impl FnOnce() -> Result<(), CompilerError>) {
        match f() {
            Ok(()) => (),
            Err(e) => e.report_and_exit(),
        }
    }

    execute(|| {
        pretty_env_logger::init();

        let opts: CompilerOptions = CompilerOptions::parse();

        // print recieved cmdargs, if debug is specified
        if opts.debug {
            println!("Stack_size is {}", opts.stack_size);

            for path in opts.includes.iter() {
                println!("Running with {}", path);
            }
        }
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
                let parser = SeqParser::new(HashGrammar);
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
                init()?;
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
