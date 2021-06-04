//! Main module.
//
// All rights reserved 2021 (c) The Hash Language authors
mod error;
mod interactive;

use clap::{crate_version, AppSettings, Clap};
use std::fs;

use crate::error::{report_error, ErrorType};

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

fn main() {
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

        return;
    }

    match opts.execute {
        Some(path) => match fs::canonicalize(&path) {
            Ok(filename) => {
                let parser = Parser::sequential(HashGrammar);
                let directory = env::current_dir().unwrap();
                let modules = parser.parse(&filename, &directory);
                println!("{:#?}", modules);
            }
            Err(e) => report_error(ErrorType::IoError, format!(" - '{}' ", e)),
        },
        None => {
            interactive::init();
        }
    }
}
