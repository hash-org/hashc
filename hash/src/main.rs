//! Main module.
//
// All rights reserved 2021 (c) The Hash Language authors
mod error;
mod path;
mod interactive;

use clap::{crate_version, AppSettings, Clap};
use hash_parser::parse;

use std::{fs, process::exit};

use crate::{error::{report_error, ErrorType}};

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
    
    match opts.execute {
        Some(path) => match fs::canonicalize(&path) {
            Ok(c) => {
                // Resolve the module path
                let contents = fs::read_to_string(&c).unwrap_or_else(|e| {
                    report_error(
                        ErrorType::IoError,
                        format!("Couldn't read file '{}'\n{}", path, e),
                    );
                    exit(-1);
                });

                // parse the given module
                let _ = parse::module(&contents);
            }
            Err(e) => report_error(ErrorType::IoError, format!(" - '{}' ", e)),
        },
        None => {
            interactive::init();
        }
    }
}
