mod pest_parser;

extern crate pest;
#[macro_use]
extern crate pest_derive;

use crate::pest_parser::{HashParser, Rule};
use clap::{crate_version, AppSettings, Clap};
use pest::Parser;

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
}

fn main() {
    let opts: CompilerOptions = CompilerOptions::parse();
    println!("Stack_size is {}", opts.stack_size);

    for path in opts.includes.into_iter() {
        println!("Running with {}", path);
    }

    match opts.execute {
        Some(path) => println!("Are we executing -> {}", path),
        None => println!("Running withing interactive mode!"),
    }

    let result =
        HashParser::parse(Rule::statement, "let s = -2;").unwrap_or_else(|e| panic!("{}", e));
    println!("{:?}", result);
}
