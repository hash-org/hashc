mod pest_parser;

extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;
use crate::pest_parser::{HashParser, Rule};
use clap::{crate_version, AppSettings, Clap};

/// This doc string acts as a help message when the user runs '--help'
/// as do all doc strings on fields
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

    // parse some shit
    // let result = HashParser::parse(Rule::statement, "struct Dog /* cats are cooler */ = {hair:str, age:int, paw_size:float};");
    // let result = HashParser::parse(Rule::statement, "enum Dogs /* cats are cooler */ = {Puppy,  Woofster(str), Michael(int, str)};");
    // let result = HashParser::parse(Rule::type_t, "(int, str) => bool");
    // let result = HashParser::parse(Rule::statement, "trait str = <Y> => (Y) => bool;").unwrap_or_else(|e| panic!("{}", e));
    let result = HashParser::parse(Rule::statement, "let _if = 2;").unwrap_or_else(|e| panic!("{}", e));
    println!("{:?}", result);

}
