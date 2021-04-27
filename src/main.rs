mod ast;
mod modules;
// mod typecheck;

use clap::{AppSettings, Clap, crate_version};

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
    #[clap(short, long, multiple_values=true)]
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
}
