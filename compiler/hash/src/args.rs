//! Hash Compiler arguments management.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use clap::Parser as ClapParser;

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
#[clap(disable_colored_help = true)]
pub(crate) struct CompilerOptions {
    /// Execute the passed script directly without launching interactive mode
    #[clap(short, long)]
    pub(crate) filename: Option<String>,

    /// Run the compiler in debug mode
    #[clap(short, long)]
    pub(crate) debug: bool,

    /// Set the maximum stack size for the current running instance.
    #[clap(short, long, default_value = "10000")]
    pub(crate) stack_size: usize,

    /// Number of worker threads the compiler should use
    #[clap(short, long, default_value = Box::leak(num_cpus::get().to_string().into_boxed_str()))]
    pub(crate) worker_count: usize,

    /// Compiler mode
    #[clap(subcommand)]
    pub(crate) mode: Option<SubCmd>,
}

#[derive(ClapParser)]
pub(crate) enum SubCmd {
    AstGen(AstGenMode),
    IrGen(IrGenMode),
    Check(CheckMode),
}

/// Generate AST from given input file
#[derive(ClapParser)]
pub(crate) struct AstGenMode {
    /// Input filename of the module
    #[clap(required = true)]
    pub(crate) filename: String,
}
/// Generate IR from the given input file
#[derive(ClapParser)]
pub(crate) struct IrGenMode {
    /// Input filename of the module
    #[clap(required = true)]
    pub(crate) filename: String,
}

/// Typecheck the provided module
#[derive(ClapParser)]
pub(crate) struct CheckMode {
    /// Input filename of the module
    #[clap(required = true)]
    pub(crate) filename: String,
}
