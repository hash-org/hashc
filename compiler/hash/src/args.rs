//! Hash Compiler arguments management.

use clap::Parser as ClapParser;
use hash_pipeline::settings::{CompilerMode, CompilerSettings};

/// CompilerOptions is a structural representation of what arguments the
/// compiler can take when running. Compiler options are well documented on the
/// wiki page: <https://hash-org.github.io/hash-arxiv/interpreter-options.html>
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

    /// Whether to dump the generated ast
    #[clap(long)]
    pub(crate) dump_ast: bool,

    /// Whether to output the result of each compiler stage. This flag
    /// supersedes `--dump-ast` when they are both enabled.
    #[clap(long)]
    pub(crate) output_stage_results: bool,

    /// Whether to print the stage metrics for each stage of the compiler.
    #[clap(long)]
    pub(crate) output_metrics: bool,

    /// Number of worker threads the compiler should use
    #[clap(short, long, default_value = Box::leak(num_cpus::get().to_string().into_boxed_str()))]
    pub(crate) worker_count: usize,

    /// Compiler mode
    #[clap(subcommand)]
    pub(crate) mode: Option<SubCmd>,
}

impl From<CompilerOptions> for CompilerSettings {
    fn from(options: CompilerOptions) -> Self {
        let stage = match options.mode {
            Some(SubCmd::AstGen { .. }) => CompilerMode::Parse,
            Some(SubCmd::DeSugar { .. }) => CompilerMode::DeSugar,

            Some(SubCmd::Check { .. }) => CompilerMode::Typecheck,
            Some(SubCmd::IrGen { .. }) => CompilerMode::IrGen,
            _ => CompilerMode::Full,
        };

        Self {
            output_stage_results: options.output_stage_results,
            output_metrics: options.output_metrics,
            worker_count: options.worker_count,
            skip_prelude: false,
            emit_errors: false,
            dump_ast: options.dump_ast,
            stage,
        }
    }
}

#[derive(ClapParser, Clone)]
pub(crate) enum SubCmd {
    AstGen(AstGenMode),
    DeSugar(DeSugarMode),
    Check(CheckMode),
    IrGen(IrGenMode),
}

/// Desugar from given input file
#[derive(ClapParser, Clone)]
pub(crate) struct DeSugarMode {
    /// Input filename of the module
    #[clap(required = true)]
    pub(crate) filename: String,
}

/// Generate AST from given input file
#[derive(ClapParser, Clone)]
pub(crate) struct AstGenMode {
    /// Input filename of the module
    #[clap(required = true)]
    pub(crate) filename: String,
}

/// Generate IR from the given input file
#[derive(ClapParser, Clone)]
pub(crate) struct IrGenMode {
    /// Input filename of the module
    #[clap(required = true)]
    pub(crate) filename: String,
}

/// Typecheck the provided module
#[derive(ClapParser, Clone)]
pub(crate) struct CheckMode {
    /// Input filename of the module
    #[clap(required = true)]
    pub(crate) filename: String,
}
