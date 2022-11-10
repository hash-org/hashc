//! Hash Compiler arguments management.

use clap::Parser as ClapParser;
use hash_pipeline::settings::{CompilerSettings, CompilerStageKind};
use hash_reporting::errors::CompilerError;
use hash_target::{Target, TargetInfo};

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

    /// The target that the compiler will emit the executable for. This
    /// will be used to determine the pointer size and other settings that
    /// are **target specific**.
    #[clap(long, default_value = std::env::consts::ARCH)]
    pub(crate) target: String,

    /// Compiler mode
    #[clap(subcommand)]
    pub(crate) mode: Option<SubCmd>,
}

impl TryInto<CompilerSettings> for CompilerOptions {
    type Error = CompilerError;

    fn try_into(self) -> Result<CompilerSettings, Self::Error> {
        let stage = match self.mode {
            Some(SubCmd::AstGen { .. }) => CompilerStageKind::Parse,
            Some(SubCmd::DeSugar { .. }) => CompilerStageKind::DeSugar,

            Some(SubCmd::Check { .. }) => CompilerStageKind::Typecheck,
            Some(SubCmd::IrGen { .. }) => CompilerStageKind::IrGen,
            _ => CompilerStageKind::Full,
        };

        let host = Target::from_string(std::env::consts::ARCH.to_string())
            .ok_or_else(|| CompilerError::InvalidTarget(std::env::consts::ARCH.to_string()))?;

        let target = Target::from_string(self.target.clone())
            .ok_or_else(|| CompilerError::InvalidTarget(self.target))?;

        let target_info = TargetInfo::new(host, target);

        Ok(CompilerSettings {
            target_info,
            output_stage_results: self.output_stage_results,
            output_metrics: self.output_metrics,
            worker_count: self.worker_count,
            skip_prelude: false,
            emit_errors: true,
            dump_ast: self.dump_ast,
            stage,
        })
    }
}

/// [SubCmd] specifies separate modes that the compiler can run in. These modes
/// are used to terminate the compiler at a particular stage of the pipeline.
#[derive(ClapParser, Clone)]
pub(crate) enum SubCmd {
    /// Parse the given program and terminate.
    AstGen(AstGenMode),
    /// Only run the compiler up until the `de-sugaring` stage.
    DeSugar(DeSugarMode),
    /// Typecheck the given module.
    Check(CheckMode),
    /// Generate the IR for the given file.
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
