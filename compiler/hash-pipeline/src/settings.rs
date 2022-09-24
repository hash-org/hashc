//! Hash Compiler pipeline implementation. This file contains various structures
//! and utilities representing settings and configurations that can be applied
//! to the Compiler pipeline.
use std::fmt::Display;

/// Various settings that are present on the compiler pipeline when initially
/// launching.
#[derive(Debug, Clone, Copy)]
pub struct CompilerSettings {
    /// Print metrics about each stage when the entire pipeline has completed.
    ///
    /// N.B: This flag has no effect if the compiler is not specified to run in
    ///       debug mode!
    pub output_metrics: bool,

    /// Whether to output of each stage result.
    pub output_stage_results: bool,

    /// The number of workers that the compiler pipeline should have access to.
    /// This value is used to determine the thread pool size that is then shared
    /// across arbitrary stages within the compiler.
    pub worker_count: usize,

    /// Whether the compiler should skip bootstrapping the prelude, this
    /// is set for testing purposes.
    pub skip_prelude: bool,

    /// Whether the pipeline should output errors and warnings to
    /// standard error
    pub emit_errors: bool,

    /// If the compiler should emit generated `ast` for all parsed modules
    ///
    /// @@Future: add the possibility of specifying which modules should be
    /// dumped, or this could be achieved with using some kind of directive to
    /// dump the ast for a particular expression.
    pub dump_ast: bool,

    /// To what should the compiler run to, anywhere from parsing, typecheck, to
    /// code generation.
    pub stage: CompilerMode,
}

impl CompilerSettings {
    pub fn new(worker_count: usize) -> Self {
        Self { worker_count, ..Default::default() }
    }

    /// Specify whether the compiler pipeline should skip running
    /// prelude during bootstrapping.
    pub fn set_skip_prelude(&mut self, value: bool) {
        self.skip_prelude = value;
    }

    /// Specify whether the compiler should emit errors to
    /// standard error, or if they should be handled by the
    /// caller.
    pub fn set_emit_errors(&mut self, value: bool) {
        self.emit_errors = value;
    }

    /// Specify the [CompilerMode] the compiler should run to.
    pub fn set_stage(&mut self, stage: CompilerMode) {
        self.stage = stage;
    }
}

impl Default for CompilerSettings {
    fn default() -> Self {
        Self {
            output_stage_results: false,
            output_metrics: false,
            worker_count: num_cpus::get(),
            skip_prelude: false,
            emit_errors: true,
            dump_ast: false,
            stage: CompilerMode::Full,
        }
    }
}

/// Enum representing what mode the compiler should run in. Specifically, if the
/// compiler should only run up to a particular stage within the pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CompilerMode {
    Parse,
    DeSugar,
    SemanticPass,
    Typecheck,
    Lower,
    IrGen,
    Full,
}

impl Default for CompilerMode {
    fn default() -> Self {
        CompilerMode::Full
    }
}

impl Display for CompilerMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompilerMode::Parse => write!(f, "parsing"),
            CompilerMode::DeSugar => write!(f, "de-sugaring"),
            CompilerMode::SemanticPass => write!(f, "semantic"),
            CompilerMode::Typecheck => write!(f, "typecheck"),
            CompilerMode::Lower => write!(f, "lowering"),
            CompilerMode::IrGen => write!(f, "ir"),
            CompilerMode::Full => write!(f, "total"),
        }
    }
}
