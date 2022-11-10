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
    ///      debug mode!
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

    /// Which target the compiler should compile for, this affects various
    /// settings within the compiler, notably the pointer size.
    pub target: CompilationTarget,

    /// To what should the compiler run to, anywhere from parsing, typecheck, to
    /// code generation.
    pub stage: CompilerStageKind,
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

    /// Specify the [CompilerStageKind] the compiler should run to.
    pub fn set_stage(&mut self, stage: CompilerStageKind) {
        self.stage = stage;
    }
}

impl Default for CompilerSettings {
    fn default() -> Self {
        Self {
            target: CompilationTarget::default(),
            output_stage_results: false,
            output_metrics: false,
            worker_count: num_cpus::get(),
            skip_prelude: false,
            emit_errors: true,
            dump_ast: false,
            stage: CompilerStageKind::Full,
        }
    }
}

/// The target that the compiler should compile for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompilationTarget {
    /// The target is a 32-bit system.
    X86,

    /// The target is a 64-bit system.
    X86_64,
}

impl Default for CompilationTarget {
    fn default() -> Self {
        match std::env::consts::ARCH {
            "x86" => Self::X86,
            "x86_64" => Self::X86_64,
            _ => panic!("Unsupported target architecture"),
        }
    }
}

impl CompilationTarget {
    /// Get the size of a pointer for the target in bytes.
    pub fn pointer_size(&self) -> usize {
        match self {
            Self::X86 => 4,
            Self::X86_64 => 8,
        }
    }
}

/// Enum representing what mode the compiler should run in. Specifically, if the
/// compiler should only run up to a particular stage within the pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CompilerStageKind {
    Parse,
    DeSugar,
    SemanticPass,
    Typecheck,
    Lower,
    IrGen,
    Full,
}

impl Default for CompilerStageKind {
    fn default() -> Self {
        CompilerStageKind::Full
    }
}

impl Display for CompilerStageKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompilerStageKind::Parse => write!(f, "parsing"),
            CompilerStageKind::DeSugar => write!(f, "de-sugaring"),
            CompilerStageKind::SemanticPass => write!(f, "semantic"),
            CompilerStageKind::Typecheck => write!(f, "typecheck"),
            CompilerStageKind::Lower => write!(f, "lowering"),
            CompilerStageKind::IrGen => write!(f, "ir"),
            CompilerStageKind::Full => write!(f, "total"),
        }
    }
}
