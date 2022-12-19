//! Hash Compiler pipeline implementation. This file contains various structures
//! and utilities representing settings and configurations that can be applied
//! to the Compiler pipeline.
use std::fmt::Display;

use clap_derive::ValueEnum;
use hash_target::TargetInfo;

/// Various settings that are present on the compiler pipeline when initially
/// launching.
#[derive(Debug, Clone)]
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

    /// All settings that relate to the lowering stage of the compiler.
    pub lowering_settings: LoweringSettings,

    /// If the compiler should emit generated `ast` for all parsed modules
    ///
    /// @@Future: add the possibility of specifying which modules should be
    /// dumped, or this could be achieved with using some kind of directive to
    /// dump the ast for a particular expression.
    pub dump_ast: bool,

    /// To what should the compiler run to, anywhere from parsing, typecheck, to
    /// code generation.
    pub stage: CompilerStageKind,

    /// Information about the current "session" that the compiler is running
    /// in. This contains information about which target the compiler is
    /// compiling for, and other information that is used by the compiler
    /// to determine how to compile the source code.
    pub target_info: TargetInfo,
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
            target_info: TargetInfo::default(),
            output_stage_results: false,
            output_metrics: false,
            worker_count: num_cpus::get(),
            skip_prelude: false,
            emit_errors: true,
            dump_ast: false,
            stage: CompilerStageKind::Full,
            lowering_settings: LoweringSettings::default(),
        }
    }
}

/// What optimisation level the compiler should run at.
#[derive(Debug, ValueEnum, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OptimisationLevel {
    /// Run the compiler using the debug optimisation level. This will
    /// disable most optimisations that the compiler would otherwise do.
    /// This is intended for building the program as fast as possible.
    Debug,

    /// Optimise the given program as much as possible, essentially
    /// applying all optimisation.
    Release,
}

impl Default for OptimisationLevel {
    fn default() -> Self {
        Self::Debug
    }
}

/// Settings that relate to the IR stage of the compiler, these include if the
/// IR should be dumped (and in which mode), whether the IR should be optimised,
/// whether the IR should use `checked` operations, etc.
#[derive(Debug, Clone, Copy)]
pub struct LoweringSettings {
    /// The optimisation level that is to be performed.
    pub optimisation_level: OptimisationLevel,

    /// Whether the IR should dump all lowered bodies, rather than
    /// relying on user directives to select specific bodies.
    pub dump_all: bool,

    /// Whether the IR that is generated at the time should be dumped.
    pub dump_mode: IrDumpMode,

    /// Use checked operations when emitting IR, this is usually derived whether
    /// the compiler is building a debug variant or not.
    pub checked_operations: bool,
}

impl Default for LoweringSettings {
    fn default() -> Self {
        Self {
            dump_mode: IrDumpMode::Pretty,
            checked_operations: true,
            dump_all: false,
            optimisation_level: OptimisationLevel::Debug,
        }
    }
}

#[derive(ValueEnum, Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrDumpMode {
    /// Dump the generated IR using a pretty-printed format
    Pretty,

    /// Dump the generated IR using the `graphviz` format
    Graph,
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
