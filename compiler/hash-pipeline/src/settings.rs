//! Hash Compiler pipeline implementation. This file contains various structures
//! and utilities representing settings and configurations that can be applied
//! to the Compiler pipeline.
use std::fmt::Display;

use clap_derive::ValueEnum;
use hash_target::TargetInfo;

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

    /// The optimisation level that is to be performed.
    pub optimisation_level: OptimisationLevel,

    /// All settings that relate to any AST traversing stages.
    pub ast_settings: AstSettings,

    /// All settings that relate to the lowering stage of the compiler.
    pub lowering_settings: LoweringSettings,

    /// All settings that relate to the code generation backends of the
    /// compiler.
    pub codegen_settings: CodeGenSettings,

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

    /// Get the optimisation level for the current settings.
    pub fn optimisation(&self) -> OptimisationLevel {
        self.optimisation_level
    }

    /// Get a reference to the [AstSettings].
    pub fn ast_settings(&self) -> &AstSettings {
        &self.ast_settings
    }

    /// Get a mutable reference to [AstSettings]
    pub fn ast_settings_mut(&mut self) -> &mut AstSettings {
        &mut self.ast_settings
    }

    /// Get a reference to [LoweringSettings].
    pub fn lowering_settings(&self) -> &LoweringSettings {
        &self.lowering_settings
    }

    /// Get a reference to [CodeGenSettings].
    pub fn codegen_settings(&self) -> &CodeGenSettings {
        &self.codegen_settings
    }
}

impl Default for CompilerSettings {
    fn default() -> Self {
        Self {
            output_stage_results: false,
            output_metrics: false,
            skip_prelude: false,
            emit_errors: true,
            worker_count: num_cpus::get(),
            stage: CompilerStageKind::default(),
            optimisation_level: OptimisationLevel::default(),
            ast_settings: AstSettings::default(),
            lowering_settings: LoweringSettings::default(),
            codegen_settings: CodeGenSettings::default(),
        }
    }
}

/// What optimisation level the compiler should run at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
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

/// Settings that relate to stages that exclusively operate on the
/// AST that is generated by the parsing, these could be stages that
/// re-write the AST, analyse it or modify it in some way.
///
/// N.B. By default, the AST is not dumped.
#[derive(Debug, Clone, Copy, Default)]
pub struct AstSettings {
    /// Whether to pretty-print all of the generated AST after the whole
    /// [Workspace] has been parsed.
    pub dump_tree: bool,
}

/// Settings that relate to the IR stage of the compiler, these include if the
/// IR should be dumped (and in which mode), whether the IR should be optimised,
/// whether the IR should use `checked` operations, etc.
#[derive(Debug, Clone, Copy)]
pub struct LoweringSettings {
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
        Self { dump_mode: IrDumpMode::Pretty, checked_operations: true, dump_all: false }
    }
}

/// Enum representing the different options for dumping the IR. It can either
/// be emitted in the pretty-printing format, or in the `graphviz` format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum IrDumpMode {
    /// Dump the generated IR using a pretty-printed format
    Pretty,

    /// Dump the generated IR using the `graphviz` format
    Graph,
}

/// All settings that are related to compiler backend and code generation.
///
/// N.B. some information that is stored here may be used by previous stages
/// e.g. target information.
#[derive(Debug, Clone, Copy, Default)]
pub struct CodeGenSettings {
    /// Information about the current "session" that the compiler is running
    /// in. This contains information about which target the compiler is
    /// compiling for, and other information that is used by the compiler
    /// to determine how to compile the source code.
    pub target_info: TargetInfo,

    /// This is only the "backend" for the global instance of code generation.
    ///
    /// Specifically, when things like compile-time evaluation are added, it may
    /// be that some functions/expressions are evaluated at compile-time via the
    /// Hash VM which may mean that the code generation backend for that one
    /// might differ from the overall code generation backend.
    pub backend: CodeGenBackend,
}

/// All of the current possible code generation backends that
/// are available.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum CodeGenBackend {
    /// The LLVM backend is target for code generation.
    LLVM,

    /// The Hash VM interpreter is being targeted.
    VM,
}

impl Default for CodeGenBackend {
    fn default() -> Self {
        Self::LLVM
    }
}

/// Enum representing what mode the compiler should run in. Specifically, if the
/// compiler should only run up to a particular stage within the pipeline.
///
/// @@Todo: consider removing "full" since it is implied by `codegen`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CompilerStageKind {
    Parse,
    DeSugar,
    SemanticPass,
    Typecheck,
    Lower,
    IrGen,
    CodeGen,
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
            CompilerStageKind::CodeGen => write!(f, "codegen"),
            CompilerStageKind::Full => write!(f, "total"),
        }
    }
}
