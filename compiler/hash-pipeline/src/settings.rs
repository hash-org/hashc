//! Hash Compiler pipeline implementation. This file contains various structures and
//! utilities representing settings and configurations that can be applied to the
//! Compiler pipeline.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use std::fmt::Display;

/// Various settings that are present on the compiler pipeline when initially launching.
#[derive(Debug, Clone, Copy)]
pub struct CompilerSettings {
    /// Print metrics about each stage when the entire pipeline has completed.
    ///
    /// Note: This flag has no effect if the compiler is not specified to run in
    ///       debug mode!
    pub display_metrics: bool,

    /// The number of workers that the compiler pipeline should have access to.
    /// This value is used to determine the thread pool size that is then shared
    /// across arbitrary stages within the compiler.
    pub worker_count: usize,
}

impl CompilerSettings {
    pub fn new(display_metrics: bool, worker_count: usize) -> Self {
        Self {
            worker_count,
            display_metrics,
        }
    }
}

impl Default for CompilerSettings {
    fn default() -> Self {
        Self {
            display_metrics: false, // @@TODO: determine this by the mode of operation
            worker_count: num_cpus::get(),
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

pub struct CompilerJobParams {
    /// Denoting to what stage the pipeline should get before terminating.
    pub mode: CompilerMode,

    /// Flag used to denote whether at a certain stage the compiler should
    /// output a result from the operation. This flag is not used by the
    /// [CompilerMode::Full] to denote whether the pipeline should
    /// output the result of any computation to standard output. This flag
    /// is only used by stages that might print debug information about what
    /// happened during the stage.
    pub output_stage_result: bool,
}

impl CompilerJobParams {
    pub fn new(mode: CompilerMode, output_stage_result: bool) -> Self {
        Self {
            mode,
            output_stage_result,
        }
    }
}

impl Default for CompilerJobParams {
    fn default() -> Self {
        Self {
            mode: CompilerMode::Full,
            output_stage_result: false,
        }
    }
}
