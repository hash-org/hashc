//! Hash Compiler pipeline implementation. This file contains various structures and
//! utilities representing settings and configurations that can be applied to the
//! Compiler pipeline.
//!
//! All rights reserved 2022 (c) The Hash Language authors

/// Various settings that are present on the compiler pipeline when initially launching.
#[derive(Debug, Clone, Copy)]
pub struct CompilerSettings {
    pub mode: CompilerMode,
}

/// Enum representing what mode the compiler should run in. Specifically, if the
/// compiler should only run up to a particular stage within the pipeline.
#[derive(Debug, Clone, Copy)]
pub enum CompilerMode {
    AstGen,
    Full,
}

impl CompilerSettings {
    pub fn new(mode: CompilerMode) -> Self {
        Self { mode }
    }
}

impl Default for CompilerSettings {
    fn default() -> Self {
        Self {
            mode: CompilerMode::Full,
        }
    }
}
