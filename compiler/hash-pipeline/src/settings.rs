//! Hash Compiler pipeline implementation. This file contains various structures
//! and utilities representing settings and configurations that can be applied
//! to the Compiler pipeline.
use std::{fmt::Display, str::FromStr};

use hash_target::{data_layout::TargetDataLayout, Target, TargetInfo};

use crate::error::{ArgumentError, CompilerError};

/// Various settings that are present on the compiler pipeline when initially
/// launching.
#[derive(Debug, Clone)]
pub struct CompilerSettings {
    /// An optionally specified entry point for the compiler.
    pub entry_point: Option<String>,

    /// Whether debugging log statements are enabled.
    pub debug: bool,

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
    /// Create a new [CompilerSettings].
    pub fn new(worker_count: usize) -> Self {
        Self { worker_count, ..Default::default() }
    }

    /// Get the entry point filename from the [CompilerSettings]. If
    /// none was provided, it is assumed that this is then an interactive
    /// session.
    pub fn entry_point(&self) -> Option<String> {
        self.entry_point.clone()
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
            debug: false,
            entry_point: None,
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OptimisationLevel {
    /// Run the compiler using the debug optimisation level. This will
    /// disable most optimisations that the compiler would otherwise do.
    /// This is intended for building the program as fast as possible.
    Debug,

    /// Optimise the given program as much as possible, essentially
    /// applying all optimisation.
    Release,
}

impl FromStr for OptimisationLevel {
    type Err = CompilerError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "debug" => Ok(Self::Debug),
            "release" => Ok(Self::Release),
            _ => {
                Err(ArgumentError::InvalidValue("optimisation-level".to_string(), s.to_string())
                    .into())
            }
        }
    }
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
    pub dump: bool,
}

/// Settings that relate to the IR stage of the compiler, these include if the
/// IR should be dumped (and in which mode), whether the IR should be optimised,
/// whether the IR should use `checked` operations, etc.
#[derive(Debug, Clone, Copy)]
pub struct LoweringSettings {
    /// Whether the IR should dump all lowered bodies, rather than
    /// relying on user directives to select specific bodies.
    pub dump: bool,

    /// Whether the IR that is generated at the time should be dumped.
    pub dump_mode: IrDumpMode,

    /// Use checked operations when emitting IR, this is usually derived whether
    /// the compiler is building a debug variant or not.
    pub checked_operations: bool,
}

impl Default for LoweringSettings {
    fn default() -> Self {
        Self { dump_mode: IrDumpMode::Pretty, checked_operations: true, dump: false }
    }
}

/// Enum representing the different options for dumping the IR. It can either
/// be emitted in the pretty-printing format, or in the `graphviz` format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone, Default)]
pub struct CodeGenSettings {
    /// Information about the current "session" that the compiler is running
    /// in. This contains information about which target the compiler is
    /// compiling for, and other information that is used by the compiler
    /// to determine how to compile the source code.
    pub target_info: TargetInfo,

    /// The specified target layout information for types. This defines
    /// the sizes of target-dependant types, and default alignments for
    /// primitive types.
    pub layout: TargetDataLayout,

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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum CompilerStageKind {
    Parse,
    DeSugar,
    SemanticPass,
    Typecheck,
    Lower,
    IrGen,
    CodeGen,
    #[default]
    Full,
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

/// This function is used to parse the command line arguments that are
/// passed to the compiler, it will return a [CompilerSettings] struct
/// that contains all of the settings that the compiler should use. If
/// there is an error, this will return an error that can be
/// dealt with by the caller.
pub fn parse_settings_from_args() -> Result<CompilerSettings, CompilerError> {
    let mut settings = CompilerSettings::default();
    let mut args = std::env::args().skip(1);

    while let Some(arg) = args.next() {
        // This is a configuration key that specifies the "key" and then
        // the value in the form of `-C<key>=<value>`
        if arg.starts_with("-C") {
            // Check if the key is part of this argument or if there is a
            // separate argument for the value, which we assume to be the
            // next argument.
            if arg.len() == 2 {
                if let Some(arg) = args.next() {
                    parse_arg_configuration(&mut settings, arg)?;
                } else {
                    return Err(CompilerError::Argument(ArgumentError::UnknownKey(arg)));
                }
            } else {
                parse_arg_configuration(&mut settings, arg.trim_start_matches("-C").to_string())?;
            }
        } else if arg.starts_with("--") {
            let key = arg.trim_start_matches("--").to_string();

            match key.as_str() {
                "debug" => {
                    settings.debug = true;
                }
                "output-metrics" => {
                    settings.output_metrics = true;
                }
                _ => {
                    return Err(CompilerError::Argument(ArgumentError::UnknownKey(arg)));
                }
            }
        } else {
            // This is specifying what kind of a stage the compiler should run
            // the job on whether it is `build`, `check`,
            // `ast-gen`...
            match arg.as_str() {
                "build" => {
                    settings.stage = CompilerStageKind::Full;
                }
                "check" => {
                    settings.stage = CompilerStageKind::Typecheck;
                }
                "ast-gen" => {
                    settings.stage = CompilerStageKind::Parse;
                }
                "ir-gen" => {
                    settings.stage = CompilerStageKind::IrGen;
                }
                _ => {
                    return Err(CompilerError::UnknownStage(arg));
                }
            };

            // The next argument after this is the input file.
            if let Some(filename) = args.next() {
                settings.entry_point = Some(filename);
            } else {
                return Err(CompilerError::MissingEntryPoint);
            }
        }
    }

    Ok(settings)
}

/// This function will parse a single `-C<key>=<value>` argument and apply the
/// specified configuration option to the [CompilerSettings]. Some keys may
/// not have a value, and some keys may specify multiple values with a comma
/// separated list.
fn parse_arg_configuration(
    settings: &mut CompilerSettings,
    arg: String,
) -> Result<(), CompilerError> {
    // First try and see if we have been provided a key-value pair, if not
    // then we will assume that the key is the argument and the value is
    // `None`.
    let (key, value) = if let Some(split_pos) = arg.find('=') {
        let (key, value) = arg.split_at(split_pos);
        (key.to_string(), Some(value[1..].to_string()))
    } else {
        (arg.clone(), None)
    };

    // When a value is expected from a key, but none is provided, this
    // closure will be used to return an error.
    let expected_value = || CompilerError::Argument(ArgumentError::MissingValue(key.clone()));

    match key.as_str() {
        "target" => {
            let value = value.ok_or_else(expected_value)?;

            let target = Target::from_string(value.clone())
                .ok_or_else(|| CompilerError::InvalidTarget(value))?;

            settings.codegen_settings.target_info.set_target(target)
        }
        "optimisation-level" => {
            let value = value.ok_or_else(expected_value)?;
            let opt_level = OptimisationLevel::from_str(value.as_str())?;
            settings.optimisation_level = opt_level;
        }
        "dump" => {
            let value = value.ok_or_else(expected_value)?;

            match value.as_str() {
                "ast" => {
                    settings.ast_settings.dump = true;
                }
                "ir" => {
                    settings.lowering_settings.dump = true;
                }
                _ => {
                    return Err(CompilerError::Argument(ArgumentError::InvalidValue(key, value)));
                }
            }
        }
        "ir-dump-mode" => {
            let value = value.ok_or_else(expected_value)?;

            match value.as_str() {
                "pretty" => {
                    settings.lowering_settings.dump_mode = IrDumpMode::Pretty;
                }
                "graph" => {
                    settings.lowering_settings.dump_mode = IrDumpMode::Graph;
                }
                _ => {
                    return Err(CompilerError::Argument(ArgumentError::InvalidValue(key, value)));
                }
            }
        }
        "backend" => {
            let value = value.ok_or_else(expected_value)?;

            match value.as_str() {
                "llvm" => {
                    settings.codegen_settings.backend = CodeGenBackend::LLVM;
                }
                "vm" => {
                    settings.codegen_settings.backend = CodeGenBackend::VM;
                }
                _ => {
                    return Err(CompilerError::Argument(ArgumentError::InvalidValue(key, value)));
                }
            }
        }
        _ => {
            return Err(CompilerError::Argument(ArgumentError::UnknownKey(key)));
        }
    };

    Ok(())
}
