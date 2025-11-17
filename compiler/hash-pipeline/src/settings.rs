//! Hash Compiler pipeline implementation. This file contains various structures
//! and utilities representing settings and configurations that can be applied
//! to the Compiler pipeline.
use core::fmt;
use std::{
    env::{self, temp_dir},
    fmt::Display,
    path::PathBuf,
    str::FromStr,
};

use hash_ast_utils::dump::AstDumpMode;
use hash_target::{HOST_TARGET_TRIPLE, HasTarget, Target};
use hash_utils::{
    clap::{Args, Parser, ValueEnum},
    logging::CompilerMessagingFormat,
    schemars::{self, JsonSchema},
    serde::{self, Deserialize, Serialize},
    tree_writing::CharacterSet,
};
use serde_json;

use crate::{error::PipelineError, fs::resolve_path};

/// Various settings that are present on the compiler pipeline when initially
/// launching.
#[derive(Parser, Debug, Clone, Deserialize, Serialize, JsonSchema)]
#[serde(crate = "self::serde", deny_unknown_fields)]
#[command(name = "hashc", version = env!("COMPILER_VERSION"), about = "", author)]
pub struct CompilerSettings {
    /// An optionally specified entry point for the compiler.
    ///
    /// N.B. This path is the one that is specified via command-line arguments,
    /// it is not resolved and it is not guaranteed to exist. The resolved
    /// path can be accessed via [`CompilerSettings::entry_point`] API.
    #[arg(
        short = 'i',
        long,
        help = "The entry point for the compiler. This will invoke the compile in a non-interactive mode."
    )]
    pub entry_point: Option<PathBuf>,

    /// An optionally specified output directory for compiler generated
    /// information and artifacts.
    ///
    /// N.B. This path is the one that is specified via command-line arguments,
    /// it is not resolved and it is not guaranteed to exist. The resolved
    /// path can be accessed via [`CompilerSettings::output_directory`] API.
    #[arg(
        short = 'o',
        long,
        help = "The directory to use when outputting compiler generated information and artifacts."
    )]
    pub output_directory: Option<PathBuf>,

    /// A collection of raw configuration options (in JSON format) that can be
    /// used to configure the compiler pipeline. These are post-processed by
    /// the compiler pipeline to set the appropriate settings.
    #[arg(long, default_value = None, num_args=0..)]
    #[serde(skip)]
    pub configure: Option<Vec<String>>,

    /// Whether debugging log statements are enabled.
    #[arg(long, default_value_t = false)]
    #[serde(default)]
    pub debug: bool,

    /// Print metrics about each stage when the entire pipeline has completed.
    #[arg(long = "timings", default_value_t = false)]
    #[serde(default, alias = "timings")]
    pub show_timings: bool,

    /// The format to use when outputting information about compilation, either
    /// in JSON format or in the normal format.
    #[arg(long, default_value_t = CompilerMessagingFormat::Normal)]
    #[serde(default)]
    pub messaging_format: CompilerMessagingFormat,

    /// Whether to output of each stage result.
    #[arg(long, default_value_t = false)]
    #[serde(default)]
    pub output_stage_results: bool,

    /// The number of workers that the compiler pipeline should have access to.
    /// This value is used to determine the thread pool size that is then shared
    /// across arbitrary stages within the compiler.
    #[arg(long, default_value_t = num_cpus::get())]
    #[serde(default = "num_cpus::get")]
    pub worker_count: usize,

    /// Whether the compiler should skip bootstrapping the prelude, this
    /// is set for testing purposes.
    #[arg(long, default_value_t = false)]
    #[serde(default)]
    pub skip_prelude: bool,

    /// This specifies whether the `prelude` module should not be emitted
    /// when the compiler should emit things like `TIR` or `IR` in order
    /// to avoid noise in the unit tests. @@Hack: remove this somehow?
    #[arg(long, default_value_t = false)]
    #[serde(default)]
    pub prelude_is_quiet: bool,

    /// Whether the pipeline should output errors and warnings to
    /// standard error
    #[arg(long, default_value_t = true)]
    #[serde(default)]
    pub emit_errors: bool,

    /// Whether the compiler should print out the current messaging schema that
    /// is used to communicate with the compiler.
    #[arg(long = "schema", default_value_t = false)]
    #[serde(default)]
    pub emit_schema: bool,

    /// Which character set to use when printing information
    /// to the terminal, this affects rendering of characters
    /// such as the arrow in the error messages.
    #[arg(long, value_parser = CharacterSet::parse, required=false, default_value = "unicode", default_value_t = CharacterSet::Unicode)]
    #[serde(default)]
    pub character_set: CharacterSet,

    /// The optimisation level that is to be performed.
    #[arg(long, default_value_t = OptimisationLevel::default())]
    #[serde(default)]
    pub optimisation_level: OptimisationLevel,

    /// All settings that relate to any AST traversing stages.
    #[command(flatten)]
    #[serde(default)]
    pub ast_settings: AstSettings,

    /// All settings that relate to the lowering stage of the compiler.
    #[command(flatten)]
    #[serde(default)]
    pub lowering_settings: LoweringSettings,

    /// All settings that relate to the semantic analysis stage.
    #[command(flatten)]
    #[serde(default)]
    pub semantic_settings: SemanticSettings,

    /// All settings that relate to the code generation backends of the
    /// compiler.
    #[command(flatten)]
    #[serde(default)]
    pub codegen_settings: CodeGenSettings,

    /// To what should the compiler run to, anywhere from parsing, typecheck, to
    /// code generation.
    #[arg(long, default_value_t = CompilerStageKind::default())]
    #[serde(default)]
    pub stage: CompilerStageKind,
}

trait MergeConfig {
    fn merge_config(&mut self, config: &Self);
}

impl MergeConfig for CompilerSettings {
    fn merge_config(&mut self, config: &Self) {
        self.debug |= config.debug;
        self.show_timings |= config.show_timings;
        self.output_stage_results |= config.output_stage_results;
        self.worker_count = config.worker_count;
        self.skip_prelude |= config.skip_prelude;
        self.prelude_is_quiet |= config.prelude_is_quiet;
        self.messaging_format = config.messaging_format;
        self.emit_errors |= config.emit_errors;
        self.emit_schema |= config.emit_schema;
        self.character_set = config.character_set;
        self.optimisation_level = config.optimisation_level;
        self.entry_point.clone_from(&config.entry_point);
        self.output_directory.clone_from(&config.output_directory);
        self.ast_settings.merge_config(&config.ast_settings);
        self.lowering_settings.merge_config(&config.lowering_settings);
        self.semantic_settings.merge_config(&config.semantic_settings);
        self.codegen_settings.merge_config(&config.codegen_settings);
        self.stage = config.stage;
    }
}

impl CompilerSettings {
    /// Create a new [CompilerSettings].
    pub fn new() -> Self {
        let mut s = Self::default();
        s.post_init();
        s
    }

    /// Create a new [CompilerSettings] from the command-line arguments.
    ///
    /// 1. Parse the [CompilerSettings] from the command-line arguments.
    ///
    /// 2. Apply any configurations that are specified in the `--configure`
    ///    flag.
    pub fn from_cli() -> Result<Self, PipelineError> {
        let mut settings = Self::try_parse().map_err(PipelineError::ParseError)?;

        // We're gonna gobble up all the `configurations` and then merge them
        // into the settings.
        std::mem::take(&mut settings.configure).unwrap_or_default().iter().try_for_each(
            |config| {
                let config: CompilerSettings = serde_json::from_str(config).map_err(|err| {
                    PipelineError::InvalidValue("configure".to_string(), err.to_string())
                })?;
                settings.merge_config(&config);
                Ok(())
            },
        )?;

        settings.post_init();
        Ok(settings)
    }

    /// Run any post-init adjustments that must happen after the settings.
    ///
    /// Add some kind of utility to guarantee a `PostInit` trait that can be
    /// implemented by the settings.
    #[inline]
    fn post_init(&mut self) {
        self.apply_optimisation_level(self.optimisation_level);
    }

    /// Get the entry point filename from the [CompilerSettings]. If
    /// [`None`] was provided, it is assumed that this is then an interactive
    /// session.
    pub fn try_entry_point(&self) -> Option<Result<PathBuf, PipelineError>> {
        self.entry_point.as_ref().map(|path| {
            let current_dir = env::current_dir().unwrap();
            resolve_path(path.to_str().unwrap(), current_dir).map_err(PipelineError::ImportPath)
        })
    }

    /// Get the entry point from the [CompilerSettings] whilst asserting that
    /// there must be a given entry point in this case. If the entrypoint is not
    /// specified, a [`PipelineError::MissingEntryPoint`] is then returned.
    pub fn entry_point(&self) -> Result<PathBuf, PipelineError> {
        self.try_entry_point().transpose()?.ok_or(PipelineError::MissingEntryPoint)
    }

    /// Get the output directory from the [CompilerSettings]. The output path
    /// is decided in the following way:
    ///
    /// 1. If the user has specified an output directory, use that.
    ///
    /// 2. If the user has specified an entry point, use the directory of the
    ///    entry point with an appended `out` directory.
    ///
    /// 3. If the user has not specified an entry point, use the operating
    ///    system temporary directory with an appended `hash-#session-id`
    ///    directory.
    pub fn output_directory(&self) -> Result<PathBuf, PipelineError> {
        // For the `temp` directory case, we want to create a folder within the
        // temporary directory that is unique to this session.
        let temp_dir = {
            let mut temp_dir = temp_dir();
            temp_dir.push(format!("hash-{}", std::process::id()));
            temp_dir
        };

        // We want to find the first suitable candidate for a valid output folder, these
        // items are specified in order of priority.
        let output_candidates = [&self.output_directory, &self.entry_point, &Some(temp_dir)];
        let mut output_directory = None;

        if let Some(candidate) = output_candidates.iter().copied().flatten().next() {
            let mut candidate = candidate.clone();

            // If the candidate is a file, then we want to get the parent directory
            // of the file.
            if candidate.is_file() {
                candidate.pop();
                candidate.push("target");
            }

            // We also push the "optimisation_level" as the final directory
            // in order to separate the output of different optimisation levels.
            candidate.push(self.optimisation_level.as_str());

            // If the candidate doesn't exist or isn't a directory, then we want to
            // create the full directory path so that the compiler can write to it
            // later during compilation.
            if !candidate.exists() || !candidate.is_dir() {
                std::fs::create_dir_all(&candidate).map_err(|error| {
                    PipelineError::ResourceCreation { path: candidate.clone(), error }
                })?;
            }

            output_directory = Some(candidate);
        }

        // It should not be possible to get here without at least one
        // candidate for a valid output directory to be chosen.
        Ok(output_directory.unwrap())
    }

    /// Configure the [CompilerSettings] to have a specified
    /// [OptimisationLevel].
    ///
    /// This function will also disable the default options that a
    /// [OptimisationLevel] implies, i.e. for "release",
    /// `checked_operations` are disabled.
    pub fn set_optimisation_level(&mut self, level: OptimisationLevel) {
        self.optimisation_level = level;
        self.apply_optimisation_level(level);
    }

    pub fn apply_optimisation_level(&mut self, level: OptimisationLevel) {
        match level {
            OptimisationLevel::Debug => {
                self.lowering_settings.checked_operations = true;
            }
            OptimisationLevel::Release => {
                self.lowering_settings.checked_operations = false;
            }
            OptimisationLevel::Size | OptimisationLevel::MinSize => {}
        }
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

    /// Get a reference to the [SemanticSettings].
    pub fn semantic_settings(&self) -> &SemanticSettings {
        &self.semantic_settings
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

impl HasTarget for CompilerSettings {
    fn target(&self) -> &Target {
        &self.codegen_settings.target_info.target
    }
}

/// Trait that is implemented by all items that have access to the
/// [`CompilerSettings`].
pub trait HasCompilerSettings {
    fn settings(&self) -> &CompilerSettings;
}

impl Default for CompilerSettings {
    fn default() -> Self {
        Self {
            debug: false,
            configure: None,
            entry_point: None,
            output_directory: None,
            output_stage_results: false,
            messaging_format: CompilerMessagingFormat::Normal,
            show_timings: false,
            skip_prelude: false,
            prelude_is_quiet: false,
            emit_errors: true,
            emit_schema: false,
            character_set: CharacterSet::Unicode,
            worker_count: num_cpus::get(),
            stage: CompilerStageKind::default(),
            optimisation_level: OptimisationLevel::default(),
            ast_settings: AstSettings::default(),
            lowering_settings: LoweringSettings::default(),
            codegen_settings: CodeGenSettings::default(),
            semantic_settings: SemanticSettings::default(),
        }
    }
}

/// What optimisation level the compiler should run at.
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    ValueEnum,
    Deserialize,
    Serialize,
    JsonSchema,
)]
#[serde(crate = "self::serde", rename_all = "kebab-case")]
#[derive(Default)]
pub enum OptimisationLevel {
    /// Run the compiler using the debug optimisation level. This will
    /// disable most optimisations that the compiler would otherwise do.
    /// This is intended for building the program as fast as possible.
    #[default]
    Debug,

    /// Optimise the given program as much as possible, essentially
    /// applying all optimisation.
    Release,

    /// Optimise for size but not aggressively as
    /// [`OptimisationLevel::MinSize`].
    Size,

    /// Optimise the given program for size rather than speed.
    MinSize,
}

impl OptimisationLevel {
    /// Check if the optimisation level is [`OptimisationLevel::Release`].
    pub fn is_release(&self) -> bool {
        matches!(self, Self::Release)
    }

    /// Get the level in optimisation of size.
    pub fn size_level(&self) -> usize {
        match self {
            Self::Size => 1,
            Self::MinSize => 2,
            _ => 0,
        }
    }

    /// Get the optimisation level as a string.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Debug => "debug",
            Self::Release => "release",
            Self::Size => "size",
            Self::MinSize => "min-size",
        }
    }
}

impl FromStr for OptimisationLevel {
    type Err = PipelineError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "debug" => Ok(Self::Debug),
            "release" => Ok(Self::Release),
            "size" => Ok(Self::Size),
            "min-size" => Ok(Self::MinSize),
            _ => Err(PipelineError::InvalidValue("optimisation-level".to_string(), s.to_string())),
        }
    }
}

impl fmt::Display for OptimisationLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Settings that relate to stages that exclusively operate on the
/// AST that is generated by the parsing, these could be stages that
/// re-write the AST, analyse it or modify it in some way.
///
/// N.B. By default, the AST is not dumped.
#[derive(Debug, Clone, Copy, Args, Deserialize, Serialize, JsonSchema)]
#[serde(crate = "self::serde")]
pub struct AstSettings {
    /// Whether to pretty-print all of the generated AST after the whole
    /// [Workspace] has been parsed.
    #[arg(name = "ast-dump", long = "ast-dump", default_value_t = false)]
    pub dump: bool,

    /// What kind of dumping mode should it be, either being "pretty"
    /// or tree mode.
    #[arg(name="ast-dump-mode", long="ast-dump-mode", default_value_t = AstDumpMode::Tree)]
    pub dump_mode: AstDumpMode,
}

impl Default for AstSettings {
    fn default() -> Self {
        Self { dump: false, dump_mode: AstDumpMode::Tree }
    }
}

impl MergeConfig for AstSettings {
    fn merge_config(&mut self, config: &Self) {
        self.dump |= config.dump;
        self.dump_mode = config.dump_mode;
    }
}

/// Settings that relate to the IR stage of the compiler, these include if the
/// IR should be dumped (and in which mode), whether the IR should be optimised,
/// whether the IR should use `checked` operations, etc.
#[derive(Debug, Clone, Copy, Args, Deserialize, Serialize, JsonSchema)]
#[serde(crate = "self::serde")]
pub struct LoweringSettings {
    /// Whether the IR should dump all lowered bodies, rather than
    /// relying on user directives to select specific bodies.
    #[arg(name = "ir-dump", long = "ir-dump", default_value_t = false)]
    pub dump: bool,

    /// What kind of dumping mode should it be, either being "pretty"
    /// or "graphviz" mode.
    #[arg(long="ir-dump-mode", default_value_t = IrDumpMode::Pretty)]
    pub dump_mode: IrDumpMode,

    /// Use checked operations when emitting IR, this is usually derived whether
    /// the compiler is building a debug variant or not.
    #[arg(long = "ir-checked-operations", default_value_t = true, action = clap::ArgAction::Set)]
    pub checked_operations: bool,
}

impl Default for LoweringSettings {
    fn default() -> Self {
        Self { dump_mode: IrDumpMode::Pretty, checked_operations: true, dump: false }
    }
}

impl MergeConfig for LoweringSettings {
    fn merge_config(&mut self, config: &Self) {
        self.dump = config.dump;
        self.dump_mode = config.dump_mode;
        self.checked_operations = config.checked_operations;
    }
}

/// Enum representing the different options for dumping the IR. It can either
/// be emitted in the pretty-printing format, or in the `graphviz` format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Serialize, Deserialize, JsonSchema)]
#[serde(crate = "self::serde")]
pub enum IrDumpMode {
    /// Dump the generated IR using a pretty-printed format
    Pretty,

    /// Dump the generated IR using the `graphviz` format
    Graph,
}

impl fmt::Display for IrDumpMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Pretty => write!(f, "pretty"),
            Self::Graph => write!(f, "graph"),
        }
    }
}

/// All settings related to semantic analysis and typechecking.
#[derive(Debug, Clone, Args, Deserialize, Serialize, JsonSchema)]
#[serde(crate = "self::serde")]
pub struct SemanticSettings {
    /// Whether the compiler should dump the generated TIR (typed intermediate
    /// representation).
    #[arg(long = "tir-dump", default_value_t = false)]
    pub dump_tir: bool,

    /// Whether the compiler should evaluate the generated TIR.
    #[arg(long = "tir-eval", default_value_t = false)]
    pub eval_tir: bool,

    /// Whether the compiler should monomorphise the generated TIR.
    #[arg(long = "tir-mono", default_value_t = true)]
    pub mono_tir: bool,
}

impl Default for SemanticSettings {
    fn default() -> Self {
        Self { dump_tir: false, eval_tir: false, mono_tir: true }
    }
}

impl MergeConfig for SemanticSettings {
    fn merge_config(&mut self, config: &Self) {
        self.dump_tir |= config.dump_tir
    }
}

/// All settings that are related to compiler backend and code generation.
///
/// N.B. some information that is stored here may be used by previous stages
/// e.g. target information.
#[derive(Debug, Clone, Args, Deserialize, Serialize, JsonSchema)]
#[serde(crate = "self::serde")]
pub struct CodeGenSettings {
    /// Information about the current "session" that the compiler is running
    /// in. This contains information about which target the compiler is
    /// compiling for, and other information that is used by the compiler
    /// to determine how to compile the source code.
    #[command(flatten)]
    #[serde(skip)]
    pub target_info: TargetInfo,

    /// This is only the "backend" for the global instance of code generation.
    ///
    /// Specifically, when things like compile-time evaluation are added, it may
    /// be that some functions/expressions are evaluated at compile-time via the
    /// Hash VM which may mean that the code generation backend for that one
    /// might differ from the overall code generation backend.
    #[arg(long="backend", default_value_t = CodeGenBackend::default())]
    pub backend: CodeGenBackend,

    /// An optionally specified path to a file that should be used to
    /// write the executable to. If the path is [`None`], the executable
    /// path will be derived from the workspace.
    #[arg(long = "output-path")]
    pub output_path: Option<PathBuf>,

    /// Emit the generated IR to standard output.
    #[arg(long = "bc-dump", default_value_t = false)]
    pub dump_bytecode: bool,

    /// Emit the generated ASM to standard output.
    #[arg(long = "asm-dump", default_value_t = false)]
    pub dump_assembly: bool,

    /// Emit the generated Link line for the project if the compiler
    /// pipeline specifies that something should be linked.
    #[arg(long = "link-line-dump", default_value_t = false)]
    pub dump_link_line: bool,
}

impl MergeConfig for CodeGenSettings {
    fn merge_config(&mut self, config: &Self) {
        self.target_info = config.target_info.clone();
        self.backend = config.backend;
        self.output_path.clone_from(&config.output_path);
        self.dump_bytecode |= config.dump_bytecode;
        self.dump_assembly |= config.dump_assembly;
        self.dump_link_line |= config.dump_link_line;
    }
}

/// Holds information about various targets that are currently used by the
/// compiler.
#[derive(Debug, Clone, Default, Args)]
pub struct TargetInfo {
    /// The target value of the host that the compiler is running
    /// for.
    #[arg(long, value_parser = target_value_parser, default_value_t = Target::default())]
    pub host: Target,

    /// The target that the compiler is compiling for.
    #[arg(long, value_parser = target_value_parser, default_value_t = Target::default())]
    pub target: Target,
}

/// FUnction is internally used to parse a target from a string.
fn target_value_parser(s: &str) -> Result<Target, String> {
    Target::search(s).ok_or_else(|| format!("unknown target: {}", s))
}

impl Default for CodeGenSettings {
    fn default() -> Self {
        Self {
            // @@Todo: we should emit a warning if the target is not supported, this
            // isn't a problem unless we're compiling to an executable.
            target_info: TargetInfo {
                host: Target::search(HOST_TARGET_TRIPLE).unwrap_or_default(),
                target: Target::search(HOST_TARGET_TRIPLE).unwrap_or_default(),
            },
            backend: Default::default(),
            output_path: Default::default(),
            dump_bytecode: Default::default(),
            dump_assembly: Default::default(),
            dump_link_line: Default::default(),
        }
    }
}

/// All of the current possible code generation backends that
/// are available.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Serialize, Deserialize, JsonSchema)]
#[serde(crate = "self::serde", rename_all = "kebab-case")]
pub enum CodeGenBackend {
    /// The LLVM backend is target for code generation.
    #[cfg(feature = "llvm")]
    LLVM,

    /// The Hash VM interpreter is being targeted.
    VM,
}

#[allow(clippy::derivable_impls)]
impl Default for CodeGenBackend {
    fn default() -> Self {
        #[cfg(feature = "llvm")]
        {
            Self::LLVM
        }
        #[cfg(not(feature = "llvm"))]
        {
            Self::VM
        }
    }
}

impl CodeGenBackend {
    /// Check if the code generation backend is the LLVM backend.
    #[cfg(feature = "llvm")]
    pub fn is_llvm(&self) -> bool {
        matches!(self, Self::LLVM)
    }

    #[cfg(not(feature = "llvm"))]
    pub fn is_llvm(&self) -> bool {
        false
    }

    /// Check if the code generation backend is the Hash VM backend.
    pub fn is_vm(&self) -> bool {
        matches!(self, Self::VM)
    }
}

impl fmt::Display for CodeGenBackend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            #[cfg(feature = "llvm")]
            Self::LLVM => write!(f, "llvm"),
            Self::VM => write!(f, "vm"),
        }
    }
}

/// Enum representing what mode the compiler should run in. Specifically, if the
/// compiler should only run up to a particular stage within the pipeline.
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
    Default,
    ValueEnum,
    Deserialize,
    Serialize,
    JsonSchema,
)]
#[serde(crate = "self::serde", rename_all = "kebab-case")]
pub enum CompilerStageKind {
    /// Parse the source code into an AST.
    Parse,

    /// Run the compilation pipeline until AST expansion
    /// terminates.
    Expand,

    /// Perform semantic analysis on the AST, this includes
    /// only untyped semantic checks that must occur before
    /// the typechecker runs.
    UntypedAnalysis,

    /// The general semantic pass, resolve types, normalise everything
    /// and prepare for IR generation.
    Analysis,

    /// Convert the produced TIR from the typechecking stage into
    /// Hash IR.
    Lower,

    /// Emit the generated bit-code for each module, this does
    /// not complete the entire compilation process, since the
    /// object files are not yet linked. Therefore, it does
    /// not produce an executable. This is relevant for whether
    /// or not a program needs an entry point defined in order
    /// to successfully compile.
    CodeGen,

    /// Run the linking stage.
    Link,

    /// If the compiler is in interactive mode, this will run
    /// the full pipeline all the way to the virtual machine, if
    /// however there is an entry point defined, this means that
    /// this will invoke the compiler through the full pipeline,
    /// whilst also potentially creating an executable.
    #[default]
    Build,

    /// This is a special stage that is used to instruct the compiler
    /// to immediately run the emitted executable.
    Exe,
}

impl CompilerStageKind {
    /// Convert [CompilerStageKind] into a string name.
    pub fn as_str(&self) -> &'static str {
        match self {
            CompilerStageKind::Parse => "parse",
            CompilerStageKind::Expand => "expand",
            CompilerStageKind::UntypedAnalysis => "untyped-analysis",
            CompilerStageKind::Analysis => "analysis",
            CompilerStageKind::Lower => "lower",
            CompilerStageKind::CodeGen => "codegen",
            CompilerStageKind::Link => "link",
            CompilerStageKind::Build => "build",
            CompilerStageKind::Exe => "exe",
        }
    }
}

impl Display for CompilerStageKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
