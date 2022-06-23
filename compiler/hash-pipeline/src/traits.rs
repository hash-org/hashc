//! Hash Compiler pipeline traits. This file contains implementable interfaces that
//! are used by the pipeline to run various stages that transform the provided sources
//! into runnable/executable code.

use hash_reporting::report::Report;
use hash_source::{InteractiveId, ModuleId, SourceId};

use crate::{settings::CompilerJobParams, sources::Sources};

pub type CompilerResult<T> = Result<T, Vec<Report>>;

/// The [Parser] represents an abstract parser that can parse all aspects of the Hash programming
/// language.
pub trait Parser<'pool> {
    /// Given a [SourceId], parse the current job and append any parsed modules to the
    /// provided sources parameter. On success, the function returns nothing and on
    /// failure, the stage provides a generated diagnostics [Report].
    fn parse(
        &mut self,
        entry_point: SourceId,
        sources: &mut Sources,
        pool: &'pool rayon::ThreadPool,
    ) -> CompilerResult<()>;
}

/// The [Desugar] represents an abstract parser that can parse all aspects of the Hash programming
/// language.
pub trait Desugar<'pool> {
    type State;

    /// Make [Self::State].
    fn make_state(&mut self) -> CompilerResult<Self::State>;

    /// Perform a de-sugaring pass on the provided sources.
    fn desugar(
        &mut self,
        entry_point: SourceId,
        sources: &mut Sources,
        state: &mut Self::State,
        pool: &'pool rayon::ThreadPool,
    ) -> CompilerResult<()>;
}

/// The [SemanticPass] represents a stage within the compiler that performs various
/// verifications on the generated AST from the [Parser] and the [Desugar] stage. The
/// details of the checks that this pass performs is available within the `hash-ast-passes`
/// crate. However, overall the checks that this stage should perform will be detailed within
/// the specification of the language.
pub trait SemanticPass<'pool> {
    type State;

    /// Make [Self::State].
    fn make_state(&mut self) -> CompilerResult<Self::State>;

    /// Perform a de-sugaring pass on the provided sources.
    fn perform_pass(
        &mut self,
        entry_point: SourceId,
        sources: &mut Sources,
        state: &mut Self::State,
        pool: &'pool rayon::ThreadPool,
    ) -> Result<(), Vec<Report>>;
}

/// The [Tc] represents an abstract type checker that implements all the specified
/// typechecking methods and internally performs some kind of typechecking operations.
/// The methods [Tc::check_module] and [Tc::check_interactive] will return
/// a unit on success, or a generated diagnostic error report which can be displayed
/// and printed by the user of the pipeline. Both functions modify the states of the
/// checker and return them regardless of error, both states are considered to be the
/// new states and should be set in the compiler pipeline.
pub trait Tc<'c> {
    /// The general [Tc] state. This is implementation specific to the
    /// typechecker that implements this trait. The pipeline should have no
    /// dealings with the actual state, except saving it.
    type State;

    /// Make the general [Tc::State].
    fn make_state(&mut self) -> CompilerResult<Self::State>;

    /// Given a [InteractiveId], check the interactive statement with the specific rules
    /// that are applied in interactive rules. The function accepts the previous [Tc]
    /// state and previous [Tc::InteractiveState].
    fn check_interactive<'pool>(
        &'pool mut self,
        interactive_id: InteractiveId,
        sources: &Sources,
        state: &mut Self::State,
        job_params: &CompilerJobParams,
    ) -> CompilerResult<()>;

    /// Given a [ModuleId], check the module. The function accepts the previous [Tc]
    /// state and [Tc::ModuleState]
    fn check_module(
        &mut self,
        module_id: ModuleId,
        sources: &Sources,
        state: &mut Self::State,
        job_params: &CompilerJobParams,
    ) -> CompilerResult<()>;
}

/// The virtual machine trait
pub trait VirtualMachine<'c> {
    /// The general [VirtualMachine] state. This is implementation specific to the
    /// VM that implements this trait. The pipeline should have no
    /// dealings with the actual state, except saving it.
    type State;

    /// Make the general [VirtualMachine::State].
    fn make_state(&mut self) -> CompilerResult<Self::State>;

    /// Run the currently generated VM
    fn run(&mut self, state: &mut Self::State) -> CompilerResult<()>;
}
