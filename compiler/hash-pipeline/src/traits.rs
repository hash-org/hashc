//! Hash Compiler pipeline traits. This file contains implementable interfaces
//! that are used by the pipeline to run various stages that transform the
//! provided sources into runnable/executable code.

use hash_reporting::report::Report;
use hash_source::{InteractiveId, ModuleId, SourceId};

use crate::sources::Workspace;

pub type CompilerResult<T> = Result<T, Vec<Report>>;

/// The [Parser] represents an abstract parser that can parse all aspects of the
/// Hash programming language.
pub trait Parser<'pool> {
    /// Given a [SourceId], parse the current job and append any parsed modules
    /// to the provided sources parameter. On success, the function returns
    /// nothing and on failure, the stage provides a generated diagnostics
    /// [Report].
    fn parse(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        pool: &'pool rayon::ThreadPool,
    ) -> CompilerResult<()>;
}

/// The [Desugar] represents an abstract parser that can parse all aspects of
/// the Hash programming language.
pub trait Desugar<'pool> {
    type State;

    /// Initialise [Desugar::State].
    fn make_state(&mut self) -> CompilerResult<Self::State>;

    /// Perform a de-sugaring pass on the provided sources.
    fn desugar(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        state: &mut Self::State,
        pool: &'pool rayon::ThreadPool,
    ) -> CompilerResult<()>;
}

/// The [SemanticPass] represents a stage within the compiler that performs
/// various verifications on the generated AST from the [Parser] and the
/// [Desugar] stage. The details of the checks that this pass performs is
/// available within the `hash-ast-passes` crate. However, overall the checks
/// that this stage should perform will be detailed within the specification of
/// the language.
pub trait SemanticPass<'pool> {
    /// Perform a de-sugaring pass on the provided sources.
    fn perform_pass(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        pool: &'pool rayon::ThreadPool,
    ) -> Result<(), Vec<Report>>;
}

/// The [Tc] represents an abstract type checker that implements all the
/// specified typechecking methods and internally performs some kind of
/// typechecking operations. The methods [Tc::check_module] and
/// [Tc::check_interactive] will return a unit on success, or a generated
/// diagnostic error report which can be displayed and printed by the user of
/// the pipeline. Both functions modify the states of the checker and return
/// them regardless of error, both states are considered to be the new states
/// and should be set in the compiler pipeline.
pub trait Tc<'c> {
    /// The [Tc] state. This is implementation specific to the
    /// typechecker that implements this trait. The pipeline should have no
    /// dealings with the actual state, except saving it.
    type State;

    /// Initialise [Tc::State].
    fn make_state(&mut self) -> CompilerResult<Self::State>;

    /// Given a [InteractiveId], check the interactive statement with the
    /// specific rules that are applied in interactive rules. The function
    /// accepts the previous [Tc::State].
    fn check_interactive<'pool>(
        &'pool mut self,
        interactive_id: InteractiveId,
        workspace: &Workspace,
        state: &mut Self::State,
    ) -> CompilerResult<()>;

    /// Given a [ModuleId], check the module. The function accepts the previous
    /// [Tc::State].
    fn check_module(
        &mut self,
        module_id: ModuleId,
        workspace: &Workspace,
        state: &mut Self::State,
    ) -> CompilerResult<()>;
}

/// The IR lowering trait, converting typed AST into Hash IR
pub trait Lowering<'c> {
    /// IR Lowering state, any temporary state that the IR Lowering requires
    /// in order to lower the AST.
    type State;

    /// Initialise [Lowering::State].
    fn make_state(&mut self) -> CompilerResult<Self::State>;

    /// Given a [InteractiveId], perform a lowering on the provided typed
    /// body block whilst keeping state on previously specified interactive
    /// blocks.
    fn lower_interactive_block<'pool>(
        &'pool mut self,
        interactive_id: InteractiveId,
        workspace: &Workspace,
        state: &mut Self::State,
    ) -> CompilerResult<()>;

    /// Perform a IR lowering pass on a module specified by a [ModuleId]. The
    /// result is written to the [Workspace] IR store.
    fn lower_module(
        &mut self,
        module_id: ModuleId,
        workspace: &Workspace,
        state: &mut Self::State,
    ) -> CompilerResult<()>;
}

/// The virtual machine trait
pub trait VirtualMachine<'c> {
    /// The general [VirtualMachine] state. This is implementation specific to
    /// the VM that implements this trait. The pipeline should have no
    /// dealings with the actual state, except saving it.
    type State;

    /// Initialise [VirtualMachine::State].
    fn make_state(&mut self) -> CompilerResult<Self::State>;

    /// Run the currently generated VM
    fn run(&mut self, state: &mut Self::State) -> CompilerResult<()>;
}
