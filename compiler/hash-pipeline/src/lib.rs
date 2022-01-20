//! Hash Compiler pipeline implementation. The pipeline is a abstract representation
//! of the compiler flow managing the compiling steps like parsing, typechecking, optimisation
//! passes, etc. The pipeline is used to abstract away the idea of depending on specific
//! implementations of the parser or typechecker and just use a common trait
//! interface that can be used. This file also has definitions for how to access
//! sources whether module or interactive.
//!
//! All rights reserved 2022 (c) The Hash Language authors

pub mod fs;
pub mod sources;

use hash_reporting::reporting::Report;
use hash_source::{InteractiveId, ModuleId, SourceId};
use hash_utils::timed;
use sources::Sources;

pub type CompilerResult<T> = Result<T, Report>;

/// The [Parser] represents an abstract parser that can parse all aspects of the Hash programming
/// language.
pub trait Parser<'c> {
    /// Given a [SourceId], parse the current job and append any parsed modules to the
    /// provided sources parameter. On success, the function returns nothing and on
    /// failure, the stage provides a generated diagnostics [Report].
    fn parse(&mut self, target: SourceId, sources: &mut Sources<'c>) -> CompilerResult<()>;
}

/// The [Checker] represents an abstract type checker that implements all the specified
/// typechecking methods and internally performs some kind of typechecking operations.
/// The methods [Checker::check_module] and [Checker::check_interactive] will return
/// a unit on success, or a generated diagnostic error report which can be displayed
/// and printed by the user of the pipeline. Both functions modify the states of the
/// checker and return them regardless of error, both states are considered to be the
/// new states and should be set in the compiler pipeline.
pub trait Checker<'c> {
    /// The general [Checker] state. This is implementation specific to the
    /// typechecker that implements this trait. The pipeline should have no
    /// dealings with the actual state, except saving it.
    type State;

    /// Make the general [Checker::State].
    fn make_state(&mut self) -> CompilerResult<Self::State>;

    /// The module typechecker state.
    type ModuleState;
    fn make_module_state(&mut self, state: &mut Self::State) -> CompilerResult<Self::ModuleState>;

    /// The interactive [Checker] state.
    type InteractiveState;

    /// Create an interactive [Checker] state.
    fn make_interactive_state(
        &mut self,
        state: &mut Self::State,
    ) -> CompilerResult<Self::InteractiveState>;

    /// Given a [InteractiveId], check the interactive statement with the specific rules
    /// that are applied in interactive rules. The function accepts the previous [Checker]
    /// state and previous [Checker::InteractiveState].
    fn check_interactive(
        &mut self,
        interactive_id: InteractiveId,
        sources: &Sources<'c>,
        state: &mut Self::State,
        interactive_state: Self::InteractiveState,
    ) -> (CompilerResult<()>, Self::InteractiveState);

    /// Check a interactive statement, and return a [String] representation of the
    /// resultant type
    fn check_interactive_and_return_type(
        &mut self,
        interactive_id: InteractiveId,
        sources: &Sources<'c>,
        state: &mut Self::State,
        interactive_state: Self::InteractiveState,
    ) -> (CompilerResult<String>, Self::InteractiveState);

    /// Given a [ModuleId], check the module. The function accepts the previous [Checker]
    /// state and [Checker::ModuleState]
    fn check_module(
        &mut self,
        module_id: ModuleId,
        sources: &Sources<'c>,
        state: &mut Self::State,
        module_state: Self::ModuleState,
    ) -> (CompilerResult<()>, Self::ModuleState);
}

/// The Hash Compiler interface. This interface allows a caller to create a
/// [Compiler] with the specified components. This allows external tinkerers
/// to add their own implementations of each compiler stage with relative ease
/// instead of having to scratch their heads.
pub struct Compiler<P, C> {
    /// The parser stage of the compiler.
    parser: P,
    /// The typechecking stage of the compiler.
    checker: C,
}

/// The [CompilerState] holds all the information and state of the compiler instance.
/// Each stage of the compiler contains a `State` type parameter which the compiler stores
/// so that incremental executions of the compiler are possible.
///
/// @@Future: Compiler metrics.
pub struct CompilerState<'c, C: Checker<'c>> {
    /// The collected workspace sources for the current job.
    pub sources: Sources<'c>,
    /// The typechecker state.
    pub checker_state: C::State,
    /// The interactive typechecker state. This mainly differs from the
    /// `module_checker_stage` by dealing with scopes slightly differently than module
    /// scope.
    pub checker_interactive_state: C::InteractiveState,
    /// The module checker stage.
    pub checker_module_state: C::ModuleState,
}

impl<'c, P, C> Compiler<P, C>
where
    P: Parser<'c>,
    C: Checker<'c>,
{
    /// Create a new instance of a [Compiler] with the provided parser and
    /// typechecker implementations.
    pub fn new(parser: P, checker: C) -> Self {
        Self { parser, checker }
    }

    /// Create a compiler state to accompany with compiler execution. Internally, this
    /// calls the [Checker] state making functions and saves it into the created
    /// [CompilerState].
    pub fn create_state(&mut self) -> CompilerResult<CompilerState<'c, C>> {
        let sources = Sources::new();
        let mut checker_state = self.checker.make_state()?;
        let checker_interactive_state = self.checker.make_interactive_state(&mut checker_state)?;
        let checker_module_state = self.checker.make_module_state(&mut checker_state)?;

        Ok(CompilerState {
            sources,
            checker_state,
            checker_interactive_state,
            checker_module_state,
        })
    }

    /// Run a interactive job with the provided [InteractiveId] pointing to the
    /// interpreted command to execute.
    pub fn run_interactive(
        &mut self,
        interactive_id: InteractiveId,
        compiler_state: CompilerState<'c, C>,
    ) -> (CompilerResult<()>, CompilerState<'c, C>) {
        let (result, state) = self.run_interactive_and_return_type(interactive_id, compiler_state);
        (result.map(|_| ()), state)
    }

    /// Function to invoke a parsing job of a specified [SourceId].
    pub fn parse_source(&mut self, id: SourceId, sources: &mut Sources<'c>) -> CompilerResult<()> {
        self.parser.parse(id, sources)
    }

    pub fn run_interactive_and_return_type(
        &mut self,
        interactive_id: InteractiveId,
        mut compiler_state: CompilerState<'c, C>,
    ) -> (CompilerResult<String>, CompilerState<'c, C>) {
        // Parsing
        let parse_result = self.parse_source(
            SourceId::Interactive(interactive_id),
            &mut compiler_state.sources,
        );

        if let Err(err) = parse_result {
            return (Err(err), compiler_state);
        }

        // Typechecking
        let (result, checker_interactive_state) = self.checker.check_interactive_and_return_type(
            interactive_id,
            &compiler_state.sources,
            &mut compiler_state.checker_state,
            compiler_state.checker_interactive_state,
        );
        compiler_state.checker_interactive_state = checker_interactive_state;
        (result, compiler_state)
    }

    /// Run a module job with the provided [ModuleId] pointing to the entry point
    /// of the current job. Typically, the entry point is the first module that's
    /// passed from commandline arguments.
    pub fn run_module(
        &mut self,
        module_id: ModuleId,
        mut compiler_state: CompilerState<'c, C>,
    ) -> (CompilerResult<()>, CompilerState<'c, C>) {
        // Parsing
        let result = timed(
            || {
                self.parser
                    .parse(SourceId::Module(module_id), &mut compiler_state.sources)
            },
            log::Level::Debug,
            |elapsed| println!("parse: {:?}", elapsed),
        );

        if let Err(err) = result {
            return (Err(err), compiler_state);
        }

        // Typechecking
        timed(
            || {
                let (result, checker_module_state) = self.checker.check_module(
                    module_id,
                    &compiler_state.sources,
                    &mut compiler_state.checker_state,
                    compiler_state.checker_module_state,
                );

                compiler_state.checker_module_state = checker_module_state;
                (result, compiler_state)
            },
            log::Level::Debug,
            |elapsed| println!("typecheck: {:?}", elapsed),
        )
    }
}
