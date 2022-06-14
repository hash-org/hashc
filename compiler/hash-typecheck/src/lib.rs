//! The Hash typecheker.
//!
//! This brings light to the world by ensuring the correctness of the crude and dangerous Hash
//! program that is given as input to the compiler.
//!
//! @@Todo(kontheocharis): write docs about the stages of the typechecker.
use hash_pipeline::{Checker, CompilerResult};

pub mod error;
pub mod fmt;
pub mod infer;
pub mod ops;
pub mod storage;

/// The entry point of the typechecker.
///
/// @@Incomplete(kontheocharis): for now a no-op.
pub struct Typechecker;

// @@Incomplete(kontheocharis): Dummy implementation so that the compiler runs:
impl Checker<'_> for Typechecker {
    type State = ();

    fn make_state(&mut self) -> CompilerResult<Self::State> {
        Ok(())
    }

    type ModuleState = ();

    fn make_module_state(&mut self, _state: &mut Self::State) -> CompilerResult<Self::ModuleState> {
        Ok(())
    }

    type InteractiveState = ();

    fn make_interactive_state(
        &mut self,
        _state: &mut Self::State,
    ) -> CompilerResult<Self::InteractiveState> {
        Ok(())
    }

    fn check_interactive(
        &mut self,
        _interactive_id: hash_source::InteractiveId,
        _sources: &hash_pipeline::sources::Sources,
        _state: &mut Self::State,
        _interactive_state: Self::InteractiveState,
    ) -> (CompilerResult<String>, Self::InteractiveState) {
        (Ok("Typechecking not implemented".to_string()), ())
    }

    fn check_module(
        &mut self,
        _module_id: hash_source::ModuleId,
        _sources: &hash_pipeline::sources::Sources,
        _state: &mut Self::State,
        _module_state: Self::ModuleState,
    ) -> (CompilerResult<()>, Self::ModuleState) {
        (Ok(()), ())
    }
}
