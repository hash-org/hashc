//! Hash Compiler Typecheck library file
//
// All rights reserved 2022 (c) The Hash Language authors
#![feature(map_try_insert)]
#![feature(extend_one)]
#![feature(trait_alias)]
#![feature(generic_associated_types)]
#![feature(never_type)]

pub mod error;
pub mod scope;
pub mod state;
pub mod storage;
pub mod traits;
pub mod traverse;
pub mod types;
pub mod unify;
pub mod writer;

use crate::scope::ScopeStack;
use crate::storage::GlobalStorage;
use hash_alloc::Wall;
use hash_pipeline::{sources::Sources, Checker, CompilerResult};
use hash_source::{InteractiveId, ModuleId, SourceId};
use traverse::SourceTypechecker;
use types::TypeId;
use writer::TypeWithStorage;

pub struct HashTypechecker<'c, 'w> {
    global_wall: &'w Wall<'c>,
}

impl<'c, 'w> HashTypechecker<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        Self { global_wall: wall }
    }

    fn check_interactive_statement(
        &mut self,
        interactive_id: InteractiveId,
        sources: &Sources<'c>,
        state: &mut GlobalStorage<'c, 'w>,
        interactive_state: ScopeStack,
    ) -> (CompilerResult<TypeId>, ScopeStack) {
        let wall = self.global_wall;
        let mut source_checker = SourceTypechecker::new(
            SourceId::Interactive(interactive_id),
            sources,
            state,
            interactive_state,
            wall,
        );
        let typecheck_result = source_checker.typecheck();
        let new_state = source_checker.into_source_storage().scopes;
        match typecheck_result {
            Ok(ty_id) => (Ok(ty_id), new_state),
            Err(e) => (Err(e.create_report(state)), new_state),
        }
    }
}

impl<'c, 'w> Checker<'c> for HashTypechecker<'c, 'w> {
    type State = GlobalStorage<'c, 'w>;
    fn make_state(&mut self) -> CompilerResult<Self::State> {
        Ok(GlobalStorage::new(self.global_wall))
    }

    type ModuleState = ();
    fn make_module_state(&mut self, _: &mut Self::State) -> CompilerResult<Self::ModuleState> {
        Ok(())
    }
    fn check_module(
        &mut self,
        module_id: ModuleId,
        sources: &Sources<'c>,
        state: &mut Self::State,
        _: Self::ModuleState,
    ) -> (CompilerResult<()>, Self::ModuleState) {
        let wall = self.global_wall;
        let scopes = ScopeStack::new(state);
        let mut source_checker =
            SourceTypechecker::new(SourceId::Module(module_id), sources, state, scopes, wall);
        match source_checker.typecheck() {
            Ok(_) => (Ok(()), ()),
            Err(e) => (Err(e.create_report(state)), ()),
        }
    }

    type InteractiveState = ScopeStack;
    fn make_interactive_state(
        &mut self,
        state: &mut Self::State,
    ) -> CompilerResult<Self::InteractiveState> {
        Ok(ScopeStack::new(state))
    }
    fn check_interactive(
        &mut self,
        interactive_id: InteractiveId,
        sources: &Sources<'c>,
        state: &mut Self::State,
        interactive_state: Self::InteractiveState,
    ) -> (CompilerResult<()>, Self::InteractiveState) {
        let (result, new_state) =
            self.check_interactive_statement(interactive_id, sources, state, interactive_state);

        (result.map(|_| ()), new_state)
    }

    fn check_interactive_and_return_type(
        &mut self,
        interactive_id: InteractiveId,
        sources: &Sources<'c>,
        state: &mut Self::State,
        interactive_state: Self::InteractiveState,
    ) -> (CompilerResult<String>, Self::InteractiveState) {
        let (result, new_state) =
            self.check_interactive_statement(interactive_id, sources, state, interactive_state);

        (
            result.map(|ty| {
                let ty_storage = TypeWithStorage::new(ty, state);
                ty_storage.to_string()
            }),
            new_state,
        )
    }
}
