//! The Hash typechecker.
//!
//! This brings light to the world by ensuring the correctness of the crude and
//! dangerous Hash program that is given as input to the compiler.
//!
//! @@Todo(kontheocharis): write docs about the stages of the typechecker.

#![feature(generic_associated_types)]

use diagnostics::reporting::TcErrorWithStorage;
use hash_pipeline::{traits::Tc, CompilerResult};
use storage::{
    core::CoreDefs, AccessToStorage, AccessToStorageMut, GlobalStorage, LocalStorage, StorageRefMut,
};
use traverse::TcVisitor;

use crate::fmt::PrepareForFormatting;

pub mod diagnostics;
pub mod fmt;
pub mod ops;
pub mod storage;
pub mod traverse;

/// The entry point of the typechecker.
pub struct TcImpl;

/// Contains global typechecker state, used for the [Tc] implementation below.
#[derive(Debug)]
pub struct TcState {
    pub global_storage: GlobalStorage,
    pub core_defs: CoreDefs,
    pub prev_local_storage: LocalStorage,
}

impl TcState {
    /// Create a new [TcState].
    pub fn new() -> Self {
        let mut global_storage = GlobalStorage::new();
        let core_defs = CoreDefs::new(&mut global_storage);
        let local_storage = LocalStorage::new(&mut global_storage);
        Self { global_storage, core_defs, prev_local_storage: local_storage }
    }
}

impl Default for TcState {
    fn default() -> Self {
        Self::new()
    }
}

impl Tc<'_> for TcImpl {
    type State = TcState;

    fn make_state(&mut self) -> CompilerResult<Self::State> {
        Ok(TcState::new())
    }

    fn check_interactive(
        &mut self,
        interactive_id: hash_source::InteractiveId,
        sources: &hash_pipeline::sources::Sources,
        state: &mut Self::State,
        _job_params: &hash_pipeline::settings::CompilerJobParams,
    ) -> CompilerResult<()> {
        // Instantiate a visitor with the source and visit the source, using the
        // previous local storage.
        let mut storage = StorageRefMut {
            global_storage: &mut state.global_storage,
            core_defs: &state.core_defs,
            local_storage: &mut state.prev_local_storage,
        };
        let mut tc_visitor = TcVisitor::new_in_source(
            storage.storages_mut(),
            hash_source::SourceId::Interactive(interactive_id),
            sources,
        );
        match tc_visitor.visit_source() {
            Ok(source_term) => {
                println!("{}", source_term.for_formatting(storage.global_storage()));

                Ok(())
            }
            Err(error) => {
                // Turn the error into a report:
                let err_with_storage = TcErrorWithStorage { error, storage: storage.storages() };
                Err(vec![err_with_storage.into()])
            }
        }
    }

    fn check_module(
        &mut self,
        module_id: hash_source::ModuleId,
        sources: &hash_pipeline::sources::Sources,
        state: &mut Self::State,
        _job_params: &hash_pipeline::settings::CompilerJobParams,
    ) -> CompilerResult<()> {
        // Instantiate a visitor with the source and visit the source, using a new local
        // storage.
        let mut local_storage = LocalStorage::new(&mut state.global_storage);
        let mut storage = StorageRefMut {
            global_storage: &mut state.global_storage,
            core_defs: &state.core_defs,
            local_storage: &mut local_storage,
        };
        let mut tc_visitor = TcVisitor::new_in_source(
            storage.storages_mut(),
            hash_source::SourceId::Module(module_id),
            sources,
        );

        match tc_visitor.visit_source() {
            Ok(_) => Ok(()),
            Err(error) => {
                // Turn the error into a report:
                let err_with_storage = TcErrorWithStorage { error, storage: storage.storages() };
                Err(vec![err_with_storage.into()])
            }
        }
    }
}
