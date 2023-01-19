//! Contains helpers to read various things stored in [crate::storage] with
//! ease.

use hash_tir::{
    args::{Args, ArgsId},
    mods::{ModDef, ModDefId},
    nominals::{NominalDef, NominalDefId},
    params::{Params, ParamsId},
    pats::{Pat, PatArgs, PatArgsId, PatId},
    scope::{Scope, ScopeId},
    terms::{Term, TermId, TermListId},
    trts::{TrtDef, TrtDefId},
};
use hash_utils::store::{CloneStore, SequenceStore, Store};

use crate::{
    exhaustiveness::{construct::DeconstructedCtor, deconstruct::DeconstructedPat},
    storage::{
        exhaustiveness::{DeconstructedCtorId, DeconstructedPatId},
        AccessToStorage, StorageRef,
    },
};

/// Helper to read data structures that are used across the typechecker.
pub struct PrimitiveReader<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for PrimitiveReader<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> PrimitiveReader<'tc> {
    /// Create a new [PrimitiveReader] with a given scope.
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Get the term with the given [TermId].
    pub fn get_term(&self, id: TermId) -> Term {
        self.term_store().get(id)
    }

    /// Get the pattern with the given [PatId].
    pub fn get_pat(&self, id: PatId) -> Pat {
        self.pat_store().get(id)
    }

    /// Get the module definition with the given [ModDefId].
    pub fn get_mod_def(&self, id: ModDefId) -> ModDef {
        self.mod_def_store().get(id)
    }

    /// Get the nominal definition with the given [NominalDefId].
    pub fn get_nominal_def(&self, id: NominalDefId) -> NominalDef {
        self.nominal_def_store().get(id)
    }

    /// Get the trait definition with the given [TrtDefId].
    pub fn get_trt_def(&self, id: TrtDefId) -> TrtDef {
        self.trt_def_store().get(id)
    }

    /// Get an owned copy of the scope with the given [ScopeId].
    pub fn get_scope_copy(&self, id: ScopeId) -> Scope {
        self.scope_store().map_fast(id, |scope| scope.duplicate())
    }

    /// Get the args with the given [ArgsId].
    pub fn get_args_owned(&self, id: ArgsId) -> Args<'static> {
        self.args_store().get_owned_param_list(id)
    }

    /// Get the associated terms with the given [TermListId].
    pub fn get_term_list_owned(&self, id: TermListId) -> Vec<TermId> {
        self.term_list_store().get_vec(id)
    }

    /// Get the params with the given [ParamsId].
    pub fn get_params_owned(&self, id: ParamsId) -> Params<'static> {
        self.params_store().get_owned_param_list(id)
    }

    /// Get the [PatArgs] with the given [PatArgsId].
    pub fn get_pat_args_owned(&self, id: PatArgsId) -> PatArgs<'static> {
        self.pat_args_store().get_owned_param_list(id)
    }

    /// Get the associated [DeconstructedPat] from [DeconstructedPatId].
    pub fn get_deconstructed_pat(&self, id: DeconstructedPatId) -> DeconstructedPat {
        self.deconstructed_pat_store().get(id)
    }

    /// Get the associated [DeconstructedCtor] from [DeconstructedPatId].
    pub fn get_deconstructed_pat_ctor(&self, id: DeconstructedPatId) -> DeconstructedCtor {
        let pat = self.deconstructed_pat_store().get(id);
        self.constructor_store().get(pat.ctor)
    }

    /// Get the associated [DeconstructedCtor] from [DeconstructedCtorId].
    pub fn get_deconstructed_ctor(&self, id: DeconstructedCtorId) -> DeconstructedCtor {
        self.constructor_store().get(id)
    }
}
