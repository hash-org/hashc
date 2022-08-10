//! Contains helpers to read various things stored in [crate::storage] with
//! ease.

use hash_utils::store::Store;

use crate::{
    exhaustiveness::{construct::DeconstructedCtor, deconstruct::DeconstructedPat},
    storage::{
        arguments::ArgsId,
        deconstructed::{DeconstructedCtorId, DeconstructedPatId},
        mods::ModDefId,
        nominals::NominalDefId,
        params::ParamsId,
        pats::{PatArgsId, PatId},
        primitives::{Args, ModDef, NominalDef, Params, Pat, PatArgs, Scope, Term, TrtDef},
        scope::ScopeId,
        terms::TermId,
        trts::TrtDefId,
        GlobalStorage,
    },
};

/// Helper to read various primitive constructions (from
/// [crate::storage::primitives]).
pub struct PrimitiveReader<'gs> {
    gs: &'gs GlobalStorage,
}

impl<'gs> PrimitiveReader<'gs> {
    /// Create a new [PrimitiveReader] with a given scope.
    pub fn new(gs: &'gs GlobalStorage) -> Self {
        Self { gs }
    }

    /// Get an immutable reference to the inner global storage.
    pub fn global_storage(&self) -> &GlobalStorage {
        self.gs
    }

    /// Get the term with the given [TermId].
    pub fn get_term(&self, id: TermId) -> Term {
        self.gs.term_store.get(id)
    }

    /// Get the pattern with the given [PatId].
    pub fn get_pat(&self, id: PatId) -> Pat {
        self.gs.pat_store.get(id)
    }

    /// Get the module definition with the given [ModDefId].
    pub fn get_mod_def(&self, id: ModDefId) -> ModDef {
        self.gs.mod_def_store.get(id)
    }

    /// Get the nominal definition with the given [NominalDefId].
    pub fn get_nominal_def(&self, id: NominalDefId) -> NominalDef {
        self.gs.nominal_def_store.get(id)
    }

    /// Get the scope with the given [ScopeId].
    pub fn get_scope(&self, id: ScopeId) -> Scope {
        self.gs.scope_store.get(id)
    }

    /// Get the args with the given [ArgsId].
    pub fn get_args_owned(&self, id: ArgsId) -> Args<'static> {
        self.gs.args_store.get_owned_param_list(id)
    }

    /// Get the params with the given [ParamsId].
    pub fn get_params_owned(&self, id: ParamsId) -> Params<'static> {
        self.gs.params_store.get_owned_param_list(id)
    }

    /// Get the [PatArgs] with the given [PatArgsId].
    pub fn get_pat_args_owned(&self, id: PatArgsId) -> PatArgs<'static> {
        self.gs.pat_args_store.get_owned_param_list(id)
    }

    /// Get the associated [DeconstructedPat] from [DeconstructedPatId].
    pub fn get_deconstructed_pat(&self, id: DeconstructedPatId) -> DeconstructedPat {
        self.gs.deconstructed_pat_store.get(id)
    }

    /// Get the associated [DeconstructedCtor] from [DeconstructedCtorId].
    pub fn get_deconstructed_ctor(&self, id: DeconstructedCtorId) -> DeconstructedCtor {
        self.gs.deconstructed_ctor_store.get(id)
    }

    /// Get the trait definition with the given [TrtDefId].
    pub fn get_trt_def(&self, id: TrtDefId) -> TrtDef {
        self.gs.trt_def_store.get(id)
    }
}
