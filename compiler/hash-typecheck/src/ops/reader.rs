//! Contains helpers to read various things stored in [crate::storage] with
//! ease.

use crate::{
    exhaustiveness::{construct::Constructor, deconstruct::DeconstructedPat},
    storage::{
        primitives::{
            Args, ArgsId, ConstructorId, DeconstructedPatId, ModDef, ModDefId, NominalDef,
            NominalDefId, Params, ParamsId, Pat, PatArgs, PatArgsId, PatId, Scope, ScopeId, Term,
            TermId, TrtDef, TrtDefId,
        },
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
    pub fn get_term(&self, id: TermId) -> &Term {
        self.gs.term_store.get(id)
    }

    /// Get the pattern with the given [PatId].
    pub fn get_pat(&self, id: PatId) -> &Pat {
        self.gs.pat_store.get(id)
    }

    /// Get the module definition with the given [ModDefId].
    pub fn get_mod_def(&self, id: ModDefId) -> &ModDef {
        self.gs.mod_def_store.get(id)
    }

    /// Get the nominal definition with the given [NominalDefId].
    pub fn get_nominal_def(&self, id: NominalDefId) -> &NominalDef {
        self.gs.nominal_def_store.get(id)
    }

    /// Get the scope with the given [ScopeId].
    pub fn get_scope(&self, id: ScopeId) -> &Scope {
        self.gs.scope_store.get(id)
    }

    /// Get the args with the given [ArgsId].
    pub fn get_args(&self, id: ArgsId) -> &Args {
        self.gs.args_store.get(id)
    }

    /// Get the params with the given [ParamsId].
    pub fn get_params(&self, id: ParamsId) -> &Params {
        self.gs.params_store.get(id)
    }

    /// Get the [PatArgs] with the given [PatArgsId].
    pub fn get_pat_args(&self, id: PatArgsId) -> &PatArgs {
        self.gs.pat_args_store.get(id)
    }

    /// Get the associated [DeconstructedPat] from [DeconstructedPatId].
    pub fn get_deconstructed_pat(&self, id: DeconstructedPatId) -> DeconstructedPat {
        self.gs.deconstructed_pat_store.get(id)
    }

    /// Get the associated [Constructor] from [ConstructorId].
    pub fn get_ctor(&self, id: ConstructorId) -> Constructor {
        self.gs.constructor_store.get(id)
    }

    /// Get the trait definition with the given [TrtDefId].
    pub fn get_trt_def(&self, id: TrtDefId) -> &TrtDef {
        self.gs.trt_def_store.get(id)
    }
}
