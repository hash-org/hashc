//! Contains helpers to read various things stored in [crate::storage] with
//! ease.


use crate::storage::{
    primitives::{
        Args, ArgsId, ModDef, ModDefId, NominalDef, NominalDefId, Params, ParamsId, Scope, ScopeId,
        Term, TermId, TrtDef, TrtDefId,
    },
    GlobalStorage,
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
    pub fn get_term(&self, term_id: TermId) -> &Term {
        self.gs.term_store.get(term_id)
    }

    /// Get the module definition with the given [ModDefId].
    pub fn get_mod_def(&self, mod_def_id: ModDefId) -> &ModDef {
        self.gs.mod_def_store.get(mod_def_id)
    }

    /// Get the nominal definition with the given [NominalDefId].
    pub fn get_nominal_def(&self, nominal_def_id: NominalDefId) -> &NominalDef {
        self.gs.nominal_def_store.get(nominal_def_id)
    }

    /// Get the scope with the given [ScopeId].
    pub fn get_scope(&self, scope_id: ScopeId) -> &Scope {
        self.gs.scope_store.get(scope_id)
    }

    /// Get the args with the given [ArgsId].
    pub fn get_args(&self, args_id: ArgsId) -> &Args {
        self.gs.args_store.get(args_id)
    }

    /// Get the params with the given [ParamsId].
    pub fn get_params(&self, params_id: ParamsId) -> &Params {
        self.gs.params_store.get(params_id)
    }

    /// Get the trait definition with the given [TrtDefId].
    pub fn get_trt_def(&self, trt_def_id: TrtDefId) -> &TrtDef {
        self.gs.trt_def_store.get(trt_def_id)
    }
}
