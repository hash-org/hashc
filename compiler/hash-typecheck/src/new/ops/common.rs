// @@Docs
use hash_source::{identifier::Identifier, location::SourceLocation};
use hash_types::new::{
    data::{DataDef, DataDefId},
    defs::DefParamsId,
    environment::context::BoundVarOrigin,
    fns::{FnDef, FnDefId},
    holes::{Hole, HoleKind},
    locations::LocationTarget,
    params::ParamsId,
    pats::{Pat, PatId},
    scopes::BoundVar,
    symbols::{Symbol, SymbolData},
    terms::{Term, TermId},
    tuples::TupleTy,
    tys::{Ty, TyId, UniverseTy},
};
use hash_utils::store::{CloneStore, SequenceStore, Store};

use crate::new::{diagnostics::error::TcResult, environment::tc_env::AccessToTcEnv};

/// Common operations during typechecking.
pub trait CommonOps: AccessToTcEnv {
    /// Get a term by its ID.
    fn get_term(&self, term_id: TermId) -> Term {
        self.stores().term().get(term_id)
    }

    /// Get a type by its ID.
    fn get_ty(&self, ty_id: TyId) -> Ty {
        self.stores().ty().get(ty_id)
    }

    /// Get a pattern by its ID.
    fn get_pat(&self, pat_id: PatId) -> Pat {
        self.stores().pat().get(pat_id)
    }

    /// Get a data definition by its ID.
    fn get_data_def(&self, data_def_id: DataDefId) -> DataDef {
        self.stores().data_def().get(data_def_id)
    }

    /// Get a function definition by its ID.
    fn get_fn_def(&self, fn_def_id: FnDefId) -> FnDef {
        self.stores().fn_def().get(fn_def_id)
    }

    /// Get the location of a location target.
    fn get_location(&self, target: impl Into<LocationTarget>) -> Option<SourceLocation> {
        self.stores().location().get_location(target)
    }

    /// Get symbol data.
    fn get_symbol(&self, symbol: Symbol) -> SymbolData {
        self.stores().symbol().get(symbol)
    }

    /// Duplicate a symbol by creating a new symbol with the same name.
    fn duplicate_symbol(&self, existing_symbol: Symbol) -> Symbol {
        let existing_symbol_name = self.stores().symbol().map_fast(existing_symbol, |s| s.name);
        self.stores()
            .symbol()
            .create_with(|symbol| SymbolData { name: existing_symbol_name, symbol })
    }

    /// Create a new type.
    fn new_ty(&self, ty: Ty) -> TyId {
        self.stores().ty().create(ty)
    }

    /// Create a new term.
    fn new_term(&self, term: Term) -> TermId {
        self.stores().term().create(term)
    }

    /// Create a new pattern.
    fn new_pat(&self, pat: Pat) -> PatId {
        self.stores().pat().create(pat)
    }

    /// Create a new symbol with the given name.
    fn new_symbol(&self, name: impl Into<Identifier>) -> Symbol {
        self.stores().symbol().create_with(|symbol| SymbolData { name: Some(name.into()), symbol })
    }

    /// Create a new symbol with the given name, at the given location.
    fn new_symbol_at_location(
        &self,
        name: impl Into<Identifier>,
        location: SourceLocation,
    ) -> Symbol {
        let symbol = self.new_symbol(name);
        self.stores().location().add_location_to_target(symbol, location);
        symbol
    }

    /// Create a new internal symbol.
    fn new_fresh_symbol(&self) -> Symbol {
        self.stores().symbol().create_with(|symbol| SymbolData { name: None, symbol })
    }

    /// Create a new term hole.
    fn new_term_hole(&self) -> TermId {
        let hole_id = self.stores().hole().create_with(|id| Hole { id, kind: HoleKind::Term });
        self.stores().term().create_with(|_| Term::Hole(hole_id))
    }

    /// Create a new type hole.
    fn new_ty_hole(&self) -> TyId {
        let hole_id = self.stores().hole().create_with(|id| Hole { id, kind: HoleKind::Ty });
        self.stores().ty().create_with(|_| Ty::Hole(hole_id))
    }

    /// Create a new empty parameter list.
    fn new_empty_params(&self) -> ParamsId {
        self.stores().params().create_from_slice(&[])
    }

    /// Create a new empty definition parameter list.
    fn new_empty_def_params(&self) -> DefParamsId {
        self.stores().def_params().create_from_slice(&[])
    }

    /// Create a type of types, i.e. small `Type`.
    fn new_small_universe_ty(&self) -> TyId {
        self.stores().ty().create(Ty::Universe(UniverseTy { size: 0 }))
    }
    fn try_or_add_error<T>(&self, result: TcResult<T>) -> Option<T> {
        match result {
            Ok(t) => Some(t),
            Err(error) => {
                self.diagnostics().add_error(error);
                None
            }
        }
    }

    /// Create a large type of types, i.e. `Type(n)` for some natural number
    /// `n`.
    fn new_universe_ty(&self, n: usize) -> TyId {
        self.stores().ty().create(Ty::Universe(UniverseTy { size: n }))
    }

    /// Create a new empty tuple type.
    fn new_void_ty(&self) -> TyId {
        self.stores().ty().create(Ty::Tuple(TupleTy { data: self.new_empty_params() }))
    }

    /// Create a new variable in the given data definition's parameter list.
    fn new_var_in_data_params(&self, name: Symbol, data_def_id: DataDefId) -> TyId {
        self.new_ty(Ty::Var(BoundVar {
            name,
            origin: {
                // Here we search the params for the variable
                self.stores().data_def().map_fast(data_def_id, |data_def| {
                    self.stores().def_params().map_fast(data_def.params, |def_params| {
                        def_params
                            .iter()
                            .enumerate()
                            .find_map(|(def_param_index, def_param)| {
                                self.stores().params().map_fast(def_param.params, |params| {
                                    params.iter().enumerate().find_map(|(param_index, param)| {
                                        if param.name == name {
                                            Some(BoundVarOrigin::Data(
                                                data_def_id,
                                                (data_def.params, def_param_index),
                                                (def_param.params, param_index),
                                            ))
                                        } else {
                                            None
                                        }
                                    })
                                })
                            })
                            .unwrap_or_else(|| {
                                panic!(
                                "Could not find parameter {} provided to new_var_in_data_params {}",
                                self.env().with(name),
                                self.env().with(data_def_id),
                            )
                            })
                    })
                })
            },
        }))
    }
}

impl<T: AccessToTcEnv> CommonOps for T {}
