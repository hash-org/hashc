// @@Docs
use hash_source::{identifier::Identifier, location::SourceLocation};
use hash_types::new::{
    args::{ArgsId, PatArgsId},
    data::{CtorDefId, CtorPat, CtorTerm, DataDef, DataDefId},
    defs::{DefArgsId, DefParamsId, DefPatArgsId},
    fns::{FnDef, FnDefId},
    holes::{Hole, HoleKind},
    locations::LocationTarget,
    params::ParamsId,
    pats::{Pat, PatId, PatListId},
    symbols::{Symbol, SymbolData},
    terms::{Term, TermId, TermListId},
    tuples::{TupleTerm, TupleTy},
    tys::{Ty, TyId, UniverseTy},
};
use hash_utils::store::{CloneStore, SequenceStore, Store};
use itertools::Itertools;

use super::bootstrap::DefinedPrimitives;
use crate::new::{diagnostics::error::TcResult, environment::tc_env::AccessToTcEnv};

/// Assert that the given term is of the given variant, and return it.
#[macro_export]
macro_rules! term_as_variant {
    ($self:expr, $term:expr, $variant:ident) => {{
        let term = $term;
        if let Term::$variant(term) = $self.get_term(term) {
            term
        } else {
            panic!("Expected term to be a {}", stringify!($variant))
        }
    }};
}

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

    /// Create a new term list.
    fn new_term_list(&self, terms: impl IntoIterator<Item = TermId>) -> TermListId {
        let terms = terms.into_iter().collect_vec();
        self.stores().term_list().create_from_slice(&terms)
    }

    /// Create a new pattern.
    fn new_pat(&self, pat: Pat) -> PatId {
        self.stores().pat().create(pat)
    }

    /// Create a new pattern list.
    fn new_pat_list(&self, pats: impl IntoIterator<Item = PatId>) -> PatListId {
        let pats = pats.into_iter().collect_vec();
        self.stores().pat_list().create_from_slice(&pats)
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

    /// Create a new empty definition argument list.
    fn new_empty_def_args(&self) -> DefArgsId {
        self.stores().def_args().create_from_slice(&[])
    }

    /// Create a new empty argument list.
    fn new_empty_args(&self) -> ArgsId {
        self.stores().args().create_from_slice(&[])
    }

    /// Create a new empty pattern argument list.
    fn new_empty_pat_args(&self) -> PatArgsId {
        self.stores().pat_args().create_from_slice(&[])
    }

    /// Create a new empty pattern definition argument list.
    fn new_empty_def_pat_args(&self) -> DefPatArgsId {
        self.stores().def_pat_args().create_from_slice(&[])
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

    /// Create a new empty tuple term.
    fn new_void_term(&self) -> TermId {
        self.stores().term().create(Term::Tuple(TupleTerm {
            data: self.new_empty_args(),
            original_ty: Some(TupleTy { data: self.new_empty_params() }),
        }))
    }

    /// Create a new variable type.
    fn new_var_ty(&self, symbol: Symbol) -> TyId {
        self.stores().ty().create(Ty::Var(symbol))
    }

    /// Access the primitive definitions.
    fn primitives(&self) -> DefinedPrimitives {
        match self.primitives_or_unset().get() {
            Some(primitives) => primitives,
            None => panic!("called primitives() before they were set"),
        }
    }

    /// Get the bool constructor for the given value.
    ///
    /// Both constructors do not take arguments.
    fn get_bool_ctor(&self, value: bool) -> CtorDefId {
        let ctor_defs =
            self.stores().data_def().map_fast(self.primitives().bool(), |bool_def| bool_def.ctors);
        match ctor_defs {
            hash_types::new::data::DataDefCtors::Defined(ctors) => {
                // Index 0 is true, 1 is false, see BootstrapOps
                let idx = if value { 0 } else { 1 };
                (ctors, idx)
            }
            hash_types::new::data::DataDefCtors::Primitive(_) => {
                panic!("Found primitive data definition for bool")
            }
        }
    }

    /// Create a boolean term of the given value.
    fn new_bool_term(&self, value: bool) -> TermId {
        self.new_term(Term::Ctor(CtorTerm {
            ctor: self.get_bool_ctor(value),
            args: self.new_empty_def_args(),
        }))
    }

    /// Create a boolean pattern of the given value.
    fn bool_pat(&self, value: bool) -> PatId {
        self.new_pat(Pat::Ctor(CtorPat {
            ctor: self.get_bool_ctor(value),
            args: self.new_empty_def_pat_args(),
        }))
    }
}

impl<T: AccessToTcEnv> CommonOps for T {}
