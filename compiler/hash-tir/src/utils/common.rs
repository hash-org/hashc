// @@Docs

use hash_source::{identifier::Identifier, location::SourceLocation};
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey, Store};

use crate::{
    args::{Arg, ArgsId, PatArgsId, PatOrCapture, SomeArgId, SomeArgsId},
    data::{DataDef, DataDefId, DataTy},
    environment::env::AccessToEnv,
    fns::{FnDef, FnDefId},
    holes::Hole,
    locations::LocationTarget,
    params::{Param, ParamId, ParamIndex, ParamsId},
    pats::{Pat, PatId, PatListId},
    scopes::StackMemberId,
    symbols::{Symbol, SymbolData},
    terms::{Term, TermId, TermListId},
    tuples::{TupleTerm, TupleTy},
    tys::{Ty, TyId, UniverseTy},
};

/// Assert that the given term is of the given variant, and return it.
#[macro_export]
macro_rules! term_as_variant {
    ($self:expr, $term:expr, $variant:ident) => {{
        let term = $term;
        if let $crate::terms::Term::$variant(term) = term {
            term
        } else {
            panic!("Expected term to be a {}", stringify!($variant))
        }
    }};
}

/// Assert that the given type is of the given variant, and return it.
#[macro_export]
macro_rules! ty_as_variant {
    ($self:expr, $ty:expr, $variant:ident) => {{
        let ty = $ty;
        if let $crate::tys::Ty::$variant(ty) = ty {
            ty
        } else {
            panic!("Expected type to be a {}", stringify!($variant))
        }
    }};
}

pub trait CommonUtils: AccessToEnv {
    /// Check whether the given term is a void term (i.e. empty tuple).
    fn term_is_void(&self, term_id: TermId) -> bool {
        matches! {
          self.stores().term().get(term_id),
          Term::Tuple(tuple_term) if tuple_term.data.is_empty()
        }
    }

    /// Try to get the parameter of the given parameters ID and index which is
    /// either symbolic or positional.
    fn try_get_param_by_index(&self, params_id: ParamsId, index: ParamIndex) -> Option<Param> {
        match index {
            ParamIndex::Name(name) => self.stores().params().map_fast(params_id, |params| {
                params.iter().find_map(|x| {
                    if self.stores().symbol().get(x.name).name? == name {
                        Some(*x)
                    } else {
                        None
                    }
                })
            }),
            ParamIndex::Position(i) => {
                self.stores().params().map_fast(params_id, |params| params.get(i).copied())
            }
        }
    }

    /// Get the parameter of the given parameters ID and index which is
    /// either symbolic or positional.
    ///
    /// This will panic if the index does not exist.
    fn get_param_by_index(&self, params_id: ParamsId, index: ParamIndex) -> Param {
        self.try_get_param_by_index(params_id, index).unwrap_or_else(|| {
            panic!(
                "Parameter with name `{}` does not exist in `{}`",
                index,
                self.env().with(params_id)
            )
        })
    }

    /// Create a new symbol with the given name.
    fn new_symbol(&self, name: impl Into<Identifier>) -> Symbol {
        self.stores().symbol().create_with(|symbol| SymbolData { name: Some(name.into()), symbol })
    }

    /// Create a new symbol from the given parameter index.
    fn new_symbol_from_param_index(&self, index: ParamIndex) -> Symbol {
        match index {
            ParamIndex::Name(name) => self.new_symbol(name),
            ParamIndex::Position(i) => self.new_symbol(i),
        }
    }

    /// Create a new empty parameter list.
    fn new_empty_params(&self) -> ParamsId {
        self.stores().params().create_from_slice(&[])
    }

    /// Get a term by its ID.
    fn get_term(&self, term_id: TermId) -> Term {
        self.stores().term().get(term_id)
    }

    /// Map a term by its ID.
    fn map_term<T>(&self, term_id: TermId, f: impl FnOnce(&Term) -> T) -> T {
        self.stores().term().map(term_id, f)
    }

    fn map_term_list<T>(&self, term_list_id: TermListId, f: impl FnOnce(&[TermId]) -> T) -> T {
        self.stores().term_list().map(term_list_id, f)
    }

    fn map_pat_list<T>(&self, pat_list_id: PatListId, f: impl FnOnce(&[PatOrCapture]) -> T) -> T {
        self.stores().pat_list().map(pat_list_id, f)
    }

    /// Get a type by its ID.
    fn get_ty(&self, ty_id: TyId) -> Ty {
        self.stores().ty().get(ty_id)
    }

    /// Map a type by its ID.
    fn map_ty<T>(&self, ty_id: TyId, f: impl FnOnce(&Ty) -> T) -> T {
        self.stores().ty().map(ty_id, f)
    }

    /// Map args by their IDs.
    fn map_args<T>(&self, args_id: ArgsId, f: impl FnOnce(&[Arg]) -> T) -> T {
        self.stores().args().map(args_id, f)
    }

    /// Map params by their IDs.
    fn map_params<T>(&self, params_id: ParamsId, f: impl FnOnce(&[Param]) -> T) -> T {
        self.stores().params().map(params_id, f)
    }

    fn map_pat<T>(&self, pat_id: PatId, f: impl FnOnce(&Pat) -> T) -> T {
        self.stores().pat().map(pat_id, f)
    }

    /// Get a type by its ID.

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

    /// Get the name of a stack member
    fn get_stack_member_name(&self, stack_member_id: StackMemberId) -> Symbol {
        self.stores()
            .stack()
            .modify_fast(stack_member_id.0, |stack| stack.members[stack_member_id.1].name)
    }

    /// Get the index target of an argument
    fn get_arg_index(&self, arg_id: impl Into<SomeArgId>) -> ParamIndex {
        let arg_id: SomeArgId = arg_id.into();
        match arg_id.0 {
            SomeArgsId::PatArgs(pat_args_id) => {
                self.stores().pat_args().map_fast(pat_args_id, |args| args[arg_id.1].target)
            }
            SomeArgsId::Args(args_id) => {
                self.stores().args().map_fast(args_id, |args| args[arg_id.1].target)
            }
        }
    }

    /// Make a parameter name from an argument index
    fn make_param_name_from_arg_index(&self, index: ParamIndex) -> Symbol {
        match index {
            ParamIndex::Name(name) => self.new_symbol(name),
            ParamIndex::Position(i) => self.new_symbol(i.to_string()),
        }
    }

    /// Get the identifier name of a parameter
    fn get_param_name_ident(&self, param_id: ParamId) -> Option<Identifier> {
        let sym = self.get_param_name(param_id);
        self.stores().symbol().map_fast(sym, |s| s.name)
    }

    /// Get the index target of a parameter
    fn get_param_index(&self, param_id: ParamId) -> ParamIndex {
        let sym = self.get_param_name(param_id);
        self.stores().symbol().map_fast(sym, |s| {
            s.name.map(ParamIndex::Name).unwrap_or(ParamIndex::Position(param_id.1))
        })
    }

    /// Get the name of a parameter
    fn get_param_name(&self, param_id: ParamId) -> Symbol {
        self.stores().params().map_fast(param_id.0, |params| params[param_id.1].name)
    }

    /// Get the default value of a parameter, if any
    fn get_param_default(&self, param_id: ParamId) -> Option<TermId> {
        self.stores().params().map_fast(param_id.0, |params| params[param_id.1].default)
    }

    /// Duplicate a symbol by creating a new symbol with the same name.
    fn duplicate_symbol(&self, existing_symbol: Symbol) -> Symbol {
        let existing_symbol_name = self.stores().symbol().map_fast(existing_symbol, |s| s.name);
        self.stores()
            .symbol()
            .create_with(|symbol| SymbolData { name: existing_symbol_name, symbol })
    }

    /// Create a new type.
    fn new_ty(&self, ty: impl Into<Ty>) -> TyId {
        let ty = ty.into();
        let location = match ty {
            Ty::Eval(term) => self.get_location(term),
            Ty::Var(v) => self.get_location(v),
            _ => None,
        };
        let created = self.stores().ty().create(ty);
        if let Some(location) = location {
            self.stores().location().add_location_to_target(created, location);
        }
        created
    }

    /// Create a new term.
    fn new_term(&self, term: impl Into<Term>) -> TermId {
        let term = term.into();
        let location = match term {
            Term::Ty(ty) => self.get_location(ty),
            Term::FnRef(f) => self.get_location(f),
            Term::Var(v) => self.get_location(v),
            _ => None,
        };
        let created = self.stores().term().create(term);
        if let Some(location) = location {
            self.stores().location().add_location_to_target(created, location);
        }
        created
    }

    /// Create a new term.
    fn new_term_from(&self, term: impl Into<Term>) -> TermId {
        self.stores().term().create(term.into())
    }

    /// Create a new term list.
    fn new_term_list(&self, terms: impl IntoIterator<Item = TermId>) -> TermListId {
        let terms = terms.into_iter().collect::<Vec<_>>();
        self.stores().term_list().create_from_slice(&terms)
    }

    /// Create a new pattern.
    fn new_pat(&self, pat: impl Into<Pat>) -> PatId {
        self.stores().pat().create(pat.into())
    }

    /// Create a new pattern list.
    fn new_pat_list(&self, pats: impl IntoIterator<Item = PatOrCapture>) -> PatListId {
        let pats = pats.into_iter().collect::<Vec<_>>();
        self.stores().pat_list().create_from_slice(&pats)
    }

    /// Create a new internal symbol.
    fn new_fresh_symbol(&self) -> Symbol {
        self.stores().symbol().create_with(|symbol| SymbolData { name: None, symbol })
    }

    fn new_hole(&self) -> Hole {
        Hole(self.new_fresh_symbol())
    }

    /// Create a new term hole.
    fn new_term_hole(&self) -> TermId {
        self.stores().term().create_with(|_| Term::Hole(self.new_hole()))
    }

    /// Create a new type hole.
    fn new_ty_hole(&self) -> TyId {
        self.stores().ty().create_with(|_| Ty::Hole(self.new_hole()))
    }

    /// Create a new empty argument list.
    fn new_empty_args(&self) -> ArgsId {
        self.stores().args().create_from_slice(&[])
    }

    /// Create a new positional parameter list with the given types.
    fn new_params(&self, types: &[TyId]) -> ParamsId {
        self.stores().params().create_from_iter_with(
            types
                .iter()
                .copied()
                .enumerate()
                .map(|(i, ty)| move |id| Param { id, name: self.new_symbol(i), ty, default: None }),
        )
    }

    /// Create a new positional argument list with the given types.
    fn new_args(&self, values: &[TermId]) -> ArgsId {
        self.stores().args().create_from_iter_with(
            values
                .iter()
                .copied()
                .enumerate()
                .map(|(i, value)| move |id| Arg { id, target: ParamIndex::Position(i), value }),
        )
    }

    /// Create a new data type with no arguments.
    fn new_data_ty(&self, data_def: DataDefId) -> TyId {
        self.stores().ty().create(Ty::Data(DataTy { data_def, args: self.new_empty_args() }))
    }

    /// Create a new empty pattern argument list.
    fn new_empty_pat_args(&self) -> PatArgsId {
        self.stores().pat_args().create_from_slice(&[])
    }

    /// Create a type of types, i.e. small `Type`.
    fn new_small_universe_ty(&self) -> TyId {
        self.stores().ty().create(Ty::Universe(UniverseTy { size: 0 }))
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
        self.stores().term().create(Term::Tuple(TupleTerm { data: self.new_empty_args() }))
    }

    /// Create a new variable type.
    fn new_var_ty(&self, symbol: Symbol) -> TyId {
        self.stores().ty().create(Ty::Var(symbol))
    }

    /// Try to use the given term as a type.
    fn try_use_term_as_ty(&self, term: TermId) -> Option<TyId> {
        match self.get_term(term) {
            Term::Var(var) => Some(self.new_ty(var)),
            Term::Ty(ty) => Some(ty),
            Term::Hole(hole) => Some(self.new_ty(hole)),
            _ => None,
        }
    }

    /// Try to use the given term as a type, or defer to a `Ty::Eval`.
    fn use_term_as_ty(&self, term: TermId) -> TyId {
        match self.try_use_term_as_ty(term) {
            Some(ty) => ty,
            None => self.new_ty(Ty::Eval(term)),
        }
    }

    /// Try to use the given type as a term.
    fn use_ty_as_term(&self, ty: TyId) -> TermId {
        match self.get_ty(ty) {
            Ty::Var(var) => self.new_term(var),
            Ty::Hole(hole) => self.new_term(hole),
            Ty::Eval(term) => match self.try_use_term_as_ty(term) {
                Some(ty) => self.use_ty_as_term(ty),
                None => term,
            },
            _ => self.new_term(ty),
        }
    }
}

impl<T: AccessToEnv + ?Sized> CommonUtils for T {}
