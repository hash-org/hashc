// @@Docs

use hash_source::{
    identifier::{Identifier, IDENTS},
    location::Span,
};
use hash_storage::store::{statics::StoreId, SequenceStore, Store};
use hash_utils::stream_less_writeln;

use super::traversing::Atom;
use crate::{
    args::{SomeArgId, SomeArgsId},
    environment::env::AccessToEnv,
    holes::Hole,
    locations::LocationTarget,
    params::{Param, ParamId, ParamIndex, ParamsId},
    scopes::StackMemberId,
    symbols::{Symbol, SymbolData},
    terms::{Term, TermId},
    tys::{Ty, TyId},
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
    /// Get the location of a location target.
    fn get_location(&self, target: impl Into<LocationTarget>) -> Option<Span> {
        self.stores().location().get_location(target)
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

    /// Get the name of the given symbol. If the symbol has no name, return the
    /// underscore symbol.
    fn symbol_name(&self, symbol: Symbol) -> Identifier {
        self.stores().symbol().map_fast(symbol, |s| s.name.unwrap_or(IDENTS.underscore))
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
        let (ast_info, location) = match ty {
            Ty::Eval(term) => {
                (self.stores().ast_info().terms().get_node_by_data(term), self.get_location(term))
            }
            Ty::Var(v) => (None, self.get_location(v)),
            _ => (None, None),
        };
        let created = self.stores().ty().create(ty);
        if let Some(location) = location {
            self.stores().location().add_location_to_target(created, location);
        }
        if let Some(ast_info) = ast_info {
            self.stores().ast_info().tys().insert(ast_info, created);
        }
        created
    }

    /// Create a new term.
    fn new_term(&self, term: impl Into<Term>) -> TermId {
        let term = term.into();
        let (ast_info, location) = match term {
            Term::Ty(ty) => {
                (self.stores().ast_info().tys().get_node_by_data(ty), self.get_location(ty))
            }
            Term::FnRef(f) => {
                (self.stores().ast_info().fn_defs().get_node_by_data(f), self.get_location(f))
            }
            Term::Var(v) => (None, self.get_location(v)),
            _ => (None, None),
        };
        let created = self.stores().term().create(term);
        if let Some(location) = location {
            self.stores().location().add_location_to_target(created, location);
        }
        if let Some(ast_info) = ast_info {
            self.stores().ast_info().terms().insert(ast_info, created);
        }
        created
    }

    /// Create a new expected type for typing the given term.
    fn new_expected_ty_of_ty(&self, ty: TyId, ty_of_ty: TyId) -> TyId {
        self.stores().location().copy_location(ty, ty_of_ty);
        if let Some(ast_info) = self.stores().ast_info().tys().get_node_by_data(ty) {
            self.stores().ast_info().tys().insert(ast_info, ty_of_ty);
        }
        ty_of_ty
    }

    /// Create a new term that inherits location and AST info from the given
    /// term.
    fn new_term_from(&self, source: TermId, term: impl Into<Term>) -> TermId {
        let created = self.new_term(term);
        self.stores().location().copy_location(source, created);
        if let Some(ast_info) = self.stores().ast_info().terms().get_node_by_data(source) {
            self.stores().ast_info().terms().insert(ast_info, created);
        }
        created
    }

    /// Create a new expected type for typing the given term.
    fn new_expected_ty_of(&self, atom: impl Into<Atom>, ty: TyId) -> TyId {
        let atom: Atom = atom.into();
        let (ast_info, location) = match atom {
            Atom::Term(origin_term) => match origin_term.value() {
                Term::Ty(ty) => {
                    (self.stores().ast_info().tys().get_node_by_data(ty), self.get_location(ty))
                }
                Term::FnRef(f) => {
                    (self.stores().ast_info().fn_defs().get_node_by_data(f), self.get_location(f))
                }
                Term::Var(v) => (None, self.get_location(v)),
                _ => (
                    self.stores().ast_info().terms().get_node_by_data(origin_term),
                    self.stores().location().get_location(origin_term),
                ),
            },
            Atom::Ty(origin_ty) => (
                self.stores().ast_info().tys().get_node_by_data(origin_ty),
                self.stores().location().get_location(origin_ty),
            ),
            Atom::FnDef(_) => todo!(),
            Atom::Pat(origin_pat) => (
                self.stores().ast_info().pats().get_node_by_data(origin_pat),
                self.stores().location().get_location(origin_pat),
            ),
        };
        if let Some(location) = location {
            self.stores().location().add_location_to_target(ty, location);
        }
        if let Some(ast_info) = ast_info {
            self.stores().ast_info().tys().insert(ast_info, ty);
        }
        ty
    }

    /// Create a new type hole for typing the given term.
    fn new_ty_hole_of_ty(&self, src: TyId) -> TyId {
        let ty = self.stores().ty().create_with(|_| Ty::Hole(Hole::fresh()));
        self.new_expected_ty_of_ty(src, ty)
    }

    /// Create a new type hole for typing the given term.
    fn new_ty_hole_of(&self, src: TermId) -> TyId {
        let ty = self.stores().ty().create_with(|_| Ty::Hole(Hole::fresh()));
        self.new_expected_ty_of(src, ty)
    }

    /// Create a new positional parameter list with the given types.
    fn new_params(&self, types: &[TyId]) -> ParamsId {
        self.stores().params().create_from_iter_with(
            types
                .iter()
                .copied()
                .enumerate()
                .map(|(i, ty)| move |_id| Param { name: Symbol::from_name(i), ty, default: None }),
        )
    }

    /// Try to use the given term as a type.
    fn try_use_term_as_ty(&self, term: TermId) -> Option<TyId> {
        match term.value() {
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
        match ty.value() {
            Ty::Var(var) => self.new_term(var),
            Ty::Hole(hole) => self.new_term(hole),
            Ty::Eval(term) => match self.try_use_term_as_ty(term) {
                Some(ty) => self.use_ty_as_term(ty),
                None => term,
            },
            _ => self.new_term(ty),
        }
    }

    fn dump_tir(&self, value: impl ToString) {
        stream_less_writeln!("[TIR dump]:\n{}", value.to_string());
    }
}

impl<T: AccessToEnv + ?Sized> CommonUtils for T {}
