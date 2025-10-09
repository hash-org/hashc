//! Operations to substitute variables in types and terms.
use std::{collections::HashSet, ops::ControlFlow};

use hash_storage::store::{TrivialSequenceStoreKey, statics::StoreId};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::HasContext,
    sub::Sub,
    tir::{
        AccessTerm, ArgsId, Hole, NodeId, ParamId, ParamIndex, ParamsId, Pat, SymbolId, Term,
        TermId, Ty, VarTerm,
    },
    visitor::{Atom, Map, Visit, Visitor},
};

use crate::{env::TcEnv, tc::Tc};

/// A wrapper around the typechecker, with its own TIR `Visitor`,
/// which can be used to substitute variables in types and terms.
pub struct Substituter<'a, T: TcEnv> {
    tc: &'a Tc<'a, T>,
    traversing_utils: Visitor,
}

impl<T: TcEnv> HasContext for Substituter<'_, T> {
    fn context(&self) -> &hash_tir::context::Context {
        self.tc.context()
    }
}

impl<'a, T: TcEnv> Substituter<'a, T> {
    pub fn new(checker: &'a Tc<'a, T>) -> Self {
        Self { tc: checker, traversing_utils: Visitor::new() }
    }

    /// Determines whether the given TIR node contains one or more holes.
    ///
    /// If so, it returns the atom which contains the hole.
    pub fn has_holes<U>(&self, item: U) -> Option<Atom>
    where
        Visitor: Visit<U>,
    {
        let mut has_holes = None;
        self.traversing_utils
            .visit(item, &mut |atom| self.atom_has_holes_once(atom, &mut has_holes));
        has_holes
    }

    /// Whether the given atom contains any of the variables in `filter`.
    pub fn contains_vars<N>(&self, atom: N, filter: &HashSet<SymbolId>) -> bool
    where
        Visitor: Visit<N>,
    {
        let mut can_apply = false;
        self.traversing_utils
            .visit(atom, &mut |atom| self.atom_contains_vars_once(atom, filter, &mut can_apply));
        can_apply
    }

    /// Apply the given substitution to the given atom, modifying it in place.
    pub fn apply_sub_in_place<U>(&self, item: U, sub: &Sub)
    where
        Visitor: Visit<U>,
    {
        self.traversing_utils
            .visit(item, &mut |atom| self.apply_sub_to_atom_in_place_once(atom, sub));
    }

    /// Apply the substitition carried by the ambient context, to the given
    /// atom.
    ///
    /// This is done so that the atom can escape the context without any
    /// lingering references to its local scope.
    // @@Formalise: we should specify exactly how this works using formal inference
    // rules, and ensure that this is met by this algorithm.
    pub fn apply_sub_from_context<U>(&self, item: U)
    where
        Visitor: Visit<U>,
    {
        let atom = item;
        let sub = self.create_sub_from_current_scope();
        self.apply_sub_in_place(atom, &sub);
    }

    /// Get the set of unassigned variables in the current scope.
    pub fn get_unassigned_vars_in_current_scope(&self) -> HashSet<SymbolId> {
        let mut sub = HashSet::new();
        let current_scope_index = self.context().get_current_scope_index();
        self.context().for_decls_of_scope_rev(current_scope_index, |binding| {
            if self.context().try_get_decl_value(binding.name).is_none() {
                sub.insert(binding.name);
            }
        });
        sub
    }

    /// Create a substitution from the current scope members.
    pub fn create_sub_from_current_scope(&self) -> Sub {
        let mut sub = Sub::identity();

        let current_scope_index = self.context().get_current_scope_index();
        self.context().for_decls_of_scope_rev(current_scope_index, |binding| {
            if let Some(value) = self.context().try_get_decl_value(binding.name) {
                self.insert_to_sub_if_needed(&mut sub, binding.name, value);
            }
        });

        sub
    }

    /// Apply a substitution to the given atom, returning a new atom.
    pub fn apply_sub<U: Copy>(&self, item: U, sub: &Sub) -> U
    where
        Visitor: Visit<U> + Map<U>,
    {
        let copy = self.traversing_utils.copy(item);
        self.apply_sub_in_place(copy, sub);
        copy
    }

    /// Create a substitution from the given arguments.
    ///
    /// Invariant: the arguments are ordered to match the
    /// parameters.
    pub fn create_sub_from_args_of_params(&self, args_id: ArgsId, params_id: ParamsId) -> Sub {
        let mut sub = Sub::identity();
        for (param_id, arg_id) in (params_id.iter()).zip(args_id.iter()) {
            let param = param_id.value();
            let arg = arg_id.value();
            self.insert_to_sub_if_needed(&mut sub, param.name, arg.value);
        }
        sub
    }

    /// Create a substitution from the given source parameter names to the
    /// same names but prefixed with the access subject.
    pub fn create_sub_from_param_access(&self, params: ParamsId, access_subject: TermId) -> Sub {
        let mut sub = Sub::identity();
        for src_id in params.iter() {
            let src = src_id.value();
            if let Some(ident) = src_id.borrow().name_ident() {
                sub.insert(
                    src.name,
                    Term::from(
                        AccessTerm { subject: access_subject, field: ParamIndex::Name(ident) },
                        access_subject.origin(),
                    ),
                );
            }
        }
        sub
    }

    /// Create a substitution from the given source parameter names to the
    /// target parameter names.
    ///
    /// Invariant: the parameters unify.
    pub fn create_sub_from_param_names(
        &self,
        src_params: ParamsId,
        target_params: ParamsId,
    ) -> Sub {
        let mut sub = Sub::identity();
        for (src, target) in (src_params.iter()).zip(target_params.iter()) {
            let src = src.value();
            let target = target.value();
            if src.name != target.name {
                sub.insert(src.name, Term::from(target.name, target.origin));
            }
        }
        sub
    }

    /// Hide the given set of parameters from the substitution.
    pub fn hide_param_binds(&self, params: impl IntoIterator<Item = ParamId>, sub: &Sub) -> Sub {
        let mut shadowed_sub = Sub::identity();
        let param_names = params.into_iter().map(|p| p.borrow().name).collect::<HashSet<_>>();

        for (name, value) in sub.iter() {
            // If the substitution is from that parameter, skip it.
            if param_names.contains(&name) {
                continue;
            }
            // If the substitution is to that parameter, skip it.
            if self.contains_vars(value, &param_names) {
                continue;
            }

            shadowed_sub.insert(name, value);
        }

        shadowed_sub
    }

    /// Check whether the given `Params` contains any of the variables inside
    /// `var_matches`.
    ///
    /// This performs shadowing on the parameter names, so that any dependency
    /// on previous parameters is not taken into account.
    fn params_contain_vars(
        &self,
        params: ParamsId,
        var_matches: &HashSet<SymbolId>,
        can_apply: &mut bool,
    ) -> HashSet<SymbolId> {
        let mut seen = var_matches.clone();
        for param in params.iter() {
            let param = param.value();
            if self.contains_vars(param.ty, &seen) {
                *can_apply = true;
                return seen;
            }
            seen.remove(&param.name);
            if let Some(default) = param.default
                && self.contains_vars(default, &seen)
            {
                *can_apply = true;
                return seen;
            }
        }
        seen
    }

    /// Apply a given substitution to the parameters, appropriately accounting
    /// for the parameter dependencies.
    ///
    /// For example, substitution `[a -> b]` in parameters `(a: A(a), b: B(a))`
    /// will result in `(a: A(b), b: B(a))`, because the second `a` depends
    /// on the first `a`, and not on the substitution source `a`. (This example
    /// is a bit contrived because usually this naming conflict doesn't exist
    /// due to uniqueness of symbols. It it still comes up when symbols have the
    /// same ID due to recursion)
    fn apply_sub_to_params_and_get_shadowed(&self, params: ParamsId, sub: &Sub) -> Sub {
        let mut shadowed_sub = sub.clone();
        for param in params.iter() {
            let param = param.value();
            self.apply_sub_in_place(param.ty, &shadowed_sub);
            shadowed_sub.remove(param.name);
            if let Some(default) = param.default {
                self.apply_sub_in_place(default, &shadowed_sub);
            }
        }
        shadowed_sub
    }

    /// Apply the given substitution to the given atom, modifying it in place.
    ///
    /// Returns `ControlFlow::Break(())` if the atom was modified, and
    /// `ControlFlow::Continue(())` otherwise to recurse deeper.
    fn apply_sub_to_atom_in_place_once(&self, atom: Atom, sub: &Sub) -> ControlFlow<()> {
        // Apply to type as well if applicable
        match atom {
            Atom::Term(term) => {
                if let Some(ty) = self.tc.try_get_inferred_ty(term) {
                    self.apply_sub_in_place(ty, sub);
                }
            }
            Atom::Pat(pat) => {
                if let Some(ty) = self.tc.try_get_inferred_ty(pat) {
                    self.apply_sub_in_place(ty, sub);
                }
            }
            Atom::Lit(_) | Atom::FnDef(_) => {}
        }
        match atom {
            Atom::Term(term) => match *term.value() {
                Term::Hole(Hole(symbol)) | Term::Var(VarTerm { symbol }) => {
                    match sub.get_sub_for(symbol) {
                        Some(subbed_term) => {
                            let subbed_term_val = subbed_term.value();
                            term.set(subbed_term_val);
                            ControlFlow::Break(())
                        }
                        None => ControlFlow::Continue(()),
                    }
                }
                Ty::TupleTy(tuple_ty) => {
                    let _ = self.apply_sub_to_params_and_get_shadowed(tuple_ty.data, sub);
                    ControlFlow::Break(())
                }
                Ty::FnTy(fn_ty) => {
                    let shadowed_sub = self.apply_sub_to_params_and_get_shadowed(fn_ty.params, sub);
                    self.apply_sub_in_place(fn_ty.return_ty, &shadowed_sub);
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::FnDef(fn_def_id) => {
                let fn_def = fn_def_id.value();
                let fn_ty = fn_def.ty;
                let shadowed_sub = self.apply_sub_to_params_and_get_shadowed(fn_ty.params, sub);
                self.apply_sub_in_place(fn_ty.return_ty, &shadowed_sub);
                self.apply_sub_in_place(fn_def.body, &shadowed_sub);
                ControlFlow::Break(())
            }
            Atom::Pat(_) => ControlFlow::Continue(()),
            Atom::Lit(_) => ControlFlow::Break(()),
        }
    }

    /// Whether the given substitution can be appliedto the given atom,
    ///
    /// i.e. if the atom contains a variable or hole that is in the
    /// substitution.
    fn atom_contains_vars_once(
        &self,
        atom: Atom,
        var_matches: &HashSet<SymbolId>,
        can_apply: &mut bool,
    ) -> ControlFlow<()> {
        let var_matches = &var_matches;
        match atom {
            Atom::Term(term) => match *term.value() {
                Term::Hole(Hole(symbol)) | Term::Var(VarTerm { symbol })
                    if var_matches.contains(&symbol) =>
                {
                    *can_apply = true;
                    ControlFlow::Break(())
                }
                Ty::TupleTy(tuple_ty) => {
                    let _ = self.params_contain_vars(tuple_ty.data, var_matches, can_apply);
                    ControlFlow::Break(())
                }
                Ty::FnTy(fn_ty) => {
                    let seen = self.params_contain_vars(fn_ty.params, var_matches, can_apply);
                    if self.contains_vars(fn_ty.return_ty, &seen) {
                        *can_apply = true;
                        return ControlFlow::Break(());
                    }
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::FnDef(fn_def_id) => {
                let fn_def = fn_def_id.value();
                let fn_ty = fn_def.ty;
                let seen = self.params_contain_vars(fn_ty.params, var_matches, can_apply);
                if self.contains_vars(fn_ty.return_ty, &seen) {
                    *can_apply = true;
                    return ControlFlow::Break(());
                }
                if self.contains_vars(fn_def.body, &seen) {
                    *can_apply = true;
                    return ControlFlow::Break(());
                }
                ControlFlow::Break(())
            }
            Atom::Pat(_) => ControlFlow::Continue(()),
            Atom::Lit(_) => ControlFlow::Break(()),
        }
    }

    /// Determines whether the given atom contains a hole.
    ///
    /// If a hole is found, `ControlFlow::Break(())` is returned. Otherwise,
    /// `ControlFlow::Continue(())` is returned. `has_holes` is updated
    /// accordingly.
    fn atom_has_holes_once(&self, atom: Atom, has_holes: &mut Option<Atom>) -> ControlFlow<()> {
        match atom {
            Atom::Term(term) => match *term.value() {
                Term::Hole(_) => {
                    *has_holes = Some(atom);
                    ControlFlow::Break(())
                }
                Term::Ctor(ctor_term) => {
                    if let Some(atom) = self.has_holes(ctor_term.ctor_args) {
                        *has_holes = Some(atom);
                    }
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::Pat(pat) => match *pat.value() {
                Pat::Ctor(ctor_pat) => {
                    if let Some(atom) = self.has_holes(ctor_pat.ctor_pat_args) {
                        *has_holes = Some(atom);
                    }
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::FnDef(_) => ControlFlow::Continue(()),
            Atom::Lit(_) => ControlFlow::Break(()),
        }
    }

    /// Insert the given variable and value into the given substitution if
    /// the value is not a variable with the same name.
    fn insert_to_sub_if_needed(&self, sub: &mut Sub, name: SymbolId, value: TermId) {
        let subbed_value = self.apply_sub(value, sub);
        if !matches!(*subbed_value.value(), Term::Var(v) if v.symbol == name) {
            sub.insert(name, subbed_value);
        }
    }
}
