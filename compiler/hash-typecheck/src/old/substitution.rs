//! Operations to substitute variables in types and terms.

use std::{collections::HashSet, ops::ControlFlow};

use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::ContextMember,
    sub::Sub,
    tir::{
        AccessTerm, ArgsId, Hole, NodeId, ParamId, ParamIndex, ParamsId, Pat, SymbolId, Term,
        TermId, Ty,
    },
    visitor::{Atom, Map, Visit, Visitor},
};
use hash_utils::{derive_more::Deref, log::warn};

use crate::env::TcEnv;

#[derive(Deref)]
pub struct SubstitutionOps<'a, T: TcEnv> {
    #[deref]
    env: &'a T,
    traversing_utils: Visitor,
}

impl<'a, T: TcEnv> SubstitutionOps<'a, T> {
    pub fn new(env: &'a T) -> Self {
        Self { env, traversing_utils: Visitor::new() }
    }

    fn params_contain_vars(
        &self,
        params: ParamsId,
        var_matches: &HashSet<SymbolId>,
        can_apply: &mut bool,
    ) -> HashSet<SymbolId> {
        let mut seen = var_matches.clone();
        for param in params.iter() {
            let param = param.value();
            if self.atom_contains_vars(param.ty.into(), &seen) {
                *can_apply = true;
                return seen;
            }
            seen.remove(&param.name);
            if let Some(default) = param.default {
                if self.atom_contains_vars(default.into(), &seen) {
                    *can_apply = true;
                    return seen;
                }
            }
        }
        seen
    }

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
    pub fn apply_sub_to_atom_in_place_once(&self, atom: Atom, sub: &Sub) -> ControlFlow<()> {
        // Apply to type as well if applicable
        match atom {
            Atom::Term(term) => {
                if let Some(ty) = self.try_get_inferred_ty(term) {
                    self.apply_sub_in_place(ty, sub);
                }
            }
            Atom::Pat(pat) => {
                if let Some(ty) = self.try_get_inferred_ty(pat) {
                    self.apply_sub_in_place(ty, sub);
                }
            }
            Atom::FnDef(_) => {}
        }
        match atom {
            Atom::Term(term) => match *term.value() {
                Term::Hole(Hole(symbol)) | Term::Var(symbol) => match sub.get_sub_for(symbol) {
                    Some(subbed_term) => {
                        let subbed_term_val = subbed_term.value();
                        term.set(subbed_term_val);
                        ControlFlow::Break(())
                    }
                    None => ControlFlow::Continue(()),
                },
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
        }
    }

    /// Whether the given substitution can be appliedto the given atom,
    ///
    /// i.e. if the atom contains a variable or hole that is in the
    /// substitution.
    pub fn atom_contains_vars_once(
        &self,
        atom: Atom,
        var_matches: &HashSet<SymbolId>,
        can_apply: &mut bool,
    ) -> ControlFlow<()> {
        let var_matches = &var_matches;
        match atom {
            Atom::Term(term) => match *term.value() {
                Term::Hole(Hole(symbol)) | Term::Var(symbol) if var_matches.contains(&symbol) => {
                    *can_apply = true;
                    ControlFlow::Break(())
                }
                Ty::TupleTy(tuple_ty) => {
                    let _ = self.params_contain_vars(tuple_ty.data, var_matches, can_apply);
                    ControlFlow::Break(())
                }
                Ty::FnTy(fn_ty) => {
                    let seen = self.params_contain_vars(fn_ty.params, var_matches, can_apply);
                    if self.atom_contains_vars(fn_ty.return_ty.into(), &seen) {
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
                if self.atom_contains_vars(fn_ty.return_ty.into(), &seen) {
                    *can_apply = true;
                    return ControlFlow::Break(());
                }
                if self.atom_contains_vars(fn_def.body.into(), &seen) {
                    *can_apply = true;
                    return ControlFlow::Break(());
                }
                ControlFlow::Break(())
            }
            Atom::Pat(_) => ControlFlow::Continue(()),
        }
    }

    /// Whether the given substitution can be appliedto the given atom,
    ///
    /// i.e. if the atom contains a variable or hole that is in the
    /// substitution.
    pub fn can_apply_sub_to_atom_once(
        &self,
        atom: Atom,
        sub: &Sub,
        can_apply: &mut bool,
    ) -> ControlFlow<()> {
        let domain: HashSet<SymbolId> = sub.domain().collect();
        self.atom_contains_vars_once(atom, &domain, can_apply)
    }

    /// Below are convenience methods for specific atoms:
    pub fn atom_contains_vars(&self, atom: Atom, filter: &HashSet<SymbolId>) -> bool {
        let mut can_apply = false;
        self.traversing_utils
            .visit(atom, &mut |atom| self.atom_contains_vars_once(atom, filter, &mut can_apply));
        can_apply
    }

    /// Below are convenience methods for specific atoms:
    pub fn can_apply_sub_to_atom(&self, atom: Atom, sub: &Sub) -> bool {
        let mut can_apply = false;
        self.traversing_utils
            .visit(atom, &mut |atom| self.can_apply_sub_to_atom_once(atom, sub, &mut can_apply));
        can_apply
    }

    pub fn apply_sub_in_place<U>(&self, item: U, sub: &Sub)
    where
        Visitor: Visit<U>,
    {
        self.traversing_utils
            .visit(item, &mut |atom| self.apply_sub_to_atom_in_place_once(atom, sub));
    }

    pub fn apply_sub_from_context<U>(&self, item: U)
    where
        Visitor: Visit<U>,
    {
        let atom = item;
        let sub = self.create_sub_from_current_scope();
        self.apply_sub_in_place(atom, &sub);
    }

    /// Determines whether the given atom contains a hole.
    ///
    /// If a hole is found, `ControlFlow::Break(())` is returned. Otherwise,
    /// `ControlFlow::Continue(())` is returned. `has_holes` is updated
    /// accordingly.
    pub fn atom_has_holes_once(&self, atom: Atom, has_holes: &mut Option<Atom>) -> ControlFlow<()> {
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
        }
    }

    /// Determines whether the given TIR node contains one or more holes.
    pub fn has_holes<U>(&self, item: U) -> Option<Atom>
    where
        Visitor: Visit<U>,
    {
        let mut has_holes = None;
        self.traversing_utils
            .visit(item, &mut |atom| self.atom_has_holes_once(atom, &mut has_holes));
        has_holes
    }

    /// Create a substitution from the current scope members.
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
    pub fn is_unassigned_var_in_current_scope(&self, var: SymbolId) -> bool {
        let _current_scope_index = self.context().get_current_scope_index();
        match self.context().get_current_scope_ref().get_decl(var) {
            Some(var) => {
                matches!(var, ContextMember { value: None, .. })
            }
            None => {
                warn!("Not found var {} in current scope", var);
                false
            }
        }
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

    pub fn apply_sub_to_sub_in_place(&self, origin: &Sub, target: &Sub) -> Sub {
        let mut sub = Sub::identity();
        for (var, value) in target.iter() {
            let value = self.apply_sub(value, origin);
            sub.insert(var, value);
        }
        sub
    }

    pub fn apply_sub<U: Copy>(&self, item: U, sub: &Sub) -> U
    where
        Visitor: Visit<U> + Map<U>,
    {
        let copy = self.traversing_utils.copy(item);
        self.apply_sub_in_place(copy, sub);
        copy
    }

    /// Insert the given variable and value into the given substitution if
    /// the value is not a variable with the same name.
    pub fn insert_to_sub_if_needed(&self, sub: &mut Sub, name: SymbolId, value: TermId) {
        let subbed_value = self.apply_sub(value, sub);
        if !matches!(*subbed_value.value(), Term::Var(v) if v == name) {
            sub.insert(name, subbed_value);
        }
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
            if self.atom_contains_vars(value.into(), &param_names) {
                continue;
            }

            shadowed_sub.insert(name, value);
        }

        shadowed_sub
    }

    /// Reverse the given substitution.
    ///
    /// Invariant: the substitution is injective.
    pub fn reverse_sub(&self, sub: &Sub) -> Sub {
        let mut reversed_sub = Sub::identity();
        for (name, value) in sub.iter() {
            match *value.value() {
                Term::Var(v) => {
                    reversed_sub.insert(v, Term::from(name, name.origin()));
                }
                Term::Hole(h) => {
                    reversed_sub.insert(h.0, Term::from(name, name.origin()));
                }
                _ => {
                    panic!("cannot reverse non-injective substitution");
                }
            }
        }
        reversed_sub
    }
}
