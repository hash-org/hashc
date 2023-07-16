//! Operations to substitute variables in types and terms.

use std::{collections::HashSet, ops::ControlFlow};

use derive_more::Deref;
use hash_tir::{
    access::AccessTerm,
    args::{ArgsId, PatArgsId},
    atom_info::ItemInAtomInfo,
    context::Decl,
    environment::stores::StoreId,
    fns::FnBody,
    holes::Hole,
    mods::ModDefId,
    params::{ParamId, ParamIndex, ParamsId},
    pats::Pat,
    sub::Sub,
    symbols::Symbol,
    terms::{Term, TermId},
    tys::{Ty, TyId},
    utils::{
        common::CommonUtils,
        traversing::{Atom, TraversingUtils},
        AccessToUtils,
    },
};
use hash_utils::{
    log::warn,
    store::{Store, TrivialKeySequenceStore, TrivialSequenceStoreKey},
};

use crate::AccessToTypechecking;

#[derive(Deref)]
pub struct SubstitutionOps<'a, T: AccessToTypechecking> {
    #[deref]
    env: &'a T,
    traversing_utils: TraversingUtils<'a>,
}

impl<'a, T: AccessToTypechecking> SubstitutionOps<'a, T> {
    pub fn new(env: &'a T) -> Self {
        Self { env, traversing_utils: env.traversing_utils() }
    }

    fn params_contain_vars(
        &self,
        params: ParamsId,
        var_matches: &HashSet<Symbol>,
        can_apply: &mut bool,
    ) -> HashSet<Symbol> {
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
            self.apply_sub_to_ty_in_place(param.ty, &shadowed_sub);
            shadowed_sub.remove(param.name);
            if let Some(default) = param.default {
                self.apply_sub_to_term_in_place(default, &shadowed_sub);
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
                    self.apply_sub_to_atom_in_place(ty.into(), sub);
                }
            }
            Atom::Pat(pat) => {
                if let Some(ty) = self.try_get_inferred_ty(pat) {
                    self.apply_sub_to_atom_in_place(ty.into(), sub);
                }
            }
            Atom::Ty(_) | Atom::FnDef(_) => {}
        }
        match atom {
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Hole(Hole(symbol)) | Ty::Var(symbol) => {
                    match sub.get_sub_for_var_or_hole(symbol) {
                        Some(subbed_term) => {
                            let subbed_ty_val = self.get_ty(self.use_term_as_ty(subbed_term));
                            self.stores().ty().modify_fast(ty, |ty| *ty = subbed_ty_val);
                            ControlFlow::Break(())
                        }
                        None => ControlFlow::Continue(()),
                    }
                }
                Ty::Tuple(tuple_ty) => {
                    let _ = self.apply_sub_to_params_and_get_shadowed(tuple_ty.data, sub);
                    ControlFlow::Break(())
                }
                Ty::Fn(fn_ty) => {
                    let shadowed_sub = self.apply_sub_to_params_and_get_shadowed(fn_ty.params, sub);
                    self.apply_sub_to_ty_in_place(fn_ty.return_ty, &shadowed_sub);
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::Term(term) => match self.get_term(term) {
                Term::Hole(Hole(symbol)) | Term::Var(symbol) => match sub.get_sub_for(symbol) {
                    Some(subbed_term) => {
                        let subbed_term_val = self.get_term(subbed_term);
                        self.stores().term().modify_fast(term, |term| *term = subbed_term_val);
                        ControlFlow::Break(())
                    }
                    None => ControlFlow::Continue(()),
                },
                _ => ControlFlow::Continue(()),
            },
            Atom::FnDef(fn_def_id) => {
                let fn_def = self.get_fn_def(fn_def_id);
                let fn_ty = fn_def.ty;
                let shadowed_sub = self.apply_sub_to_params_and_get_shadowed(fn_ty.params, sub);
                self.apply_sub_to_ty_in_place(fn_ty.return_ty, &shadowed_sub);
                match fn_def.body {
                    FnBody::Defined(defined) => {
                        self.apply_sub_to_term_in_place(defined, &shadowed_sub);
                    }
                    FnBody::Intrinsic(_) | FnBody::Axiom => {}
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
    pub fn atom_contains_vars_once(
        &self,
        atom: Atom,
        var_matches: &HashSet<Symbol>,
        can_apply: &mut bool,
    ) -> ControlFlow<()> {
        let var_matches = &var_matches;
        match atom {
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Hole(Hole(symbol)) | Ty::Var(symbol) if var_matches.contains(&symbol) => {
                    *can_apply = true;
                    ControlFlow::Break(())
                }
                Ty::Tuple(tuple_ty) => {
                    let _ = self.params_contain_vars(tuple_ty.data, var_matches, can_apply);
                    ControlFlow::Break(())
                }
                Ty::Fn(fn_ty) => {
                    let seen = self.params_contain_vars(fn_ty.params, var_matches, can_apply);
                    if self.atom_contains_vars(fn_ty.return_ty.into(), &seen) {
                        *can_apply = true;
                        return ControlFlow::Break(());
                    }
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::Term(term) => match self.get_term(term) {
                Term::Hole(Hole(symbol)) | Term::Var(symbol) if var_matches.contains(&symbol) => {
                    *can_apply = true;
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::FnDef(fn_def_id) => {
                let fn_def = self.get_fn_def(fn_def_id);
                let fn_ty = fn_def.ty;
                let seen = self.params_contain_vars(fn_ty.params, var_matches, can_apply);
                if self.atom_contains_vars(fn_ty.return_ty.into(), &seen) {
                    *can_apply = true;
                    return ControlFlow::Break(());
                }
                match fn_def.body {
                    FnBody::Defined(defined) => {
                        if self.atom_contains_vars(defined.into(), &seen) {
                            *can_apply = true;
                            return ControlFlow::Break(());
                        }
                    }
                    FnBody::Intrinsic(_) | FnBody::Axiom => {}
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
        let domain: HashSet<Symbol> = sub.domain().collect();
        self.atom_contains_vars_once(atom, &domain, can_apply)
    }

    /// Below are convenience methods for specific atoms:
    pub fn atom_contains_vars(&self, atom: Atom, filter: &HashSet<Symbol>) -> bool {
        let mut can_apply = false;
        self.traversing_utils
            .visit_atom::<!, _>(atom, &mut |atom| {
                Ok(self.atom_contains_vars_once(atom, filter, &mut can_apply))
            })
            .into_ok();
        can_apply
    }

    /// Below are convenience methods for specific atoms:
    pub fn can_apply_sub_to_atom(&self, atom: Atom, sub: &Sub) -> bool {
        let mut can_apply = false;
        self.traversing_utils
            .visit_atom::<!, _>(atom, &mut |atom| {
                Ok(self.can_apply_sub_to_atom_once(atom, sub, &mut can_apply))
            })
            .into_ok();
        can_apply
    }

    pub fn apply_sub_to_term_in_place(&self, term_id: TermId, sub: &Sub) {
        self.traversing_utils
            .visit_term::<!, _>(term_id, &mut |atom| {
                Ok(self.apply_sub_to_atom_in_place_once(atom, sub))
            })
            .into_ok()
    }

    pub fn apply_sub_to_ty_in_place(&self, ty_id: TyId, sub: &Sub) {
        self.traversing_utils
            .visit_ty::<!, _>(
                ty_id,
                &mut |atom| Ok(self.apply_sub_to_atom_in_place_once(atom, sub)),
            )
            .into_ok()
    }

    pub fn apply_sub_to_params_in_place(&self, params_id: ParamsId, sub: &Sub) {
        self.traversing_utils
            .visit_params::<!, _>(params_id, &mut |atom| {
                Ok(self.apply_sub_to_atom_in_place_once(atom, sub))
            })
            .into_ok()
    }

    pub fn apply_sub_to_atom_in_place(&self, atom: Atom, sub: &Sub) {
        self.traversing_utils
            .visit_atom::<!, _>(atom, &mut |atom| {
                Ok(self.apply_sub_to_atom_in_place_once(atom, sub))
            })
            .into_ok()
    }

    pub fn apply_sub_to_pat_args_in_place(&self, pat_args_id: PatArgsId, sub: &Sub) {
        self.traversing_utils
            .visit_pat_args::<!, _>(pat_args_id, &mut |atom| {
                Ok(self.apply_sub_to_atom_in_place_once(atom, sub))
            })
            .into_ok()
    }

    pub fn apply_sub_to_args_in_place(&self, args_id: ArgsId, sub: &Sub) {
        self.traversing_utils
            .visit_args::<!, _>(args_id, &mut |atom| {
                Ok(self.apply_sub_to_atom_in_place_once(atom, sub))
            })
            .into_ok()
    }

    pub fn apply_sub_to_atom_from_context(&self, atom: impl Into<Atom>) {
        let atom = atom.into();
        let sub = self.create_sub_from_current_scope();
        self.apply_sub_to_atom_in_place(atom, &sub);
    }

    /// Determines whether the given atom contains a hole.
    ///
    /// If a hole is found, `ControlFlow::Break(())` is returned. Otherwise,
    /// `ControlFlow::Continue(())` is returned. `has_holes` is updated
    /// accordingly.
    pub fn has_holes_once(&self, atom: Atom, has_holes: &mut Option<Atom>) -> ControlFlow<()> {
        match atom {
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Hole(_) => {
                    *has_holes = Some(atom);
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::Term(term) => match self.get_term(term) {
                Term::Hole(_) => {
                    *has_holes = Some(atom);
                    ControlFlow::Break(())
                }
                Term::Ctor(ctor_term) => {
                    if let Some(atom) = self.args_have_holes(ctor_term.ctor_args) {
                        *has_holes = Some(atom);
                    }
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::Pat(pat) => match self.get_pat(pat) {
                Pat::Ctor(ctor_pat) => {
                    if let Some(atom) = self.pat_args_have_holes(ctor_pat.ctor_pat_args) {
                        *has_holes = Some(atom);
                    }
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::FnDef(_) => ControlFlow::Continue(()),
        }
    }

    /// Determines whether the given atom contains one or more holes.
    pub fn atom_has_holes(&self, atom: impl Into<Atom>) -> Option<Atom> {
        let mut has_holes = None;
        self.traversing_utils
            .visit_atom::<!, _>(atom.into(), &mut |atom| {
                Ok(self.has_holes_once(atom, &mut has_holes))
            })
            .into_ok();
        has_holes
    }

    /// Determines whether the given module definition contains one or more
    /// holes.
    pub fn mod_def_has_holes(&self, mod_def_id: ModDefId) -> Option<Atom> {
        let mut has_holes = None;
        self.traversing_utils
            .visit_mod_def::<!, _>(mod_def_id, &mut |atom| {
                Ok(self.has_holes_once(atom, &mut has_holes))
            })
            .into_ok();
        has_holes
    }

    /// Determines whether the given set of arguments contains one or more
    /// holes.
    pub fn pat_args_have_holes(&self, pat_args_id: PatArgsId) -> Option<Atom> {
        let mut has_holes = None;
        self.traversing_utils
            .visit_pat_args::<!, _>(pat_args_id, &mut |atom| {
                Ok(self.has_holes_once(atom, &mut has_holes))
            })
            .into_ok();
        has_holes
    }

    /// Determines whether the given set of arguments contains one or more
    /// holes.
    pub fn args_have_holes(&self, args_id: ArgsId) -> Option<Atom> {
        let mut has_holes = None;
        self.traversing_utils
            .visit_args::<!, _>(args_id, &mut |atom| Ok(self.has_holes_once(atom, &mut has_holes)))
            .into_ok();
        has_holes
    }

    /// Determines whether the given set of parameters contains one or more
    /// holes.
    pub fn params_have_holes(&self, params_id: ParamsId) -> Option<Atom> {
        let mut has_holes = None;
        self.traversing_utils
            .visit_params::<!, _>(params_id, &mut |atom| {
                Ok(self.has_holes_once(atom, &mut has_holes))
            })
            .into_ok();
        has_holes
    }

    /// Create a substitution from the current scope members.
    pub fn get_unassigned_vars_in_current_scope(&self) -> HashSet<Symbol> {
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
    pub fn is_unassigned_var_in_current_scope(&self, var: Symbol) -> bool {
        let _current_scope_index = self.context().get_current_scope_index();
        match self.context().get_current_scope_ref().get_decl(var) {
            Some(var) => {
                matches!(var, Decl { value: None, .. })
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
            let value = self.apply_sub_to_term(value, origin);
            sub.insert(var, value);
        }
        sub
    }

    pub fn apply_sub_to_atom(&self, atom: Atom, sub: &Sub) -> Atom {
        let copy = self.copy_atom(atom);
        self.apply_sub_to_atom_in_place(copy, sub);
        copy
    }

    pub fn apply_sub_to_args(&self, args: ArgsId, sub: &Sub) -> ArgsId {
        let copy = self.copy_args(args);
        self.apply_sub_to_args_in_place(copy, sub);
        copy
    }

    pub fn apply_sub_to_params(&self, params: ParamsId, sub: &Sub) -> ParamsId {
        let copy = self.copy_params(params);
        self.apply_sub_to_params_in_place(copy, sub);
        copy
    }

    pub fn apply_sub_to_ty(&self, ty: TyId, sub: &Sub) -> TyId {
        let copy = self.copy_ty(ty);
        self.apply_sub_to_ty_in_place(copy, sub);
        copy
    }

    pub fn apply_sub_to_term(&self, term: TermId, sub: &Sub) -> TermId {
        let copy = self.copy_term(term);
        self.apply_sub_to_term_in_place(copy, sub);
        copy
    }

    /// Insert the given variable and value into the given substitution if
    /// the value is not a variable with the same name.
    pub fn insert_to_sub_if_needed(&self, sub: &mut Sub, name: Symbol, value: TermId) {
        let subbed_value = self.apply_sub_to_term(value, sub);
        if !matches!(self.get_term(subbed_value), Term::Var(v) if v == name) {
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
            let param = self.stores().params().get_element(param_id);
            let arg = self.stores().args().get_element(arg_id);
            self.insert_to_sub_if_needed(&mut sub, param.name, arg.value);
        }
        sub
    }

    /// Create a substitution from the given source parameter names to the
    /// same names but prefixed with the access subject.
    pub fn create_sub_from_param_access(&self, params: ParamsId, access_subject: TermId) -> Sub {
        let mut sub = Sub::identity();
        for src_id in params.iter() {
            let src = self.stores().params().get_element(src_id);
            if let Some(ident) = self.get_param_name_ident(src_id) {
                sub.insert(
                    src.name,
                    self.new_term(AccessTerm {
                        subject: access_subject,
                        field: ParamIndex::Name(ident),
                    }),
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
            let src = self.stores().params().get_element(src);
            let target = self.stores().params().get_element(target);
            if src.name != target.name {
                sub.insert(src.name, self.new_term(target.name));
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
            match self.get_term(value) {
                Term::Var(v) => {
                    reversed_sub.insert(v, self.new_term(name));
                }
                Term::Hole(h) => {
                    reversed_sub.insert(h.0, self.new_term(name));
                }
                _ => {
                    panic!("cannot reverse non-injective substitution");
                }
            }
        }
        reversed_sub
    }

    /// Copies an atom, returning a new atom.
    pub fn copy_atom(&self, atom: Atom) -> Atom {
        self.traversing_utils.fmap_atom::<!, _>(atom, |_a| Ok(ControlFlow::Continue(()))).into_ok()
    }

    /// Copies a type, returning a new type.
    pub fn copy_term(&self, term: TermId) -> TermId {
        self.traversing_utils.fmap_term::<!, _>(term, |_a| Ok(ControlFlow::Continue(()))).into_ok()
    }

    /// Copies a type, returning a new type.
    pub fn copy_ty(&self, ty: TyId) -> TyId {
        self.traversing_utils.fmap_ty::<!, _>(ty, |_a| Ok(ControlFlow::Continue(()))).into_ok()
    }

    /// Copies parameters, returning new parameters.
    pub fn copy_params(&self, params: ParamsId) -> ParamsId {
        self.traversing_utils
            .fmap_params::<!, _>(params, |_a| Ok(ControlFlow::Continue(())))
            .into_ok()
    }

    /// Copies parameters, returning new parameters.
    pub fn copy_args(&self, args: ArgsId) -> ArgsId {
        self.traversing_utils.fmap_args::<!, _>(args, |_a| Ok(ControlFlow::Continue(()))).into_ok()
    }
}
