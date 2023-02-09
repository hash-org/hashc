//! Operations to substitute variables in types and terms.

use std::ops::ControlFlow;

use derive_more::{Constructor, Deref};
use hash_tir::new::{
    args::ArgsId,
    environment::context::BindingKind,
    holes::Hole,
    mods::ModDefId,
    params::ParamsId,
    pats::PatId,
    sub::Sub,
    terms::{Term, TermId},
    tys::{Ty, TyId},
    utils::{common::CommonUtils, traversing::Atom, AccessToUtils},
};
use hash_utils::store::{SequenceStore, SequenceStoreKey, Store};

use crate::AccessToTypechecking;

#[derive(Constructor, Deref)]
pub struct SubstitutionOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> SubstitutionOps<'_, T> {
    /// Apply the given substitution to the given atom, modifying it in place.
    ///
    /// Returns `ControlFlow::Break(())` if the atom was modified, and
    /// `ControlFlow::Continue(())` otherwise to recurse deeper.
    pub fn apply_sub_to_atom_in_place_once(&self, atom: Atom, sub: &Sub) -> ControlFlow<()> {
        match atom {
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Hole(Hole(symbol)) | Ty::Var(symbol) => {
                    match sub.get_sub_for_var_or_hole(symbol) {
                        Some(term) => {
                            let subbed_ty = self.get_ty(self.use_term_as_ty(term));
                            self.stores().ty().modify_fast(ty, |ty| *ty = subbed_ty);
                            ControlFlow::Break(())
                        }
                        None => ControlFlow::Continue(()),
                    }
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::Term(term) => match self.get_term(term) {
                Term::Hole(Hole(symbol)) | Term::Var(symbol) => match sub.get_sub_for(symbol) {
                    Some(term) => {
                        let subbed_term = self.get_term(term);
                        self.stores().term().modify_fast(term, |term| *term = subbed_term);
                        ControlFlow::Break(())
                    }
                    None => ControlFlow::Continue(()),
                },
                _ => ControlFlow::Continue(()),
            },
            Atom::FnDef(_) | Atom::Pat(_) => ControlFlow::Continue(()),
        }
    }

    /// Apply the given substitution to the given atom,
    ///
    /// Returns `ControlFlow::Break(a)` with a new atom, or
    /// `ControlFlow::Continue(())` otherwise to recurse deeper.
    pub fn apply_sub_to_atom_once(&self, atom: Atom, sub: &Sub) -> ControlFlow<Atom> {
        match atom {
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Hole(Hole(symbol)) | Ty::Var(symbol) => match sub.get_sub_for(symbol) {
                    Some(term) => ControlFlow::Break(Atom::Ty(self.use_term_as_ty(term))),
                    None => ControlFlow::Continue(()),
                },
                _ => ControlFlow::Continue(()),
            },
            Atom::Term(term) => match self.get_term(term) {
                Term::Hole(Hole(symbol)) | Term::Var(symbol) => match sub.get_sub_for(symbol) {
                    Some(term) => ControlFlow::Break(Atom::Term(term)),
                    None => ControlFlow::Continue(()),
                },
                _ => ControlFlow::Continue(()),
            },
            Atom::FnDef(_) | Atom::Pat(_) => ControlFlow::Continue(()),
        }
    }

    /// Below are convenience methods for specific atoms:

    pub fn apply_sub_to_atom(&self, atom: Atom, sub: &Sub) -> Atom {
        self.traversing_utils()
            .fmap_atom::<!, _>(atom, |atom| Ok(self.apply_sub_to_atom_once(atom, sub)))
            .into_ok()
    }

    pub fn apply_sub_to_term(&self, term_id: TermId, sub: &Sub) -> TermId {
        self.traversing_utils()
            .fmap_term::<!, _>(term_id, |atom| Ok(self.apply_sub_to_atom_once(atom, sub)))
            .into_ok()
    }

    pub fn apply_sub_to_pat(&self, pat_id: PatId, sub: &Sub) -> PatId {
        self.traversing_utils()
            .fmap_pat::<!, _>(pat_id, |atom| Ok(self.apply_sub_to_atom_once(atom, sub)))
            .into_ok()
    }

    pub fn apply_sub_to_ty(&self, ty_id: TyId, sub: &Sub) -> TyId {
        self.traversing_utils()
            .fmap_ty::<!, _>(ty_id, |atom| Ok(self.apply_sub_to_atom_once(atom, sub)))
            .into_ok()
    }

    pub fn apply_sub_to_term_in_place(&self, term_id: TermId, sub: &Sub) {
        self.traversing_utils()
            .visit_term::<!, _>(term_id, &mut |atom| {
                Ok(self.apply_sub_to_atom_in_place_once(atom, sub))
            })
            .into_ok()
    }

    pub fn apply_sub_to_ty_in_place(&self, ty_id: TyId, sub: &Sub) {
        self.traversing_utils()
            .visit_ty::<!, _>(
                ty_id,
                &mut |atom| Ok(self.apply_sub_to_atom_in_place_once(atom, sub)),
            )
            .into_ok()
    }

    pub fn apply_sub_to_args(&self, args_id: ArgsId, sub: &Sub) -> ArgsId {
        self.traversing_utils()
            .fmap_args::<!, _>(args_id, |atom| Ok(self.apply_sub_to_atom_once(atom, sub)))
            .into_ok()
    }

    pub fn apply_sub_to_params_in_place(&self, params_id: ParamsId, sub: &Sub) {
        self.traversing_utils()
            .visit_params::<!, _>(params_id, &mut |atom| {
                Ok(self.apply_sub_to_atom_in_place_once(atom, sub))
            })
            .into_ok()
    }

    pub fn apply_sub_to_params(&self, params_id: ParamsId, sub: &Sub) -> ParamsId {
        self.traversing_utils()
            .fmap_params::<!, _>(params_id, |atom| Ok(self.apply_sub_to_atom_once(atom, sub)))
            .into_ok()
    }

    pub fn apply_sub_to_args_in_place(&self, args_id: ArgsId, sub: &Sub) {
        self.traversing_utils()
            .visit_args::<!, _>(args_id, &mut |atom| {
                Ok(self.apply_sub_to_atom_in_place_once(atom, sub))
            })
            .into_ok()
    }

    /// Determines whether the given atom contains a hole.
    ///
    /// If a hole is found, `ControlFlow::Break(())` is returned. Otherwise,
    /// `ControlFlow::Continue(())` is returned. `has_holes` is updated
    /// accordingly.
    pub fn has_holes_once(&self, atom: Atom, has_holes: &mut bool) -> ControlFlow<()> {
        match atom {
            Atom::Ty(ty) => match self.get_ty(ty) {
                Ty::Hole(_) => {
                    *has_holes = true;
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::Term(term) => match self.get_term(term) {
                Term::Hole(_) => {
                    *has_holes = true;
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(()),
            },
            Atom::FnDef(_) | Atom::Pat(_) => ControlFlow::Continue(()),
        }
    }

    /// Determines whether the given atom contains one or more holes.
    pub fn atom_has_holes(&self, atom: impl Into<Atom>) -> bool {
        let mut has_holes = false;
        self.traversing_utils()
            .visit_atom::<!, _>(atom.into(), &mut |atom| {
                Ok(self.has_holes_once(atom, &mut has_holes))
            })
            .into_ok();
        has_holes
    }

    /// Determines whether the given module definition contains one or more
    /// holes.
    pub fn mod_def_has_holes(&self, mod_def_id: ModDefId) -> bool {
        let mut has_holes = false;
        self.traversing_utils()
            .visit_mod_def::<!, _>(mod_def_id, &mut |atom| {
                Ok(self.has_holes_once(atom, &mut has_holes))
            })
            .into_ok();
        has_holes
    }

    /// Determines whether the given set of arguments contains one or more
    /// holes.
    pub fn args_have_holes(&self, args_id: ArgsId) -> bool {
        let mut has_holes = false;
        self.traversing_utils()
            .visit_args::<!, _>(args_id, &mut |atom| Ok(self.has_holes_once(atom, &mut has_holes)))
            .into_ok();
        has_holes
    }

    /// Determines whether the given set of parameters contains one or more
    /// holes.
    pub fn params_have_holes(&self, params_id: ParamsId) -> bool {
        let mut has_holes = false;
        self.traversing_utils()
            .visit_params::<!, _>(params_id, &mut |atom| {
                Ok(self.has_holes_once(atom, &mut has_holes))
            })
            .into_ok();
        has_holes
    }

    /// Create a substitution from the current stack members.
    pub fn create_sub_from_current_stack_members(&self) -> Sub {
        let mut sub = Sub::identity();

        let current_scope_index = self.context().get_current_scope_index();
        self.context().for_bindings_of_scope(current_scope_index, |binding| {
            if let BindingKind::StackMember(_, Some(value)) = binding.kind {
                sub.insert(binding.name, value);
            }
        });

        sub
    }

    /// Create a substitution from the given arguments.
    ///
    /// Invariant: the arguments are ordered to match the
    /// parameters.
    pub fn create_sub_from_args_of_params(&self, args_id: ArgsId, params_id: ParamsId) -> Sub {
        assert!(params_id.len() == args_id.len(), "called with mismatched args and params");

        let mut sub = Sub::identity();
        for (param_id, arg_id) in (params_id.iter()).zip(args_id.iter()) {
            let param = self.stores().params().get_element(param_id);
            let arg = self.stores().args().get_element(arg_id);
            sub.insert(param.name, arg.value);
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
            sub.insert(src.name, self.new_term(target.name));
        }
        sub
    }
}
