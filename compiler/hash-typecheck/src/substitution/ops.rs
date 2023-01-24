//! Operations to substitute variables in types and terms.

use std::ops::ControlFlow;

use derive_more::{Constructor, Deref};
use hash_tir::new::{
    args::ArgsId,
    defs::DefArgsId,
    params::ParamsId,
    terms::{Term, TermId},
    tys::{Ty, TyId},
    utils::{common::CommonUtils, traversing::Atom, AccessToUtils},
};
use hash_utils::store::{SequenceStoreKey, Store};

use super::sub::Sub;
use crate::{errors::TcResult, AccessToTypechecking};

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
                Ty::Var(var_ty) => match sub.get_sub_for(var_ty) {
                    Some(term) => {
                        let subbed_ty = self.get_ty(self.use_term_as_ty_or_eval(term));
                        self.stores().ty().modify_fast(ty, |ty| *ty = subbed_ty);
                        ControlFlow::Break(())
                    }
                    None => ControlFlow::Continue(()),
                },
                _ => ControlFlow::Continue(()),
            },
            Atom::Term(term) => match self.get_term(term) {
                Term::Var(var_term) => match sub.get_sub_for(var_term) {
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
                Ty::Var(var_ty) => match sub.get_sub_for(var_ty) {
                    Some(term) => ControlFlow::Break(Atom::Ty(self.use_term_as_ty_or_eval(term))),
                    None => ControlFlow::Continue(()),
                },
                _ => ControlFlow::Continue(()),
            },
            Atom::Term(term) => match self.get_term(term) {
                Term::Var(var_term) => match sub.get_sub_for(var_term) {
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

    pub fn apply_sub_to_def_args_in_place(&self, def_args_id: DefArgsId, sub: &Sub) {
        self.traversing_utils()
            .visit_def_args::<!, _>(def_args_id, &mut |atom| {
                Ok(self.apply_sub_to_atom_in_place_once(atom, sub))
            })
            .into_ok()
    }

    pub fn apply_sub_to_args_in_place(&self, args_id: ArgsId, sub: &Sub) {
        self.traversing_utils()
            .visit_args::<!, _>(args_id, &mut |atom| {
                Ok(self.apply_sub_to_atom_in_place_once(atom, sub))
            })
            .into_ok()
    }

    /// Create a substitution from applying the arguments to the parameters.
    ///
    /// For argument terms `a1, a2, ..., an` and parameter indices `p1, p2, ...,
    /// pn` this creates a substitution `s` such that `s(p1) = a1, s(p2) =
    /// a2, ..., s(pn) = an`.
    pub fn create_sub_from_applying_args_to_params(
        &self,
        args_id: ArgsId,
        params_id: ParamsId,
    ) -> TcResult<Sub> {
        assert!(args_id.len() == params_id.len());
        todo!()
    }
}
