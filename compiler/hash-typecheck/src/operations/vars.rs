use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::HasContext,
    tir::{pats::BindingPat, PatId, Term, TermId, TyId, VarTerm},
    visitor::Map,
};

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{already_normalised, normalised_to, NormaliseResult},
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
};

impl<E: TcEnv> OperationsOn<VarTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        term: &mut VarTerm,
        annotation_ty: Self::AnnotNode,
        _: Self::Node,
    ) -> TcResult<()> {
        let term = *term;
        match self.context().try_get_decl(term.symbol) {
            Some(decl) => {
                if let Some(ty) = decl.ty {
                    let ty = self.visitor().copy(ty);
                    self.check_ty(ty)?;
                    self.unify_nodes(ty, annotation_ty)?;
                    Ok(())
                } else if decl.value.is_some() {
                    panic!("no type found for decl '{}'", decl)
                } else {
                    panic!("Found declaration without type or value during inference: {}", decl)
                }
            }
            None => {
                panic!("no binding found for symbol '{}'", term)
            }
        }
    }

    fn try_normalise(&self, item: VarTerm, _: Self::Node) -> NormaliseResult<ControlFlow<TermId>> {
        let var = item.symbol;
        match self.context().try_get_decl_value(var) {
            Some(result) => {
                if matches!(*result.value(), Term::Var(v) if v.symbol == var) {
                    already_normalised()
                } else {
                    normalised_to(self.normalise_node(result)?)
                }
            }
            None => already_normalised(),
        }
    }

    fn unify(
        &self,
        src: &mut VarTerm,
        _: &mut VarTerm,
        a_id: Self::Node,
        b_id: Self::Node,
    ) -> TcResult<()> {
        self.unify_var_with(*src, a_id, b_id)
    }
}

impl<E: TcEnv> Tc<'_, E> {
    pub(crate) fn unify_var_with(
        &self,
        var: VarTerm,
        var_term: TermId,
        term: TermId,
    ) -> TcResult<()> {
        match self.context().try_get_decl_value(var.symbol) {
            Some(v) => self.unify_nodes(v, term),
            None => self.mismatching_atoms(var_term, term),
        }
    }

    pub(crate) fn unify_binding_with(&self, binding: BindingPat, term: TermId) -> TcResult<()> {
        self.add_unification(binding.name, term);
        Ok(())
    }
}

impl<E: TcEnv> OperationsOn<BindingPat> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        var: &mut BindingPat,
        annotation_ty: Self::AnnotNode,
        _: Self::Node,
    ) -> TcResult<()> {
        self.check_ty(annotation_ty)?;
        self.context().add_typing_to_closest_stack(var.name, annotation_ty);
        Ok(())
    }

    fn try_normalise(
        &self,
        _item: BindingPat,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        already_normalised()
    }

    fn unify(
        &self,
        src: &mut BindingPat,
        target: &mut BindingPat,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()> {
        self.unify(
            &mut VarTerm { symbol: src.name },
            &mut VarTerm { symbol: target.name },
            src_node,
            target_node,
        )
    }
}
