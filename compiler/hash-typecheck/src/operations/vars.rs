use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::HasContext,
    tir::{PatId, Term, TermId, TyId, VarTerm, pats::BindingPat},
    visitor::Map,
};

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{NormaliseResult, already_normalised, normalised_to},
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
        target: &mut VarTerm,
        a_id: Self::Node,
        b_id: Self::Node,
    ) -> TcResult<()> {
        let a = src.symbol;
        let b = target.symbol;
        if let Some(binds) = &*self.unification_opts.pat_binds.get() {
            if binds.contains(&a) {
                self.add_unification(b, a_id);
                return Ok(());
            }
            if binds.contains(&b) {
                self.add_unification(a, b_id);
                return Ok(());
            }
        }
        if a == b { Ok(()) } else { self.mismatching_atoms(a_id, b_id) }
    }
}

impl<E: TcEnv> OperationsOn<BindingPat> for Tc<'_, E> {
    type AnnotNode = (TyId, Option<TermId>);
    type Node = PatId;

    fn check(
        &self,
        var: &mut BindingPat,
        (annotation_ty, binds_to): Self::AnnotNode,
        _: Self::Node,
    ) -> TcResult<()> {
        self.check_ty(annotation_ty)?;
        match binds_to {
            Some(value) if self.has_effects(value) == Some(false) => {
                self.context().add_assignment_to_closest_stack(var.name, annotation_ty, value);
            }
            _ => {
                self.context().add_typing_to_closest_stack(var.name, annotation_ty);
            }
        }
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
        self.unification_ok_or_mismatching_atoms(
            src.name == target.name && src.is_mutable == target.is_mutable,
            src_node,
            target_node,
        )
    }
}
