use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::HasContext,
    scopes::BindingPat,
    tir::{PatId, Term, TermId, TyId, VarTerm},
    visitor::Map,
};

use crate::{
    env::TcEnv,
    errors::TcResult,
    options::normalisation::{already_normalised, normalised_to},
    tc::Tc,
    traits::{Operations, OperationsOnNode},
};

impl<E: TcEnv> Operations<VarTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        term: &mut VarTerm,
        annotation_ty: Self::TyNode,
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

    fn try_normalise(
        &self,
        item: VarTerm,
        _: Self::Node,
    ) -> crate::options::normalisation::NormaliseResult<TermId> {
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
        if a == b {
            Ok(())
        } else {
            self.mismatching_atoms(a_id, b_id)
        }
    }
}

impl<E: TcEnv> Operations<BindingPat> for Tc<'_, E> {
    type TyNode = (TyId, Option<TermId>);
    type Node = PatId;

    fn check(
        &self,
        var: &mut BindingPat,
        (annotation_ty, binds_to): Self::TyNode,
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
    ) -> crate::options::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _src: &mut BindingPat,
        _target: &mut BindingPat,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }
}
