use hash_storage::store::statics::StoreId;
use hash_tir::{
    scopes::BindingPat,
    tir::{PatId, Term, TermId, TyId, VarTerm},
    visitor::{Map, Visitor},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    operations::{
        normalisation::{already_normalised, normalised_to, NormalisationOptions},
        unification::UnificationOptions,
        Operations,
    },
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
                    let ty = Visitor::new().copy(ty);
                    self.check_ty(ty)?;
                    self.uni_ops().unify_terms(ty, annotation_ty)?;
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

    fn normalise(
        &self,
        _opts: &NormalisationOptions,
        item: VarTerm,
        _: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<TermId> {
        let var = item.symbol;
        match self.context().try_get_decl_value(var) {
            Some(result) => {
                if matches!(*result.value(), Term::Var(v) if v.symbol == var) {
                    already_normalised()
                } else {
                    let actual = self.norm_ops().eval(result.into())?;
                    normalised_to(actual.to_term())
                }
            }
            None => already_normalised(),
        }
    }

    fn unify(
        &self,
        opts: &UnificationOptions,
        src: &mut VarTerm,
        target: &mut VarTerm,
        a_id: Self::Node,
        b_id: Self::Node,
    ) -> TcResult<()> {
        let a = src.symbol;
        let b = target.symbol;
        let uni_ops = self.uni_ops_with(opts);

        if let Some(binds) = opts.pat_binds.get() {
            if binds.contains(&a) {
                uni_ops.add_unification(b, a_id);
                return Ok(());
            }
            if binds.contains(&b) {
                uni_ops.add_unification(a, b_id);
                return Ok(());
            }
        }
        if a == b {
            Ok(())
        } else {
            uni_ops.mismatching_atoms(a_id, b_id)
        }
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut VarTerm) {
        todo!()
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
            Some(value) if self.norm_ops().atom_has_effects(value.into()) == Some(false) => {
                self.context().add_assignment_to_closest_stack(var.name, annotation_ty, value);
            }
            _ => {
                self.context().add_typing_to_closest_stack(var.name, annotation_ty);
            }
        }
        Ok(())
    }

    fn normalise(
        &self,
        _opts: &NormalisationOptions,
        _item: BindingPat,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &UnificationOptions,
        _src: &mut BindingPat,
        _target: &mut BindingPat,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut BindingPat) {
        todo!()
    }
}
