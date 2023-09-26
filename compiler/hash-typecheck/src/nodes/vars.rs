use hash_storage::store::statics::StoreId;
use hash_tir::{
    tir::{Term, TermId, TyId, VarTerm},
    visitor::{Map, Visitor},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{
        checking::did_check,
        normalisation::{already_normalised, normalised, NormalisationOptions},
        unification::UnificationOptions,
        Operations,
    },
};

impl<E: TcEnv> Operations<VarTerm> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _ctx: &mut hash_tir::context::Context,
        term: &mut VarTerm,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> crate::operations::checking::CheckResult {
        let term = *term;
        match self.context().try_get_decl(term.symbol) {
            Some(decl) => {
                if let Some(ty) = decl.ty {
                    let ty = Visitor::new().copy(ty);
                    self.infer_ops().check_ty(ty)?;
                    self.uni_ops().unify_terms(ty, annotation_ty)?;
                    did_check(())
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
        _ctx: &mut hash_tir::context::Context,
        _opts: &NormalisationOptions,
        item: &mut VarTerm,
        item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<()> {
        let var = item.symbol;
        match self.context().try_get_decl_value(var) {
            Some(result) => {
                if matches!(*result.value(), Term::Var(v) if v.symbol == var) {
                    already_normalised()
                } else {
                    let actual = self.norm_ops().eval(result.into())?;
                    item_node.set(actual.to_term().value());
                    normalised()
                }
            }
            None => already_normalised(),
        }
    }

    fn unify(
        &self,
        _ctx: &mut hash_tir::context::Context,
        opts: &UnificationOptions,
        src: &mut VarTerm,
        target: &mut VarTerm,
        a_id: Self::Node,
        b_id: Self::Node,
    ) -> crate::operations::unification::UnifyResult {
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
            uni_ops.mismatching_atoms(a_id, b_id)?;
            Ok(())
        }
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut VarTerm) {
        todo!()
    }
}