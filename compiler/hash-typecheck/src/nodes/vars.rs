use hash_tir::{
    tir::{TermId, TyId, VarTerm},
    visitor::{Map, Visitor},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{checking::did_check, Operations},
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
        _item: &mut VarTerm,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut hash_tir::context::Context,
        _src: &mut VarTerm,
        _target: &mut VarTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::operations::unification::UnifyResult {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut VarTerm) {
        todo!()
    }
}
