use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    context::HasContext,
    intrinsics::definitions::never_ty,
    scopes::{BlockStatement, BlockTerm},
    tir::{NodeOrigin, TermId, Ty, TyId},
};

use crate::{
    env::TcEnv,
    errors::{TcError, TcResult},
    options::normalisation::NormaliseResult,
    tc::{FnInferMode, Tc},
    traits::{Operations, OperationsOnNode},
};

impl<E: TcEnv> Operations<BlockTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        block_term: &mut BlockTerm,
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        self.context().enter_scope(block_term.stack_id.into(), || {
            // Handle local mod def
            let stack = block_term.stack_id.value();
            if let Some(local_mod_def) = stack.local_mod_def {
                // @@Improvement: it would be nice to pass through local
                // mod defs in two stages as well.
                self.fn_infer_mode
                    .enter(FnInferMode::Body, || self.check_node(local_mod_def, ()))?
            }

            // Keep track of statements diverging, so we can infer the appropriate return
            // type.
            let mut diverges = false;

            for statement in block_term.statements.iter() {
                let ty_to_check_divergence = match *statement.value() {
                    BlockStatement::Decl(decl) => {
                        self.check_ty(decl.ty)?;
                        self.check_node(decl.value, decl.ty)?;
                        self.check_node(decl.bind_pat, (decl.ty, Some(decl.value)))?;

                        // Check that the binding pattern of the declaration is irrefutable.
                        let mut eck = self.exhaustiveness_checker(decl.bind_pat);

                        self.env.time_item("exhaustiveness", |_| {
                            eck.is_pat_irrefutable(&[decl.bind_pat], decl.ty, None)
                        });
                        self.append_exhaustiveness_diagnostics(eck);

                        decl.ty
                    }
                    BlockStatement::Expr(expr) => {
                        let statement_ty = Ty::hole_for(expr);
                        self.check_node(expr, statement_ty)?;
                        statement_ty
                    }
                };

                // If the statement diverges, we can already exit
                if self.is_uninhabitable(ty_to_check_divergence)? {
                    diverges = true;
                }
            }

            if diverges {
                match *annotation_ty.value() {
                    Ty::Hole(_) => {
                        // If it diverges, we can just infer the return type as `never`.
                        let block_term_ty =
                            Ty::expect_is(original_term_id, never_ty(NodeOrigin::Expected));
                        self.check_by_unify(block_term_ty, annotation_ty)?;
                    }
                    _ => {
                        // Infer the return value
                        let return_value_ty = Ty::hole_for(block_term.expr);
                        self.check_node(block_term.expr, return_value_ty)?;
                    }
                }
            } else {
                // Infer the return value
                self.check_node(block_term.expr, annotation_ty)?;
            };

            let sub = self.substituter().create_sub_from_current_scope();
            self.substituter().apply_sub_in_place(annotation_ty, &sub);

            let sub_ops = self.substituter();
            let vars_in_scope = sub_ops.get_unassigned_vars_in_current_scope();
            if sub_ops.atom_contains_vars(annotation_ty.into(), &vars_in_scope) {
                return Err(TcError::TryingToReferenceLocalsInType { ty: annotation_ty });
            }

            Ok(())
        })
    }

    fn normalise(&self, _item: BlockTerm, _item_node: Self::Node) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify(
        &self,
        _src: &mut BlockTerm,
        _target: &mut BlockTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        todo!()
    }
}
