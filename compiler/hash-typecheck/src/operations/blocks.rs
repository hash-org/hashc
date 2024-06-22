use std::ops::ControlFlow;

use hash_storage::store::{statics::StoreId, SequenceStoreKey, TrivialSequenceStoreKey};
use hash_tir::{
    context::{HasContext, ScopeKind},
    intrinsics::definitions::never_ty,
    tir::{
        blocks::{BlockStatement, BlockTerm},
        NodeOrigin, TermId, Ty, TyId,
    },
};
use hash_utils::log::info;

use crate::{
    diagnostics::{TcError, TcResult},
    env::TcEnv,
    options::normalisation::{normalised_to, NormalisationState, NormaliseResult},
    tc::{FnInferMode, Tc},
    traits::{OperationsOn, OperationsOnNode},
    utils::matching::MatchResult,
};

impl<E: TcEnv> OperationsOn<BlockTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        block_term: &mut BlockTerm,
        annotation_ty: Self::AnnotNode,
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
                        self.check_node(decl.ty, Ty::universe_of(decl.ty))?;
                        self.check_node(decl.value, decl.ty)?;
                        self.in_pat.enter(true, || self.check_node(decl.bind_pat, decl.ty))?;

                        // Check that the binding pattern of the declaration is irrefutable.
                        // let mut eck = self.exhaustiveness_checker(decl.bind_pat);

                        // self.env.record("exhaustiveness", |_| {
                        //     eck.is_pat_irrefutable(&[decl.bind_pat], decl.ty, None)
                        // });
                        // self.append_exhaustiveness_diagnostics(eck);

                        decl.ty
                    }
                    BlockStatement::Expr(expr) => {
                        let statement_ty = self.fresh_meta_for(expr);
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
                    Ty::Meta(_) => {
                        // If it diverges, we can just infer the return type as `never`.
                        let block_term_ty =
                            Ty::expect_is(original_term_id, never_ty(NodeOrigin::Expected));
                        self.unify_nodes(block_term_ty, annotation_ty)?;
                    }
                    _ => {
                        // Infer the return value
                        let return_value_ty = self.fresh_meta_for(block_term.expr);
                        self.check_node(block_term.expr, return_value_ty)?;
                    }
                }
            } else {
                // Infer the return value
                self.check_node(block_term.expr, annotation_ty)?;
            };

            let sub = self.substituter().create_sub_from_current_scope();
            self.substituter().apply_sub_in_place(annotation_ty, &sub);

            let subber = self.substituter();
            let vars_in_scope = subber.get_unassigned_vars_in_current_scope();
            if subber.contains_vars(annotation_ty, &vars_in_scope) {
                return Err(TcError::TryingToReferenceLocalsInType { ty: annotation_ty });
            }

            Ok(())
        })
    }

    fn try_normalise(
        &self,
        block_term: BlockTerm,
        _: Self::Node,
    ) -> NormaliseResult<ControlFlow<TermId>> {
        self.context().enter_scope(ScopeKind::Stack(block_term.stack_id), || {
            let st = NormalisationState::new();

            for statement in block_term.statements.iter() {
                match *statement.value() {
                    BlockStatement::Decl(mut decl_term) => {
                        decl_term.value =
                            self.normalise_nested_node_and_record(decl_term.value, &st)?;

                        match self.match_value_and_get_binds(
                            decl_term.value,
                            decl_term.bind_pat,
                            &mut |name, term_id| {
                                self.context().add_assignment(name, term_id)
                            },
                        )? {
                            MatchResult::Successful => {
                                // All good
                            }
                            MatchResult::Failed => {
                                panic!("Non-exhaustive let-binding: {}", decl_term)
                            }
                            MatchResult::Stuck => {
                                info!("Stuck evaluating let-binding: {}", decl_term);
                            }
                        }
                    }
                    BlockStatement::Expr(expr) => {
                        let _ = self.normalise_node_and_record(expr, &st)?;
                    }
                }
            }

            let sub = self.substituter().create_sub_from_current_scope();
            let result_term = self.normalise_node_and_record(block_term.expr, &st)?;
            let subbed_result_term = self.substituter().apply_sub(result_term, &sub);

            normalised_to(subbed_result_term)
        })
    }

    fn unify(
        &self,
        src: &mut BlockTerm,
        target: &mut BlockTerm,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()> {
        if src.statements.len() != target.statements.len() {
            return self.mismatching_atoms(src_node, target_node);
        }

        for (src_statement, target_statement) in src.statements.iter().zip(target.statements.iter())
        {
            match (src_statement.value().data, target_statement.value().data) {
                (BlockStatement::Decl(src_decl), BlockStatement::Decl(target_decl)) => {
                    self.unify_nodes(src_decl.value, target_decl.value)?;
                }
                (BlockStatement::Expr(src_expr), BlockStatement::Expr(target_expr)) => {
                    self.unify_nodes(src_expr, target_expr)?;
                }
                _ => return self.mismatching_atoms(src_node, target_node),
            }
        }

        Ok(())
    }
}
