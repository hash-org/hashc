use hash_attrs::{attr::attr_store, builtin::attrs};
use hash_tir::tir::{FnTy, HasAstNodeId, TermId, TyId};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    operations::{normalisation::NormalisationMode, OperationsOnNode},
};

impl<E: TcEnv> Tc<'_, E> {
    /// Potentially run an expression at compile-time.
    ///
    /// This is only done if the expression has a `#run` annotation.
    pub fn potentially_run_expr(&self, expr: TermId, term_ty: TyId) -> TcResult<()> {
        if self.should_monomorphise() {
            let has_run_directive = if let Some(id) = expr.node_id() {
                attr_store().node_has_attr(id, attrs::RUN)
            } else {
                false
            };

            if has_run_directive {
                let norm_ops = self.norm_ops();
                norm_ops.with_mode(NormalisationMode::Full);
                if norm_ops.normalise_in_place(expr.into())? {
                    self.check_node(expr, term_ty)?;
                }
            }
        }
        Ok(())
    }

    /// Potentially monomorphise a function call, if it is pure.
    pub fn potentially_monomorphise_fn_call(
        &self,
        fn_call: TermId,
        fn_ty: FnTy,
        fn_call_result_ty: TyId,
    ) -> TcResult<()> {
        if self.should_monomorphise() && fn_ty.pure {
            let norm_ops = self.norm_ops();
            norm_ops.with_mode(NormalisationMode::Full);
            if norm_ops.normalise_in_place(fn_call.into())? {
                self.check_node(fn_call, fn_call_result_ty)?;
            }
        }
        Ok(())
    }
}
