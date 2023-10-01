use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::{HasContext, ScopeKind},
    tir::{Arg, CallTerm, Term, TermId, Ty, TyId},
    visitor::Map,
};

use crate::{
    env::TcEnv,
    errors::{TcError, TcResult, WrongTermKind},
    options::normalisation::NormaliseResult,
    tc::Tc,
    utils::operation_traits::{Operations, OperationsOnNode, RecursiveOperationsOnNode},
};

impl<E: TcEnv> Operations<CallTerm> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        call_term: &mut CallTerm,
        annotation_ty: Self::TyNode,
        original_term_id: Self::Node,
    ) -> TcResult<()> {
        self.context().enter_scope(ScopeKind::Sub, || {
            self.normalise_and_check_ty(annotation_ty)?;
            let inferred_subject_ty = Ty::hole_for(call_term.subject);
            self.check_node(call_term.subject, inferred_subject_ty)?;

            match *inferred_subject_ty.value() {
                Ty::FnTy(fn_ty) => {
                    // Potentially fill-in implicit args
                    if let Ty::FnTy(_) = *fn_ty.return_ty.value() && fn_ty.implicit && !call_term.implicit {
                        let applied_args = Arg::seq_from_params_as_holes(fn_ty.params);
                        let copied_subject = Term::inherited_from(call_term.subject, *call_term.subject.value());
                        let new_subject = CallTerm {
                            args: applied_args,
                            subject: copied_subject,
                            implicit: fn_ty.implicit,
                        };
                        call_term.subject.set(call_term.subject.value().with_data(new_subject.into()));
                        return self.check(call_term, annotation_ty, original_term_id);
                    }

                    // Check that the function call is of the correct kind.
                    if fn_ty.implicit != call_term.implicit {
                        return Err(TcError::WrongCallKind {
                            site: original_term_id,
                            expected_implicit: fn_ty.implicit,
                            actual_implicit: call_term.implicit,
                        });
                    }

                    let copied_params = self.visitor().copy(fn_ty.params);
                    let copied_return_ty = self.visitor().copy(fn_ty.return_ty);

                    let mut fn_call_term = *call_term;
                    self.check_node_rec(fn_call_term.args, copied_params, |inferred_fn_call_args| {
                        fn_call_term.args = inferred_fn_call_args;
                        original_term_id.set(original_term_id.value().with_data(fn_call_term.into()));

                        self.substituter().apply_sub_from_context(copied_return_ty);
                        self.check_by_unify(copied_return_ty, annotation_ty)?;
                        Ok(())
                    })?;

                    self.substituter().apply_sub_from_context(fn_call_term.subject);
                    self.potentially_monomorphise_fn_call(original_term_id, fn_ty, annotation_ty)?;

                    Ok(())
                }
                _ => {
                    // Not a function type.
                    Err(TcError::WrongTy {
                        kind: WrongTermKind::NotAFunction,
                        inferred_term_ty: inferred_subject_ty,
                        term: original_term_id,
                    })
                }
            }
        })
    }

    fn normalise(&self, _item: CallTerm, _item_node: Self::Node) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify(
        &self,

        src: &mut CallTerm,
        target: &mut CallTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> TcResult<()> {
        self.unify_nodes(src.subject, target.subject)?;
        self.unify_nodes_rec(src.args, target.args, |_| Ok(()))?;
        Ok(())
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut CallTerm) {
        todo!()
    }
}
