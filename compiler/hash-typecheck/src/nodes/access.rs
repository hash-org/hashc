use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::Context,
    tir::{AccessTerm, CtorTerm, Term, TermId, TupleTerm, Ty, TyId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    errors::{TcError, TcResult, WrongTermKind},
    operations::{
        normalisation::{
            stuck_normalising, NormalisationOptions, NormalisationState, NormaliseResult,
        },
        unification::UnificationOptions,
        Operations,
    },
};

impl<E: TcEnv> Operations<AccessTerm> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _ctx: &mut Context,
        access_term: &mut AccessTerm,
        annotation_ty: Self::TyNode,
        item_node: Self::Node,
    ) -> TcResult<()> {
        let subject_ty = Ty::hole_for(access_term.subject);
        self.infer_ops().infer_term(access_term.subject, subject_ty)?;

        let params = match *subject_ty.value() {
            Ty::TupleTy(tuple_ty) => tuple_ty.data,
            Ty::DataTy(data_ty) => {
                match data_ty.data_def.borrow().get_single_ctor() {
                    Some(ctor) => {
                        let ctor = ctor.value();
                        let data_def = data_ty.data_def.value();
                        let sub = self
                            .sub_ops()
                            .create_sub_from_args_of_params(data_ty.args, data_def.params);
                        self.sub_ops().apply_sub(ctor.params, &sub)
                    }
                    None => {
                        // Not a record type because it has more than one constructor
                        // @@ErrorReporting: more information about the error
                        return Err(TcError::WrongTy {
                            kind: WrongTermKind::NotARecord,
                            inferred_term_ty: subject_ty,
                            term: item_node,
                        });
                    }
                }
            }

            // Not a record type.
            _ => {
                return Err(TcError::WrongTy {
                    kind: WrongTermKind::NotARecord,
                    inferred_term_ty: subject_ty,
                    term: item_node,
                })
            }
        };

        if let Some(param) = params.at_index(access_term.field) {
            // Create a substitution that maps the parameters of the record
            // type to the corresponding fields of the record term.
            //
            // i.e. `x: (T: Type, t: T);  x.t: x.T`
            let param_access_sub =
                self.sub_ops().create_sub_from_param_access(params, access_term.subject);
            let subbed_param_ty = self.sub_ops().apply_sub(param.borrow().ty, &param_access_sub);
            self.infer_ops().check_by_unify(subbed_param_ty, annotation_ty)?;
            Ok(())
        } else {
            Err(TcError::PropertyNotFound {
                term: access_term.subject,
                term_ty: subject_ty,
                property: access_term.field,
            })
        }
    }

    fn normalise(
        &self,
        _: &mut Context,
        opts: &NormalisationOptions,
        access_term: &mut AccessTerm,
        term_id: Self::Node,
    ) -> NormaliseResult<()> {
        let st = NormalisationState::new();
        let norm_ops = self.norm_ops_with(opts);
        access_term.subject =
            (norm_ops.eval_and_record(access_term.subject.into(), &st)?).to_term();

        let result = match *access_term.subject.value() {
            Term::Tuple(TupleTerm { data: args })
            | Term::Ctor(CtorTerm { ctor_args: args, .. }) => {
                norm_ops.get_param_in_args(args, access_term.field)
            }
            _ => {
                return stuck_normalising();
            }
        };

        let result = norm_ops.eval_and_record(result, &st)?.to_term();
        term_id.set(result.value());

        st.done()
    }

    fn unify(
        &self,
        _ctx: &mut Context,
        opts: &UnificationOptions,
        src: &mut AccessTerm,
        target: &mut AccessTerm,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()> {
        let ops = self.uni_ops_with(opts);
        if src.field != target.field {
            return ops.mismatching_atoms(src_node, target_node);
        }
        ops.unify_terms(src.subject, target.subject)
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut AccessTerm) {
        todo!()
    }
}
