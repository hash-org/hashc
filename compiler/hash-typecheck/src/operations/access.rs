use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::tir::{AccessTerm, CtorTerm, Term, TermId, TupleTerm, Ty, TyId};

use crate::{
    env::TcEnv,
    errors::{TcError, TcResult, WrongTermKind},
    options::normalisation::{
        normalised_if, stuck_normalising, NormalisationState, NormaliseResult,
    },
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
};

impl<E: TcEnv> OperationsOn<AccessTerm> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        access_term: &mut AccessTerm,
        annotation_ty: Self::AnnotNode,
        item_node: Self::Node,
    ) -> TcResult<()> {
        let subject_ty = Ty::hole_for(access_term.subject);
        self.check_node(access_term.subject, subject_ty)?;

        let params = match *subject_ty.value() {
            Ty::TupleTy(tuple_ty) => tuple_ty.data,
            Ty::DataTy(data_ty) => {
                match data_ty.data_def.borrow().get_single_ctor() {
                    Some(ctor) => {
                        let ctor = ctor.value();
                        let data_def = data_ty.data_def.value();
                        let sub = self
                            .substituter()
                            .create_sub_from_args_of_params(data_ty.args, data_def.params);
                        self.substituter().apply_sub(ctor.params, &sub)
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
                self.substituter().create_sub_from_param_access(params, access_term.subject);
            let subbed_param_ty =
                self.substituter().apply_sub(param.borrow().ty, &param_access_sub);
            self.check_by_unify(subbed_param_ty, annotation_ty)?;
            Ok(())
        } else {
            Err(TcError::PropertyNotFound {
                term: access_term.subject,
                term_ty: subject_ty,
                property: access_term.field,
            })
        }
    }

    fn try_normalise(
        &self,
        mut access_term: AccessTerm,
        _: Self::Node,
    ) -> NormaliseResult<ControlFlow<TermId>> {
        let st = NormalisationState::new();
        access_term.subject = self.normalise_node_and_record(access_term.subject, &st)?;

        let result = match *access_term.subject.value() {
            Term::Tuple(TupleTerm { data: args })
            | Term::Ctor(CtorTerm { ctor_args: args, .. }) => {
                self.get_param_in_args(args, access_term.field)
            }
            _ => {
                return stuck_normalising();
            }
        };
        let evaluated = self.normalise_node_and_record(result, &st)?;
        normalised_if(|| evaluated, &st)
    }

    fn unify(
        &self,
        src: &mut AccessTerm,
        target: &mut AccessTerm,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()> {
        if src.field != target.field {
            return self.mismatching_atoms(src_node, target_node);
        }
        self.unify_nodes(src.subject, target.subject)
    }
}
