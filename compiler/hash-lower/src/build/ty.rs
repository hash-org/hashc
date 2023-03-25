//! Logic for converting `hash-tir` types into `hash-ir` types. This is done
//! in order to simplify the lowering process when it needs to deal with types
//! of items. The full [Term] structure which is defined in the `hash-tir` is
//! not required for the IR generation stage, and often has un-needed terms for
//! the lowering process. This is why this builder is used to `lower` the [Term]
//! types into the [IrTy] which is then used for the lowering process.

use hash_intrinsics::{
    intrinsics::{AccessToIntrinsics, BoolBinOp, EndoBinOp, ShortCircuitBinOp, UnOp},
    utils::PrimitiveUtils,
};
use hash_ir::{
    ir::{self, Const},
    ty::IrTyId,
};
use hash_source::constant::CONSTANT_MAP;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    data::DataTy,
    environment::env::AccessToEnv,
    fns::{FnCallTerm, FnDefId},
    lits::LitPat,
    pats::PatId,
    terms::{Term, TermId},
    tys::TyId,
    utils::common::CommonUtils,
};
use hash_utils::store::SequenceStore;

use super::BodyBuilder;

/// An auxiliary data structure that represents the underlying [FnCallTerm]
/// as either being a function call, a binary operation (of various kinds), or
/// a an index operation.
///
/// The [FnCallTermKind] is used beyond the semantic stage of the compiler to
/// help the lowering stage distinguish between these cases.
pub enum FnCallTermKind {
    /// A function call, the term doesn't change and should just be
    /// handled as a function call.
    Call(FnCallTerm),

    /// A cast intrinsic operation, we perform a cast from the type of the
    /// first term into the desired second [IrTyId].
    Cast(TermId, IrTyId),

    /// A "boolean" binary operation which takes two terms and yields a boolean
    /// term as a result.
    BinaryOp(ir::BinOp, TermId, TermId),

    /// A short-circuiting boolean binary operation, the term should be lowered
    /// into the equivalent of `a && b` or `a || b`.
    LogicalBinOp(ir::LogicalBinOp, TermId, TermId),

    /// An "unary" operation, the term should be lowered into the equivalent
    /// unary operation.
    UnaryOp(ir::UnaryOp, TermId),
}

impl<'tcx> BodyBuilder<'tcx> {
    /// Get the [IrTyId] from a given [TermId]. This function will internally
    /// cache results of lowering a [TermId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(crate) fn ty_id_from_tir_term(&self, term: TermId) -> IrTyId {
        let ty = self.get_inferred_ty(term);
        self.ctx.ty_id_from_tir_ty(ty)
    }

    /// Get the [IrTyId] for a give [PatId].
    pub(super) fn ty_id_from_tir_pat(&self, pat: PatId) -> IrTyId {
        let ty = self.get_inferred_ty(pat);
        self.ty_id_from_tir_ty(ty)
    }

    /// Create an ADT from a defined [DataTy].
    pub(crate) fn ty_id_from_tir_data(&self, data_ty: DataTy) -> IrTyId {
        self.ctx.ty_from_tir_data(data_ty)
    }

    /// Create an function type from the given [FnDefId].
    pub(super) fn ty_id_from_tir_fn_def(&mut self, fn_def: FnDefId) -> IrTyId {
        self.ctx.ty_id_from_tir_fn_def(fn_def)
    }

    /// Get the [IrTyId] from a given [TyId]. This function will internally
    /// cache results of lowering a [TyId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(super) fn ty_id_from_tir_ty(&self, ty: TyId) -> IrTyId {
        self.ctx.ty_id_from_tir_ty(ty)
    }

    /// Function which is used to classify a [FnCallTerm] into a
    /// [FnCallTermKind].
    pub(crate) fn classify_fn_call_term(&self, term: &FnCallTerm) -> FnCallTermKind {
        let FnCallTerm { subject, args, .. } = term;

        match self.get_term(*subject) {
            Term::FnRef(fn_def) => {
                // Check if the fn_def is a `un_op` intrinsic
                if fn_def == self.intrinsics().un_op() {
                    let (op, subject) = (
                        self.stores().args().get_at_index(*args, 1).value,
                        self.stores().args().get_at_index(*args, 2).value,
                    );

                    // Parse the operator from the starting term as defined in `hash-intrinsics`
                    let parsed_op =
                        UnOp::try_from(self.try_use_term_as_integer_lit::<u8>(op).unwrap())
                            .unwrap();

                    FnCallTermKind::UnaryOp(parsed_op.into(), subject)
                } else if fn_def == self.intrinsics().short_circuiting_op() {
                    let (op, lhs, rhs) = (
                        self.stores().args().get_at_index(*args, 1).value,
                        self.stores().args().get_at_index(*args, 2).value,
                        self.stores().args().get_at_index(*args, 3).value,
                    );

                    let op = ShortCircuitBinOp::try_from(
                        self.try_use_term_as_integer_lit::<u8>(op).unwrap(),
                    )
                    .unwrap();

                    FnCallTermKind::LogicalBinOp(op.into(), lhs, rhs)
                } else if fn_def == self.intrinsics().endo_bin_op() {
                    let (op, lhs, rhs) = (
                        self.stores().args().get_at_index(*args, 1).value,
                        self.stores().args().get_at_index(*args, 2).value,
                        self.stores().args().get_at_index(*args, 3).value,
                    );

                    let op =
                        EndoBinOp::try_from(self.try_use_term_as_integer_lit::<u8>(op).unwrap())
                            .unwrap();
                    FnCallTermKind::BinaryOp(op.into(), lhs, rhs)
                } else if fn_def == self.intrinsics().bool_bin_op() {
                    let (op, lhs, rhs) = (
                        self.stores().args().get_at_index(*args, 1).value,
                        self.stores().args().get_at_index(*args, 2).value,
                        self.stores().args().get_at_index(*args, 3).value,
                    );

                    let op =
                        BoolBinOp::try_from(self.try_use_term_as_integer_lit::<u8>(op).unwrap())
                            .unwrap();
                    FnCallTermKind::BinaryOp(op.into(), lhs, rhs)
                } else if fn_def == self.intrinsics().cast() {
                    let (to_ty, value) = (
                        self.stores().args().get_at_index(*args, 1).value,
                        self.stores().args().get_at_index(*args, 2).value,
                    );

                    // Convert the `to_ty` into an IR type and
                    let to_ty = self.use_term_as_ty(to_ty);
                    let ty = self.ty_id_from_tir_ty(to_ty);

                    FnCallTermKind::Cast(value, ty)
                } else {
                    FnCallTermKind::Call(*term)
                }
            }
            Term::FnCall(_) => FnCallTermKind::Call(*term),
            term => panic!("unexpected term in classify_fn_call_term() `{term:?}`"),
        }
    }

    /// Assuming that the provided [TermId] is a literal term, we essentially
    /// convert the term into a [Const] and return the value of the constant
    /// as a [u128]. This literal term must be an integral type.
    pub(crate) fn evaluate_const_pat(&self, pat: LitPat) -> (Const, u128) {
        match pat {
            LitPat::Int(lit) => {
                let value = lit.interned_value();

                CONSTANT_MAP.map_int(value, |constant| {
                    (Const::Int(value), constant.value.as_u128().unwrap())
                })
            }
            LitPat::Char(lit) => {
                let value = lit.value();
                (Const::Char(value), u128::from(value))
            }
            _ => unreachable!(),
        }
    }
}
