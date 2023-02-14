//! Logic for converting `hash-tir` types into `hash-ir` types. This is done
//! in order to simplify the lowering process when it needs to deal with types
//! of items. The full [Term] structure which is defined in the `hash-tir` is
//! not required for the IR generation stage, and often has un-needed terms for
//! the lowering process. This is why this builder is used to `lower` the [Term]
//! types into the [IrTy] which is then used for the lowering process.

use hash_intrinsics::{
    intrinsics::{BoolBinOp, EndoBinOp, UnOp},
    utils::PrimitiveUtils,
};
use hash_ir::{
    ir::{BinOp, Const, UnaryOp},
    ty::{IrTy, IrTyId},
};
use hash_source::constant::CONSTANT_MAP;
use hash_tir::{
    atom_info::ItemInAtomInfo, data::DataTy, environment::env::AccessToEnv, fns::FnCallTerm,
    lits::LitPat, pats::PatId, terms::TermId, tys::TyId,
};
use hash_utils::store::{SequenceStore, Store};

use super::Builder;
use crate::ty::TyLoweringCtx;

/// Convert a [LitTerm] into a [Const] value.
pub(super) fn constify_lit_pat(term: &LitPat) -> Const {
    match term {
        LitPat::Int(lit) => Const::Int(lit.interned_value()),
        LitPat::Str(lit) => Const::Str(lit.interned_value()),
        LitPat::Char(lit) => Const::Char(lit.value()),
    }
}

impl<'tcx> Builder<'tcx> {
    /// Get the [IrTyId] from a given [TermId]. This function will internally
    /// cache results of lowering a [TermId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(crate) fn ty_id_from_tir_term(&self, term: TermId) -> IrTyId {
        let ty = self.get_inferred_ty(term);

        let ctx = TyLoweringCtx { tcx: self.env(), lcx: self.ctx };
        ctx.ty_id_from_tir_ty(ty)
    }

    /// Get the [IrTy] from a given [TermId].
    pub(super) fn ty_from_tir_term(&mut self, term: TermId) -> IrTy {
        self.ty_from_tir_ty(self.get_inferred_ty(term))
    }

    /// Get the [IrTyId] from a given [TyId]. This function will internally
    /// cache results of lowering a [TyId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(super) fn ty_id_from_tir_ty(&self, ty: TyId) -> IrTyId {
        let ctx = TyLoweringCtx { tcx: self.env(), lcx: self.ctx };
        ctx.ty_id_from_tir_ty(ty)
    }

    /// Get the [IrTy] from a given [TyId].
    pub(super) fn ty_from_tir_ty(&self, ty: TyId) -> IrTy {
        self.stores().ty().map_fast(ty, |ty| {
            let ctx = TyLoweringCtx { tcx: self.env(), lcx: self.ctx };
            ctx.ty_from_tir_ty(ty)
        })
    }

    /// Get the [IrTyId] for a give [PatId].
    pub(super) fn ty_id_from_tir_pat(&self, pat: PatId) -> IrTyId {
        let ty = self.get_inferred_ty(pat);
        self.ty_id_from_tir_ty(ty)
    }

    /// Get the [IrTy] for a give [PatId].
    pub(super) fn ty_from_tir_pat(&self, pat: PatId) -> IrTy {
        let ty = self.get_inferred_ty(pat);
        self.ty_from_tir_ty(ty)
    }

    /// Get the [IrTyId] from the given [DataTy].
    pub(super) fn lower_nominal_as_id(&self, data: DataTy) -> IrTyId {
        let ctx = TyLoweringCtx { tcx: self.env(), lcx: self.ctx };
        ctx.ty_id_from_tir_data(data)
    }

    /// Check whether a given function call is a intrinsic indexing operation.
    pub(super) fn tir_fn_call_is_index(&self, subject: TermId) -> bool {
        todo!()
    }

    /// Check whether a given term is a intrinsic unary operation.
    pub(super) fn tir_term_is_un_op(&self, subject: TermId) -> bool {
        todo!()
    }

    /// Convert a [FnCallTerm] into an intrinsic unary operation.
    pub(super) fn tir_fn_call_as_un_op(&self, fn_call: &FnCallTerm) -> (UnaryOp, TermId) {
        let (op, arg) = (
            self.stores().args().get_at_index(fn_call.args, 0).value,
            self.stores().args().get_at_index(fn_call.args, 1).value,
        );

        // Parse the operator from the starting term as defined in `hash-intrinsics`
        let parsed_op =
            UnOp::try_from(self.try_use_term_as_integer_lit::<u8>(op).unwrap()).unwrap();
        (parsed_op.into(), arg)
    }

    /// Check whether a given term is a intrinsic binary operation.
    ///
    /// N.B. This does nothing for binary operations that involve the `&&` and
    /// the `||`
    pub(super) fn tir_fn_call_is_bool_binary_op(&self, subject: TermId) -> bool {
        todo!()
    }

    pub(super) fn tir_term_as_bool_op(&self, term: TermId) -> Option<BoolBinOp> {
        BoolBinOp::try_from(self.try_use_term_as_integer_lit::<u8>(term).unwrap()).ok()
    }

    /// Convert a [FnCallTerm] into an intrinsic binary operation which
    /// is not an "bool" binary operation.
    ///
    /// N.B. This does nothing for binary operations that involve the `&&` and
    /// the `||`
    pub(super) fn tir_fn_call_as_bool_binary_op(
        &self,
        fn_call: &FnCallTerm,
    ) -> Option<(BinOp, TermId, TermId)> {
        let (op, lhs, rhs) = (
            self.stores().args().get_at_index(fn_call.args, 0).value,
            self.stores().args().get_at_index(fn_call.args, 1).value,
            self.stores().args().get_at_index(fn_call.args, 2).value,
        );

        // Parse the operator from the starting term as defined in `hash-intrinsics`
        let value = self.try_use_term_as_integer_lit::<u8>(op).unwrap();

        let parsed_op = self.tir_term_as_bool_op(op).unwrap();

        // This is of been handled outside of this function.
        if parsed_op == BoolBinOp::And || parsed_op == BoolBinOp::Or {
            None
        } else {
            Some((parsed_op.into(), lhs, rhs))
        }
    }

    /// Check whether a given term is a intrinsic binary operation.
    pub(super) fn tir_fn_call_is_endo_binary_op(&self, subject: TermId) -> bool {
        todo!()
    }

    /// Convert a [FnCallTerm] into an intrinsic binary operation which
    /// is not an "endo" binary operation.
    pub(super) fn tir_fn_call_as_endo_binary_op(
        &self,
        fn_call: &FnCallTerm,
    ) -> (BinOp, TermId, TermId) {
        let (op, lhs, rhs) = (
            self.stores().args().get_at_index(fn_call.args, 0).value,
            self.stores().args().get_at_index(fn_call.args, 1).value,
            self.stores().args().get_at_index(fn_call.args, 2).value,
        );

        // Parse the operator from the starting term as defined in `hash-intrinsics`
        let value = self.try_use_term_as_integer_lit::<u8>(op).unwrap();

        let parsed_op =
            EndoBinOp::try_from(self.try_use_term_as_integer_lit::<u8>(op).unwrap()).unwrap();
        (parsed_op.into(), lhs, rhs)
    }

    /// Assuming that the provided [TermId] is a literal term, we essentially
    /// convert the term into a [Const] and return the value of the constant
    /// as a [u128]. This literal term must be an integral type.
    pub(crate) fn evaluate_const_pat(&self, pat: LitPat) -> (Const, u128) {
        match pat {
            LitPat::Int(lit) => {
                let value = lit.interned_value();

                CONSTANT_MAP.map_int_constant(value, |constant| {
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
