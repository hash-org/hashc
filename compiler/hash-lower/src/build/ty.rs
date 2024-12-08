//! Logic for converting `hash-tir` types into `hash-ir` types. This is done
//! in order to simplify the lowering process when it needs to deal with types
//! of items. The full [Term] structure which is defined in the `hash-tir` is
//! not required for the IR generation stage, and often has un-needed terms for
//! the lowering process. This is why this builder is used to `lower` the [Term]
//! types into the [ReprTy] which is then used for the lowering process.

use hash_ast::ast::AstNodeId;
use hash_const_eval::{
    op::{BinOp, LogicalBinOp, UnOp},
    Const, ConstKind,
};
use hash_ir::{
    ir::{BodyInfo, Scalar},
    ty::{ReprTy, ReprTyId},
};
use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_target::{size::Size, HasTarget};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    intrinsics::{definitions::Intrinsic as TirIntrinsic, utils::try_use_term_as_integer_lit},
    tir::{CallTerm, DataTy, FnDefId, LitPat, PatId, Term, TermId, TyId},
};

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
    Call,

    /// A cast intrinsic operation, we perform a cast from the type of the
    /// first term into the desired second [ReprTyId].
    Cast(TermId, ReprTyId),

    /// A "boolean" binary operation which takes two terms and yields a boolean
    /// term as a result.
    BinaryOp(BinOp, TermId, TermId),

    /// A short-circuiting boolean binary operation, the term should be lowered
    /// into the equivalent of `a && b` or `a || b`.
    LogicalBinOp(LogicalBinOp, TermId, TermId),

    /// An "unary" operation, the term should be lowered into the equivalent
    /// unary operation.
    UnaryOp(UnOp, TermId),
}

impl BodyBuilder<'_> {
    /// Get the [ReprTyId] from a given [TermId]. This function will internally
    /// cache results of lowering a [TermId] into an [ReprTyId] to avoid
    /// duplicate work.
    pub(crate) fn ty_id_from_tir_term(&self, term: TermId) -> ReprTyId {
        let ty = self.ctx.get_inferred_ty(term);
        self.ctx.repr_ty_from_tir_ty(ty)
    }

    /// Get the [ReprTyId] from a given [TyId]. This function will internally
    /// cache results of lowering a [TyId] into an [ReprTyId] to avoid
    /// duplicate work.
    pub(super) fn ty_id_from_tir_ty(&self, ty: TyId) -> ReprTyId {
        self.ctx.repr_ty_from_tir_ty(ty)
    }

    /// Get the [ReprTyId] for a give [PatId].
    pub(super) fn ty_id_from_tir_pat(&self, pat: PatId) -> ReprTyId {
        let ty = self.ctx.get_inferred_ty(pat);
        self.ty_id_from_tir_ty(ty)
    }

    /// Create an ADT from a defined [DataTy].
    pub(crate) fn ty_id_from_tir_data(&self, data_ty: DataTy) -> ReprTyId {
        self.ctx.repr_ty_from_tir_data_ty(data_ty)
    }

    /// Create an function type from the given [TirIntrinsic].
    pub(super) fn ty_id_from_tir_intrinsic(
        &mut self,
        intrinsic: TirIntrinsic,
        originating_node: AstNodeId,
    ) -> ReprTyId {
        self.ctx.repr_ty_from_tir_intrinsic(intrinsic, originating_node)
    }

    /// Create an function type from the given [FnDefId].
    pub(super) fn ty_id_from_tir_fn_def(&mut self, fn_def: FnDefId) -> ReprTyId {
        self.ctx.repr_ty_from_tir_fn_def(fn_def)
    }

    /// Function which is used to classify a [FnCallTerm] into a
    /// [FnCallTermKind].
    pub(crate) fn classify_fn_call_term(&self, term: &CallTerm) -> FnCallTermKind {
        let CallTerm { subject, args, .. } = term;

        match *subject.value() {
            Term::Intrinsic(intrinsic) => {
                match intrinsic {
                    // Handle these intrinsics specially:
                    TirIntrinsic::Cast => {
                        let (to_ty, value) = (
                            args.at(1).unwrap().borrow().value,
                            args.at(2).unwrap().borrow().value,
                        );

                        // Convert the `to_ty` into an IR type and
                        let ty = self.ty_id_from_tir_ty(to_ty);

                        FnCallTermKind::Cast(value, ty)
                    }
                    TirIntrinsic::CondBinOp => {
                        let (op, lhs, rhs) = (
                            args.at(1).unwrap().borrow().value,
                            args.at(2).unwrap().borrow().value,
                            args.at(3).unwrap().borrow().value,
                        );

                        let op = BinOp::try_from(
                            try_use_term_as_integer_lit::<_, u8>(&self.ctx, op).unwrap(),
                        )
                        .unwrap();
                        FnCallTermKind::BinaryOp(op, lhs, rhs)
                    }
                    TirIntrinsic::ShortCircuitingBoolOp => {
                        let (op, lhs, rhs) = (
                            args.at(1).unwrap().borrow().value,
                            args.at(2).unwrap().borrow().value,
                            args.at(3).unwrap().borrow().value,
                        );

                        let op = LogicalBinOp::try_from(
                            try_use_term_as_integer_lit::<_, u8>(&self.ctx, op).unwrap(),
                        )
                        .unwrap();

                        FnCallTermKind::LogicalBinOp(op, lhs, rhs)
                    }
                    TirIntrinsic::BinOp => {
                        let (op, lhs, rhs) = (
                            args.at(1).unwrap().borrow().value,
                            args.at(2).unwrap().borrow().value,
                            args.at(3).unwrap().borrow().value,
                        );

                        let op = BinOp::try_from(
                            try_use_term_as_integer_lit::<_, u8>(&self.ctx, op).unwrap(),
                        )
                        .unwrap();
                        FnCallTermKind::BinaryOp(op, lhs, rhs)
                    }
                    TirIntrinsic::UnOp => {
                        let (op, subject) = (
                            args.at(1).unwrap().borrow().value,
                            args.at(2).unwrap().borrow().value,
                        );

                        // Parse the operator from the starting term.
                        let parsed_op = UnOp::try_from(
                            try_use_term_as_integer_lit::<_, u8>(&self.ctx, op).unwrap(),
                        )
                        .unwrap();

                        FnCallTermKind::UnaryOp(parsed_op, subject)
                    }
                    TirIntrinsic::SizeOf
                    | TirIntrinsic::AlignOf
                    | TirIntrinsic::PtrOffset
                    | TirIntrinsic::Transmute
                    | TirIntrinsic::Memcmp
                    | TirIntrinsic::Memcpy
                    | TirIntrinsic::Abort
                    | TirIntrinsic::Panic => FnCallTermKind::Call,
                    TirIntrinsic::Eval | TirIntrinsic::UserError | TirIntrinsic::DebugPrint => {
                        panic!("Found unexpected intrinsic {} which should have been evaluated during TC", intrinsic)
                    }
                }
            }
            _ => FnCallTermKind::Call,
        }
    }

    /// Get a [BodyInfo] from the current [BodyBuilder] state.
    pub fn body_info(&self) -> BodyInfo<'_> {
        BodyInfo { locals: &self.locals, projections: &self.projections }
    }

    /// Convert the [LitPat] into a [Const] and return the value of the constant
    /// as a [u128]. This literal term must be an integral type.
    #[inline]
    pub(crate) fn eval_lit_pat(&self, pat: LitPat) -> Const {
        self.lit_as_const(pat.0)
    }

    /// This will compute the value of a range literal as a [Const] and a
    /// [u128]. The [u128] is essentially an encoded version in order to
    /// store signed and unsigned values within the same value.
    ///
    /// This function accounts for the fact that a range literal may not have
    /// a `lo` or `hi` value. In this case, this function will autofill the
    /// range to either have a `lo` or `hi` value depending on the type of
    /// the range. In the case of a missing `lo`, it is then assumed that
    /// the value is `ty::MIN` and in the case of a missing `hi`, it is
    /// assumed that the value is `ty::MAX`.
    pub(crate) fn eval_range_lit(
        &self,
        maybe_pat: Option<LitPat>,
        ty_id: ReprTyId,
        at_end: bool,
    ) -> (Const, u128) {
        let scalar = match maybe_pat {
            Some(lit_pat) => {
                let constant = self.eval_lit_pat(lit_pat);
                let ConstKind::Scalar(scalar) = constant.kind else {
                    panic!("expected scalar constant in `add_cases_to_switch`")
                };

                return (constant, scalar.to_bits(scalar.size()).unwrap());
            }
            None => ty_id.map(|ty| match ty {
                ReprTy::Char if at_end => Scalar::from(std::char::MAX),
                ReprTy::Char => {
                    Scalar::from_uint(0u32, Size::from_bytes(std::mem::size_of::<char>() as u64))
                }
                ReprTy::Int(int_ty) => {
                    let ptr_size = self.ctx.target().ptr_size();
                    let size = int_ty.size(ptr_size);
                    let value = if at_end { size.signed_int_max() } else { size.signed_int_min() };
                    Scalar::from_int(value, size)
                }
                ReprTy::UInt(ty) => {
                    let ptr_size = self.ctx.target().ptr_size();
                    let size = ty.size(ptr_size);

                    let value = if at_end { size.unsigned_int_max() } else { 0 };
                    Scalar::from_uint(value, ptr_size)
                }
                _ => unreachable!(),
            }),
        };

        // Evaluate the bits of the scalar into a u128
        let bits = scalar.to_bits(scalar.size()).unwrap();
        (Const::new(ty_id, ConstKind::Scalar(scalar)), bits)
    }
}
