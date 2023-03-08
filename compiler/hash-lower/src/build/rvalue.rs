//! Module that contains logic for handling and creating [RValue]s from
//! [Term]s.

use hash_ir::{
    cast::CastKind,
    ir::{AssertKind, BasicBlock, BinOp, Const, ConstKind, Operand, RValue, UnaryOp},
    ty::{IrTy, Mutability},
};
use hash_source::{
    constant::{IntConstant, IntTy, CONSTANT_MAP},
    location::Span,
};
use hash_tir::{
    environment::env::AccessToEnv,
    terms::{Term, TermId},
};
use hash_utils::store::{CloneStore, Store};

use super::{category::Category, ty::FnCallTermKind, unpack, BlockAnd, BlockAndExtend, Builder};

impl<'tcx> Builder<'tcx> {
    /// Construct an [RValue] from the given [ast::Expr].
    pub(crate) fn as_rvalue(&mut self, mut block: BasicBlock, term_id: TermId) -> BlockAnd<RValue> {
        // @@Temporary: replace with get_ref();
        let term = self.stores().term().get(term_id);
        let span = self.span_of_term(term_id);

        let mut as_operand = |this: &mut Self| {
            // Verify that this is an actual RValue...
            debug_assert!(!matches!(Category::of(&term), Category::RValue | Category::Constant));

            let operand = unpack!(block = this.as_operand(block, term_id, Mutability::Mutable));
            block.and(RValue::Use(operand))
        };

        match term {
            Term::Lit(lit) => {
                let value = self.as_constant(&lit).into();
                block.and(value)
            }
            Term::FnCall(fn_call) => {
                match self.classify_fn_call_term(&fn_call) {
                    FnCallTermKind::BinaryOp(op, lhs, rhs) => {
                        let lhs = unpack!(block = self.as_operand(block, lhs, Mutability::Mutable));
                        let rhs = unpack!(block = self.as_operand(block, rhs, Mutability::Mutable));

                        // @@Future: we shouldn't use the un-cached version here, however since this
                        // only for primitive types (at the moment), this is fine.
                        let ty = self.ty_from_tir_term(term_id);
                        self.build_binary_op(block, ty, span, op, lhs, rhs)
                    }
                    FnCallTermKind::UnaryOp(op, subject) => {
                        let arg =
                            unpack!(block = self.as_operand(block, subject, Mutability::Mutable));

                        // @@Future: we shouldn't use the un-cached version here, however since this
                        // only for primitive types (at the moment), this is fine.
                        let ty = self.ty_from_tir_term(term_id);

                        // If the operator is a negation, and the operand is signed, we can have a
                        // case of overflow. This occurs when the operand is the minimum value for
                        // the type, and a negation occurs. This causes the value to overflow. We
                        // check for this case here, and emit an assertion check for this (assuming
                        // checked operations are enabled).
                        if self.settings.lowering_settings().checked_operations
                            && matches!(op, UnaryOp::Neg)
                            && ty.is_signed()
                        {
                            let min_value = self.min_value_of_ty(ty);
                            let is_min = self.temp_place(self.ctx.tys().common_tys.bool);

                            self.control_flow_graph.push_assign(
                                block,
                                is_min,
                                RValue::BinaryOp(BinOp::Eq, Box::new((arg, min_value))),
                                span,
                            );

                            block = self.assert(
                                block,
                                is_min.into(),
                                false,
                                AssertKind::NegativeOverflow { operand: arg },
                                span,
                            );
                        }

                        block.and(RValue::UnaryOp(op, arg))
                    }
                    // A casting operation between the given term into a type.
                    FnCallTermKind::Cast(term, ty) => {
                        // @@Future: there should be some way to convert an enum
                        // value that is naked
                        // i.e. equivalent of a c-enum:
                        // ```
                        // Direction := enum {
                        //     Up,
                        //     Down,
                        //     Left,
                        //     Right,
                        // }
                        // ```
                        // Should be convertible into the discriminant value of
                        // the enum so that it
                        // can be used for external FFI calls.
                        let source_ty = self.ty_id_from_tir_term(term);
                        let source =
                            unpack!(block = self.as_operand(block, term, Mutability::Mutable));

                        let cast_kind = CastKind::classify(self.ctx, source_ty, ty);
                        block.and(RValue::Cast(cast_kind, source, ty))
                    }
                    _ => as_operand(self),
                }
            }

            Term::Array(_)
            | Term::Tuple(_)
            | Term::Ctor(_)
            | Term::FnRef(_)
            | Term::Block(_)
            | Term::Var(_)
            | Term::Loop(_)
            | Term::LoopControl(_)
            | Term::Match(_)
            | Term::Return(_)
            | Term::Decl(_)
            | Term::Assign(_)
            | Term::Unsafe(_)
            | Term::Access(_)
            | Term::Index(_)
            | Term::Cast(_)
            | Term::TypeOf(_)
            | Term::Ty(_)
            | Term::Ref(_)
            | Term::Deref(_)
            | Term::Hole(_) => as_operand(self),
        }
    }

    /// Compute the minimum value of an [IrTy] assuming that it is a
    /// signed integer type.
    fn min_value_of_ty(&self, ty: IrTy) -> Operand {
        let value = if let IrTy::Int(signed_ty) = ty {
            let ptr_width = self.settings.target().pointer_bit_width / 8;
            let size = signed_ty.size(ptr_width).unwrap().bits();
            let n = 1 << (size - 1);

            // Create and intern the constant
            let const_int = CONSTANT_MAP.create_int_constant(IntConstant::from_sint(n, signed_ty));
            Const::Int(const_int).into()
        } else {
            unreachable!()
        };

        Operand::Const(value)
    }

    /// Convert the given expression into an [RValue] operand which means that
    /// this is either a constant or a local variable. In the case of a
    /// constant, this means that the value is [`RValue::Use(..)`], and in the
    /// case of a local variable, this means that the value is
    /// [RValue::Use].
    pub(crate) fn as_operand(
        &mut self,
        mut block: BasicBlock,
        term_id: TermId,
        mutability: Mutability,
    ) -> BlockAnd<Operand> {
        let term = self.stores().term().get(term_id);
        let span = self.span_of_term(term_id);

        // If the item is a reference to a function, i.e. the subject of a call, then
        // we emit a constant that refers to the function.
        if let Term::FnRef(def_id) = term {
            let ty_id = self.ty_id_from_tir_fn_def(def_id);

            // If this is a function type, we emit a ZST to represent the operand
            // of the function.
            if self.ctx.map_ty(ty_id, |ty| matches!(ty, IrTy::FnDef { .. })) {
                return block.and(Operand::Const(Const::Zero(ty_id).into()));
            }
        }

        match Category::of(&term) {
            // Just directly recurse and create the constant.
            Category::Constant => block.and(self.lower_constant_expr(&term, span).into()),
            Category::Place | Category::RValue => {
                let place = unpack!(block = self.as_place(block, term_id, mutability));
                block.and(place.into())
            }
        }
    }

    /// Create a binary operation from two operands and a provided [BinOp]. This
    /// function is needed to handle some additional cases where we might
    /// eagerly evaluate the operands and just produce a new constant. For
    /// example, if we have `1 + 2`, we can just produce a constant `3`
    /// instead of creating a binary operation. Additionally, we also
    /// introduce "checks" for various kinds of operators to ensure that
    /// undefined behaviour causes a runtime crash (depending on if the
    /// compiler session specified to do this).
    pub(crate) fn build_binary_op(
        &mut self,
        mut block: BasicBlock,
        ty: IrTy,
        span: Span,
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
    ) -> BlockAnd<RValue> {
        // try to constant fold the two operands
        if let Operand::Const(ConstKind::Value(lhs_value)) = lhs &&
           let Operand::Const(ConstKind::Value(rhs_value)) = rhs {
            if let Some(folded) = self.try_fold_const_op(op, lhs_value, rhs_value) {
                return block.and(folded.into());
            }
        }

        let operands = Box::new((lhs, rhs));

        // If we need have been instructed to insert overflow checks, and the
        // operator is checkable, then use `CheckedBinaryOp` instead of `BinaryOp`.
        if self.settings.lowering_settings().checked_operations {
            if op.is_checkable() && ty.is_integral() {
                // Create a new tuple that contains the result of the operation
                let expr_ty = self.ctx.tys().create(ty);
                let ty = IrTy::tuple(self.ctx, &[expr_ty, self.ctx.tys().common_tys.bool]);
                let ty_id = self.ctx.tys().create(ty);

                let temp = self.temp_place(ty_id);
                let rvalue = RValue::CheckedBinaryOp(op, operands);

                let result = temp.field(0, self.ctx);
                let overflow = temp.field(1, self.ctx);

                // Push an assignment to the tuple on the operation
                self.control_flow_graph.push_assign(block, temp, rvalue, span);

                block = self.assert(
                    block,
                    Operand::Place(overflow),
                    false,
                    AssertKind::Overflow { op, lhs, rhs },
                    span,
                );

                return block.and(result.into());
            } else if ty.is_integral() && (op == BinOp::Div || op == BinOp::Mod) {
                // Check for division or a remainder by zero, and if so emit
                // an assertion to verify this condition.
                let int_ty: IntTy = ty.into();
                let uint_ty = int_ty.to_unsigned();

                let assert_kind = if op == BinOp::Div {
                    AssertKind::DivisionByZero { operand: lhs }
                } else {
                    AssertKind::RemainderByZero { operand: lhs }
                };

                // Check for division/modulo of zero...
                let is_zero = self.temp_place(self.ctx.tys().common_tys.bool);

                let const_val = Const::Int(
                    CONSTANT_MAP.create_int_constant(IntConstant::from_uint(0, uint_ty)),
                );
                let zero_val = Operand::Const(const_val.into());

                self.control_flow_graph.push_assign(
                    block,
                    is_zero,
                    RValue::BinaryOp(BinOp::Eq, Box::new((rhs, zero_val))),
                    span,
                );

                block = self.assert(block, Operand::Place(is_zero), false, assert_kind, span);

                // In the case of signed integers, if the RHS value is `-1`, and the LHS
                // is the MIN value, this will result in a division overflow, we need to
                // check for this and emit code.
                if ty.is_signed() {
                    let sint_ty = int_ty.to_signed();

                    let const_val = Const::Int(
                        CONSTANT_MAP.create_int_constant(IntConstant::from_sint(-1, sint_ty)),
                    );
                    let negative_one_val = Operand::Const(const_val.into());
                    let minimum_value = self.min_value_of_ty(ty);

                    let is_negative_one = self.temp_place(self.ctx.tys().common_tys.bool);
                    let is_minimum_value = self.temp_place(self.ctx.tys().common_tys.bool);

                    // Push the values that have been created into the temporaries
                    self.control_flow_graph.push_assign(
                        block,
                        is_negative_one,
                        RValue::BinaryOp(BinOp::Eq, Box::new((rhs, negative_one_val))),
                        span,
                    );

                    self.control_flow_graph.push_assign(
                        block,
                        is_minimum_value,
                        RValue::BinaryOp(BinOp::Eq, Box::new((lhs, minimum_value))),
                        span,
                    );

                    // To simplify the generated control flow, we perform a bit_and operation
                    // which checks the condition `(rhs == -1) & (lhs == MIN)`, and then we
                    // emit an assert. Alternatively, this could short_circuit on the first
                    // check, but it would make control flow more complex.
                    let is_overflow = self.temp_place(self.ctx.tys().common_tys.bool);
                    self.control_flow_graph.push_assign(
                        block,
                        is_overflow,
                        RValue::BinaryOp(
                            BinOp::BitAnd,
                            Box::new((is_negative_one.into(), is_minimum_value.into())),
                        ),
                        span,
                    );

                    // Now finally, emit the assert
                    block = self.assert(
                        block,
                        Operand::Place(is_overflow),
                        false,
                        AssertKind::Overflow { op, lhs, rhs },
                        span,
                    );
                }
            }
        }

        block.and(RValue::BinaryOp(op, operands))
    }
}
