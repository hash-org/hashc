//! Module that contains logic for handling and creating [RValue]s from
//! [ast::Expr]s.

use hash_ast::ast;
use hash_ir::{
    ir::{AssertKind, BasicBlock, BinOp, Const, ConstKind, Operand, RValue, UnevaluatedConst},
    ty::{IrTy, Mutability},
};
use hash_source::{
    constant::{IntConstant, IntTy, CONSTANT_MAP},
    location::Span,
};
use hash_tir::old::scope::ScopeKind;
use hash_utils::store::Store;

use super::{category::Category, unpack, BlockAnd, BlockAndExtend, Builder};

impl<'tcx> Builder<'tcx> {
    /// Construct an [RValue] from the given [ast::Expr].
    pub(crate) fn as_rvalue(
        &mut self,
        mut block: BasicBlock,
        expr: ast::AstNodeRef<'tcx, ast::Expr>,
    ) -> BlockAnd<RValue> {
        match expr.body {
            ast::Expr::Lit(lit) => {
                let value = self.as_constant(lit.data.ast_ref()).into();
                block.and(value)
            }

            // @@SpecialCase: if this is a variable, and it is not in scope,
            // then we essentially assume that it is a zero-sized constant type.
            ast::Expr::Variable(variable) if self.lookup_local(variable.name.ident).is_none() => {
                let ty = self.ty_id_of_node(expr.id());
                let value = Const::Zero(ty).into();

                block.and(value)
            }

            ast::Expr::UnaryExpr(ast::UnaryExpr { operator, expr }) => {
                // If the unary operator is a typeof, we should have already dealt with
                // this...
                if matches!(operator.body(), ast::UnOp::TypeOf) {
                    panic!("`typeof` should have been handled already");
                }

                let arg =
                    unpack!(block = self.as_operand(block, expr.ast_ref(), Mutability::Mutable));

                // If the operator is a negation, and the operand is signed, we can have a
                // case of overflow. This occurs when the operand is the minimum value for
                // the type, and a negation occurs. This causes the value to overflow. We
                // check for this case here, and emit an assertion check for this (assuming
                // checked operations are enabled).
                let ty = self.ty_of_node(expr.id());

                if self.settings.lowering_settings().checked_operations
                    && matches!(operator.body(), ast::UnOp::Neg)
                    && ty.is_signed()
                {
                    let min_value = self.min_value_of_ty(ty);
                    let is_min = self.temp_place(self.ctx.tys().common_tys.bool);

                    self.control_flow_graph.push_assign(
                        block,
                        is_min,
                        RValue::BinaryOp(BinOp::Eq, Box::new((arg, min_value))),
                        expr.span(),
                    );

                    block = self.assert(
                        block,
                        is_min.into(),
                        false,
                        AssertKind::NegativeOverflow { operand: arg },
                        expr.span(),
                    );
                }

                block.and(RValue::UnaryOp((*operator.body()).into(), arg))
            }
            ast::Expr::BinaryExpr(ast::BinaryExpr { lhs, rhs, operator }) => {
                let lhs =
                    unpack!(block = self.as_operand(block, lhs.ast_ref(), Mutability::Mutable));
                let rhs =
                    unpack!(block = self.as_operand(block, rhs.ast_ref(), Mutability::Mutable));

                return self.build_binary_op(
                    block,
                    self.ty_of_node(expr.id()),
                    expr.span,
                    (*operator.body()).into(),
                    lhs,
                    rhs,
                );
            }
            ast::Expr::Variable(_)
            | ast::Expr::ConstructorCall(_)
            | ast::Expr::Directive(_)
            | ast::Expr::Declaration(_)
            | ast::Expr::Access(_)
            | ast::Expr::Ref(_)
            | ast::Expr::Deref(_)
            | ast::Expr::Unsafe(_)
            | ast::Expr::Cast(_)
            | ast::Expr::Block(_)
            | ast::Expr::Import(_)
            | ast::Expr::StructDef(_)
            | ast::Expr::EnumDef(_)
            | ast::Expr::TyFnDef(_)
            | ast::Expr::TraitDef(_)
            | ast::Expr::ImplDef(_)
            | ast::Expr::ModDef(_)
            | ast::Expr::FnDef(_)
            | ast::Expr::Ty(_)
            | ast::Expr::Return(_)
            | ast::Expr::Break(_)
            | ast::Expr::Continue(_)
            | ast::Expr::Index(_)
            | ast::Expr::Assign(_)
            | ast::Expr::AssignOp(_)
            | ast::Expr::MergeDeclaration(_)
            | ast::Expr::TraitImpl(_) => {
                // Verify that this is an actual RValue...
                debug_assert!(!matches!(Category::of(expr), Category::RValue | Category::Constant));

                let operand = unpack!(block = self.as_operand(block, expr, Mutability::Mutable));
                block.and(RValue::Use(operand))
            }
        }
    }

    /// Compute the minimum value of an [IrTy] assuming that it is a
    /// signed integer type.
    fn min_value_of_ty(&self, ty: IrTy) -> Operand {
        let value = if let IrTy::Int(signed_ty) = ty {
            let size = signed_ty.size(self.tcx.pointer_width).unwrap().bits();
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
        expr: ast::AstNodeRef<'tcx, ast::Expr>,
        mutability: Mutability,
    ) -> BlockAnd<Operand> {
        // We want to deal with variables in a special way since they might
        // be referencing values that are outside of the the body, i.e. un-evaluated
        // constants. In this case, we want to just create a constant value that is
        // yet to be evaluated.
        //
        // @@Future: would be nice to remove this particular check and somehow deal with
        // these differently, possibly some kind of additional syntax or a flag to
        // denote when some variable refers to a constant value.
        if let ast::Expr::Variable(variable) = expr.body {
            let name = variable.name.ident;

            let ty_id = self.ty_id_of_node(expr.id());

            // If this is a function type, we emit a ZST to represent the operand
            // of the function.
            if self.ctx.map_ty(ty_id, |ty| matches!(ty, IrTy::FnDef { .. })) {
                return block.and(Operand::Const(Const::Zero(ty_id).into()));
            }

            if let Some((scope, _, kind)) = self.lookup_item_scope(name) && kind != ScopeKind::Variable {
                let unevaluated_const = UnevaluatedConst { scope, name };

                // record that this constant is used in this function
                self.needed_constants.push(unevaluated_const);

                return block.and(ConstKind::Unevaluated(unevaluated_const).into());
            }
        }

        match Category::of(expr) {
            // Just directly recurse and create the constant.
            Category::Constant => block.and(self.lower_constant_expr(expr).into()),
            Category::Place | Category::RValue => {
                let place = unpack!(block = self.as_place(block, expr, mutability));
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
