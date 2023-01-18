//! Module that contains logic for handling and creating [RValue]s from
//! [ast::Expr]s.

use hash_ast::ast;
use hash_ir::{
    ir::{AssertKind, BasicBlock, BinOp, Const, ConstKind, Operand, RValue, UnevaluatedConst},
    ty::{IrTy, Mutability},
};
use hash_source::location::Span;
use hash_types::scope::ScopeKind;
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

                // @@Todo: depending on what mode we're running in (which should be derived from
                // the compiler session, we should emit a check here
                // determining if the operation might cause an overflow, or an underflow).
                let value = RValue::UnaryOp((*operator.body()).into(), arg);
                block.and(value)
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
        if self.settings.lowering_settings().checked_operations
            && op.is_checkable()
            && ty.is_integral()
        {
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

            block.and(result.into())
        } else {
            let binary_op = RValue::BinaryOp(op, operands);
            block.and(binary_op)
        }
    }
}
