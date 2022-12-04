use hash_ast::ast::{self, AstNodeRef, BinaryExpr, Expr, UnaryExpr};
use hash_ir::{
    ir::{AssertKind, BasicBlock, BinOp, Const, RValue, RValueId},
    ty::{IrTy, Mutability},
};
use hash_source::location::Span;
use hash_utils::store::Store;

use super::{category::Category, unpack, BlockAnd, BlockAndExtend, Builder};

impl<'tcx> Builder<'tcx> {
    /// Construct an [RValue] from the given [Expr] and return the [RValueId].
    pub(crate) fn as_rvalue(
        &mut self,
        mut block: BasicBlock,
        expr: AstNodeRef<'tcx, Expr>,
    ) -> BlockAnd<RValueId> {
        // @@Todo: use a notion of `categories` to determine if we should
        // lower it as a constant or else, the `category` is derived from
        // the expression itself,
        let rvalue = match expr.body {
            Expr::Lit(lit) => self.as_constant(lit.data.ast_ref()).into(),

            // @@SpecialCase: if this is a variable, and it is not in scope,
            // then we essentially assume that it is a zero-sized constant type.
            Expr::Variable(variable) if self.lookup_local(variable.name.ident).is_none() => {
                let ty = self.ty_id_of_node(expr.id());
                Const::Zero(ty).into()
            }

            Expr::UnaryExpr(UnaryExpr { operator, expr }) => {
                // If the unary operator is a typeof, we should have already dealt with
                // this...
                if matches!(operator.body(), ast::UnOp::TypeOf) {
                    panic!("`typeof` should have been handled already");
                }

                let arg =
                    unpack!(block = self.as_operand(block, expr.ast_ref(), Mutability::Mutable));

                // @@Todo: depending on what mode we're running in (which should be derived from
                // the compiler session, we         should emit a check here
                // determining if the operation might cause an overflow, or an underflow).
                RValue::UnaryOp((*operator.body()).into(), arg)
            }
            Expr::BinaryExpr(BinaryExpr { lhs, rhs, operator }) => {
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
            Expr::Variable(_)
            | Expr::ConstructorCall(_)
            | Expr::Directive(_)
            | Expr::Declaration(_)
            | Expr::Access(_)
            | Expr::Ref(_)
            | Expr::Deref(_)
            | Expr::Unsafe(_)
            | Expr::Cast(_)
            | Expr::Block(_)
            | Expr::Import(_)
            | Expr::StructDef(_)
            | Expr::EnumDef(_)
            | Expr::TyFnDef(_)
            | Expr::TraitDef(_)
            | Expr::FnDef(_)
            | Expr::Ty(_)
            | Expr::Return(_)
            | Expr::Break(_)
            | Expr::Continue(_)
            | Expr::Index(_)
            | Expr::Assign(_)
            | Expr::AssignOp(_)
            | Expr::MergeDeclaration(_)
            | Expr::TraitImpl(_) => {
                // Verify that this is an actual RValue...
                debug_assert!(!matches!(Category::of(expr), Category::RValue | Category::Constant));

                let operand = unpack!(block = self.as_operand(block, expr, Mutability::Mutable));
                return block.and(operand);
            }
        };

        let rvalue_id = self.storage.rvalue_store().create(rvalue);
        block.and(rvalue_id)
    }

    /// Convert the given expression into an [RValue] operand which means that
    /// this is either a constant or a local variable. In the case of a
    /// constant, this means that the value is [RValue::Const], and in the
    /// case of a local variable, this means that the value is
    /// [RValue::Use].
    pub(crate) fn as_operand(
        &mut self,
        mut block: BasicBlock,
        expr: AstNodeRef<'tcx, Expr>,
        mutability: Mutability,
    ) -> BlockAnd<RValueId> {
        match Category::of(expr) {
            // Just directly recurse and create the constant.
            Category::Constant => self.as_rvalue(block, expr),
            Category::Place | Category::RValue => {
                let place = unpack!(block = self.as_place(block, expr, mutability));

                let rvalue = RValue::Use(place);
                let rvalue_id = self.storage.rvalue_store().create(rvalue);

                block.and(rvalue_id)
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
        lhs: RValueId,
        rhs: RValueId,
    ) -> BlockAnd<RValueId> {
        let is_lhs_const =
            self.storage.rvalue_store().map_fast(lhs, |value| value.is_integral_const());
        let is_rhs_const =
            self.storage.rvalue_store().map_fast(rhs, |value| value.is_integral_const());

        // If both values are constant, see if we can perform a constant fold...
        if is_lhs_const && is_rhs_const {
            let lhs = self.storage.rvalue_store().map_fast(lhs, |value| value.as_const());
            let rhs = self.storage.rvalue_store().map_fast(rhs, |value| value.as_const());

            if let Some(folded) = self.try_fold_const_op(op, lhs, rhs) {
                return block.and(self.storage.rvalue_store().create(folded.into()));
            }
        }

        // If we need have been instructed to insert overflow checks, and the
        // operator is checkable, then use `CheckedBinaryOp` instead of `BinaryOp`.
        if self.settings.checked_operations && op.is_checkable() && ty.is_integral() {
            // Create a new tuple that contains the result of the operation
            let expr_ty = self.storage.ty_store().create(ty);
            let ty = IrTy::tuple(self.storage, &[expr_ty, self.storage.ty_store().make_bool()]);
            let ty_id = self.storage.ty_store().create(ty);

            let temp = self.temp_place(ty_id);
            let rvalue_id =
                self.storage.rvalue_store().create(RValue::CheckedBinaryOp(op, lhs, rhs));

            let result = temp.field(0);
            let overflow = temp.field(1);

            // Push an assignment to the tuple on the operation
            self.control_flow_graph.push_assign(block, temp, rvalue_id, span);

            block = self.assert(block, overflow, false, AssertKind::Overflow, span);

            let value = self.storage.rvalue_store().create(RValue::Use(result));
            block.and(value)
        } else {
            let binary_op = RValue::BinaryOp(op, lhs, rhs);
            let rvalue_id = self.storage.rvalue_store().create(binary_op);
            block.and(rvalue_id)
        }
    }
}
