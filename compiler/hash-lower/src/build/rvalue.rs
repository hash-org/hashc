use hash_ast::ast::{self, AstNodeRef, BinaryExpr, Expr, UnaryExpr};
use hash_ir::{
    ir::{AssertKind, BasicBlock, BinOp, Const, ConstKind, Operand, RValue, RValueId},
    ty::{IrTy, Mutability},
};
use hash_source::location::Span;
use hash_types::scope::ScopeKind;
use hash_utils::store::Store;

use super::{category::Category, unpack, BlockAnd, BlockAndExtend, Builder};

impl<'tcx> Builder<'tcx> {
    /// Construct an [RValue] from the given [Expr] and return the [RValueId].
    pub(crate) fn as_rvalue(
        &mut self,
        mut block: BasicBlock,
        expr: AstNodeRef<'tcx, Expr>,
    ) -> BlockAnd<RValueId> {
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
                // the compiler session, we should emit a check here
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
            | Expr::ImplDef(_)
            | Expr::ModDef(_)
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
                let rvalue = self.storage.rvalues().create(operand.into());

                return block.and(rvalue);
            }
        };

        let rvalue_id = self.storage.rvalues().create(rvalue);
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
    ) -> BlockAnd<Operand> {
        // We want to deal with variables in a special way since they might
        // be referencing values that are outside of the the body, i.e. un-evaluated
        // constants. In this case, we want to just create a constant value that is
        // yet to be evaluated.
        //
        // @@Future: would be nice to remove this particular check and somehow deal with
        // these differently, possibly some kind of additional syntax or a flag to
        // denote when some variable refers to a constant value.
        if let Expr::Variable(variable) = expr.body {
            let name = variable.name.ident;

            if let Some((scope, _, kind)) = self.lookup_item_scope(name) && kind != ScopeKind::Variable {
                return block.and(ConstKind::Unevaluated { scope, name }.into());
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
    ) -> BlockAnd<RValueId> {
        // try to constant fold the two operands
        if let Operand::Const(ConstKind::Value(lhs_value)) = lhs &&
           let Operand::Const(ConstKind::Value(rhs_value)) = rhs {
            if let Some(folded) = self.try_fold_const_op(op, lhs_value, rhs_value) {
                return block.and(self.storage.rvalues().create(folded.into()));
            }
        }

        let operands = Box::new((lhs, rhs));

        // If we need have been instructed to insert overflow checks, and the
        // operator is checkable, then use `CheckedBinaryOp` instead of `BinaryOp`.
        if self.settings.checked_operations && op.is_checkable() && ty.is_integral() {
            // Create a new tuple that contains the result of the operation
            let expr_ty = self.storage.tys().create(ty);
            let ty = IrTy::tuple(self.storage, &[expr_ty, self.storage.tys().make_bool()]);
            let ty_id = self.storage.tys().create(ty);

            let temp = self.temp_place(ty_id);
            let rvalue_id = self.storage.rvalues().create(RValue::CheckedBinaryOp(op, operands));

            let result = temp.field(0, self.storage);
            let overflow = temp.field(1, self.storage);

            // Push an assignment to the tuple on the operation
            self.control_flow_graph.push_assign(block, temp, rvalue_id, span);

            block = self.assert(block, overflow, false, AssertKind::Overflow, span);

            let value = self.storage.rvalues().create(result.into());
            block.and(value)
        } else {
            let binary_op = RValue::BinaryOp(op, operands);
            let rvalue_id = self.storage.rvalues().create(binary_op);
            block.and(rvalue_id)
        }
    }
}
