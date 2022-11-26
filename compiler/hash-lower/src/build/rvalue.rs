use hash_ast::ast::{self, AstNodeRef, Expr, UnaryExpr};
use hash_ir::ir::{BasicBlock, RValue, RValueId};
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
            Expr::UnaryExpr(UnaryExpr { operator, expr }) => {
                // If the unary operator is a typeof, we should have already dealt with
                // this...
                if matches!(operator.body(), ast::UnOp::TypeOf) {
                    panic!("`typeof` should have been handled already");
                }

                let arg = unpack!(block = self.as_operand(block, expr.ast_ref()));

                // @@Todo: depending on what mode we're running in (which should be derived from
                // the compiler session, we         should emit a check here
                // determining if the operation might cause an overflow, or an underflow).
                RValue::UnaryOp((*(operator.body())).into(), arg)
            }
            Expr::BinaryExpr(..) => todo!(),
            Expr::Index(..) => todo!(),
            _ => unimplemented!(),
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
    ) -> BlockAnd<RValueId> {
        let category = Category::of(expr);

        match category {
            // Just directly recurse and create the constant.
            Category::Constant => self.as_rvalue(block, expr),
            Category::Place | Category::Rvalue => {
                let place = unpack!(block = self.as_place(block, expr));

                let rvalue = RValue::Use(place);
                let rvalue_id = self.storage.rvalue_store().create(rvalue);

                block.and(rvalue_id)
            }
        }
    }
}
