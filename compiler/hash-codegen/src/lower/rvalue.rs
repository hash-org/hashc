//! Module that deals with lowering [ir::RValue]s into
//! backend specific RValues.

use hash_ir::ir;

use super::FnBuilder;
use crate::traits::{ctx::HasCtxMethods, layout::LayoutMethods, CodeGen};

impl<'b, 'ir, Builder: CodeGen<'b>> FnBuilder<'b, 'ir, Builder> {
    /// Check whether the given [RValue] will create an
    /// operand or not.
    pub fn rvalue_creates_operand(&self, rvalue: &ir::RValue) -> bool {
        match *rvalue {
            ir::RValue::Use(_)
            | ir::RValue::ConstOp(_, _)
            | ir::RValue::UnaryOp(_, _)
            | ir::RValue::BinaryOp(_, _)
            | ir::RValue::CheckedBinaryOp(_, _)
            | ir::RValue::Len(_)
            | ir::RValue::Ref(_, _, _)
            | ir::RValue::Discriminant(_) => true,
            ir::RValue::Aggregate(_, _) => {
                let ty = rvalue.ty(self.ctx.body_data());

                // check if the type is a ZST, and if so this satisfies the
                // case that the rvalue creates an operand...
                self.ctx.layout_of(ty).is_zst(self.ctx.layouts())
            }
        }
    }
}
