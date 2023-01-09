//! Module that deals with lowering [ir::RValue]s into
//! backend specific RValues.

use hash_ir::ir;

use super::{operands::OperandRef, place::PlaceRef, FnBuilder};
use crate::traits::{builder::BlockBuilderMethods, ctx::HasCtxMethods, layout::LayoutMethods};

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {
    /// Emit code for the given [ir::RValue] and store the result in the
    /// given [PlaceRef].
    pub fn codegen_rvalue(
        &mut self,
        builder: &mut Builder,
        destination: PlaceRef<Builder::Value>,
        rvalue: &ir::RValue,
    ) {
        // @@Todo: introduce casting, and deal with the code generation
        match *rvalue {
            // specifics here.
            ir::RValue::Use(_) => todo!(),
            ir::RValue::Aggregate(_, _) => todo!(),
            _ => {
                let temp = self.codegen_rvalue_operand(builder, rvalue);
                temp.value.store(builder, destination);
            }
        }
    }

    /// Emit code for a [ir::RValue] that will return an [OperandRef].
    pub fn codegen_rvalue_operand(
        &mut self,
        _builder: &mut Builder,
        rvalue: &ir::RValue,
    ) -> OperandRef<Builder::Value> {
        match *rvalue {
            ir::RValue::Use(_) => todo!(),
            ir::RValue::Aggregate(_, _) => todo!(),
            ir::RValue::ConstOp(_, _) => todo!(),
            ir::RValue::UnaryOp(_, _) => todo!(),
            ir::RValue::BinaryOp(_, _) => todo!(),
            ir::RValue::CheckedBinaryOp(_, _) => todo!(),
            ir::RValue::Len(_) => todo!(),
            ir::RValue::Ref(_, _, _) => todo!(),
            ir::RValue::Discriminant(_) => todo!(),
        }
    }

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
                let ty = rvalue.ty(self.ctx.ir_ctx());

                // check if the type is a ZST, and if so this satisfies the
                // case that the rvalue creates an operand...
                self.ctx.layout_of(ty).is_zst(self.ctx.layouts())
            }
        }
    }
}
