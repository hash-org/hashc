//! Module that hosts all of the logic that deals with emitting
//! code and resolving references to intrinsic function calls.

use hash_abi::FnAbi;
use hash_ir::{intrinsics::Intrinsic, ty::IrTy};

use super::{abi::compute_fn_abi_from_instance, FnBuilder};
use crate::traits::{builder::BlockBuilderMethods, ctx::HasCtxMethods, misc::MiscBuilderMethods};

impl<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> FnBuilder<'a, 'b, Builder> {
    /// Resolve a reference to an [Intrinsic].
    pub(super) fn resolve_intrinsic(
        &mut self,
        builder: &mut Builder,
        intrinsic: Intrinsic,
    ) -> (FnAbi, Builder::Function) {
        // @@ErrorHandling: propagate the error into the compiler pipeline, thus
        // terminating the workflow if this error occurs which it shouldn't
        let ty = self.ctx.ir_ctx().intrinsics().get(intrinsic).unwrap();

        // Get function pointer from the specified instance
        let instance = self.ctx.ir_ctx().map_ty(ty, |ty| match ty {
            IrTy::FnDef { instance, .. } => *instance,
            _ => panic!("expected function type when resolving intrinsic item"),
        });

        let abi = compute_fn_abi_from_instance(builder, instance).unwrap();
        (abi, builder.get_fn_ptr(instance))
    }
}
