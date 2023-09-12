//! Implementation of the `StaticMethods` trait for the `CodeGenCtx` struct in
//! the LLVM backend.

use hash_codegen::{
    target::alignment::Alignment,
    traits::{statics::StaticMethods, ty::TypeBuilderMethods},
};
use inkwell::values::{AnyValue, AnyValueEnum, BasicValueEnum, GlobalValue, UnnamedAddress};

use crate::ctx::CodeGenCtx;

impl<'b, 'm> CodeGenCtx<'b, 'm> {
    // Define a global static variable within the current [LLVMModule]. This
    // function is only invoked if the static variable has not already been
    // defined.
    fn define_static_item(&self, cv: AnyValueEnum<'m>, align: Alignment) -> GlobalValue<'m> {
        let sym = self.generate_local_symbol_name("");
        let def = self.define_private_global(self.ty_of_value(cv), sym.as_str());

        // We set the initialiser as the `cv`
        let value: BasicValueEnum = cv.try_into().unwrap();
        def.set_initializer(&value);
        self.set_alignmnent_on_global(def, align);
        def.set_unnamed_address(UnnamedAddress::Global);
        def
    }

    /// Set the alignment on a global variable.
    fn set_alignmnent_on_global(&self, value: GlobalValue<'m>, align: Alignment) {
        // @@FixMe: https://github.com/rust-lang/rust/issues/44411 - respect targets
        // which require for a minimum alignment to be specified on globals.

        let align = align.bytes() as u32;
        value.set_alignment(align);
    }
}

impl<'b, 'm> StaticMethods for CodeGenCtx<'b, 'm> {
    fn static_addr_of(&self, cv: Self::Value, align: Alignment) -> Self::Value {
        // Check if we've already created the global
        if let Some(global) = self.global_consts.borrow().get(&cv) {
            // Check if might need to upgrade alignment based on the use case.
            let alignment = align.bytes() as u32;
            if alignment > global.get_alignment() {
                // Upgrade the alignment of the global.
                global.set_alignment(alignment);
            }

            return global.as_any_value_enum();
        }

        // Otherwise we have to create it.
        let gv = self.define_static_item(cv, align);
        gv.set_constant(true);

        self.global_consts.borrow_mut().insert(cv, gv);
        gv.as_any_value_enum()
    }
}
