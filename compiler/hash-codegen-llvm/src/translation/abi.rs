//! This implements all of the ABI specified methods for the [Builder].

use hash_codegen::{
    abi::{ArgAbi, ArgAttributes, CallingConvention, FnAbi, PassMode},
    lower::{operands::OperandValue, place::PlaceRef},
    traits::{
        abi::AbiBuilderMethods, builder::BlockBuilderMethods, debug, layout::LayoutMethods,
        ty::TypeBuilderMethods,
    },
};
use hash_target::abi::{AbiRepresentation, ScalarKind};
use inkwell::{
    attributes::{Attribute, AttributeLoc},
    types::{AnyTypeEnum, BasicTypeEnum},
    values::{AnyValue, AnyValueEnum, CallSiteValue, FunctionValue},
};
use llvm_sys::{LLVMAttributeIndex, LLVMOpaqueAttributeRef};
use smallvec::SmallVec;

use super::{ty::ExtendedTyBuilderMethods, Builder};
use crate::{context::CodeGenCtx, misc::AttributeKind};

impl<'b> AbiBuilderMethods<'b> for Builder<'b> {
    fn get_param(&mut self, index: usize) -> Self::Value {
        let func = self.basic_block().get_parent().unwrap();
        func.get_nth_param(index as u32).unwrap().into()
    }

    fn store_arg(
        &mut self,
        arg_abi: &ArgAbi,
        value: Self::Value,
        destination: PlaceRef<Self::Value>,
    ) {
        arg_abi.store(self, value, destination);
    }

    fn store_fn_arg(
        &mut self,
        arg_abi: &ArgAbi,
        index: &mut usize,
        destination: PlaceRef<Self::Value>,
    ) {
        arg_abi.store_fn_arg(self, index, destination)
    }
}

pub trait ExtendedArgAbiMethods<'b> {
    /// Get the type of the memory location that is backing
    /// the given [ArgAbi].
    fn get_memory_ty(&self, ctx: &CodeGenCtx<'b>) -> AnyTypeEnum<'b>;

    /// Store the given [AnyValueEnum] into the given [PlaceRef].
    fn store(
        &self,
        builder: &mut Builder<'b>,
        value: AnyValueEnum<'b>,
        destination: PlaceRef<AnyValueEnum<'b>>,
    );

    /// Store the given function argument into the given [PlaceRef].
    fn store_fn_arg(
        &self,
        builder: &mut Builder<'b>,
        index: &mut usize,
        destination: PlaceRef<AnyValueEnum<'b>>,
    );
}

impl<'b> ExtendedArgAbiMethods<'b> for ArgAbi {
    fn store(
        &self,
        builder: &mut Builder<'b>,
        value: AnyValueEnum<'b>,
        destination: PlaceRef<AnyValueEnum<'b>>,
    ) {
        // we don't need to do anything if the value is ignored.
        if self.is_ignored() {
            return;
        }

        if self.is_indirect() {
            let alignment = builder.map_layout(self.info.layout, |layout| layout.alignment.abi);

            OperandValue::Ref(value, alignment).store(builder, destination)
        } else {
            OperandValue::Immediate(value).store(builder, destination)
        }
    }

    fn store_fn_arg(
        &self,
        builder: &mut Builder<'b>,
        index: &mut usize,
        destination: PlaceRef<AnyValueEnum<'b>>,
    ) {
        // get the next argument at the index, and increment the
        // index counter for the next argument.
        let mut next_arg = || {
            let value = builder.get_param(*index);
            *index += 1;
            value
        };

        match self.mode {
            PassMode::Ignore => {}
            PassMode::Pair(_, _) => {
                OperandValue::Pair(next_arg(), next_arg()).store(builder, destination)
            }
            PassMode::Direct(_) | PassMode::Indirect { .. } => {
                let arg = next_arg();
                self.store(builder, arg, destination)
            }
        }
    }

    fn get_memory_ty(&self, ctx: &CodeGenCtx<'b>) -> AnyTypeEnum<'b> {
        self.info.llvm_ty(ctx)
    }
}

pub trait ExtendedArgAttributeMethods<'b> {
    /// Get a list of attributes that are currently set on the
    /// [ArhAttributes].
    fn get_attributes(&self) -> SmallVec<[Attribute; 4]>;

    /// Apply the given [ArgAttributes] to the the [FunctionValue]
    /// with the specified [AttributeLoc] which indicates whether
    /// to apply the attributes onto an argument, return value or the
    /// function definition itself.
    fn apply_attributes_to_fn(
        &self,
        ctx: &CodeGenCtx<'b>,
        index: AttributeLoc,
        value: FunctionValue<'b>,
    );

    /// Apply the given [ArgAttributes] to the the [CallSiteValue]
    /// with the specified [AttributeLoc] which indicates whether
    /// to apply the attributes onto an argument, return value or the
    /// function call itself.
    fn apply_attributes_to_call_site(
        &self,
        ctx: &CodeGenCtx<'b>,
        index: AttributeLoc,
        value: CallSiteValue<'b>,
    );
}

impl<'b> ExtendedArgAttributeMethods<'b> for ArgAttributes {
    fn get_attributes(&self) -> SmallVec<[Attribute; 4]> {
        // let mut attributes = SmallVec::new();
        // attributes
        todo!()
    }

    fn apply_attributes_to_fn(
        &self,
        ctx: &CodeGenCtx<'b>,
        index: AttributeLoc,
        value: FunctionValue<'b>,
    ) {
        todo!()
    }

    fn apply_attributes_to_call_site(
        &self,
        ctx: &CodeGenCtx<'b>,
        index: AttributeLoc,
        value: CallSiteValue<'b>,
    ) {
        todo!()
    }
}

pub trait ExtendedFnAbiMethods<'b> {
    /// Produce an LLVM type for the given [FnAbi].
    fn llvm_ty(&self, ctx: &CodeGenCtx<'b>) -> AnyTypeEnum<'b>;

    /// Apply the derived ABI attributes to the given [FunctionValue].
    fn apply_attributes_to_fn(&self, ctx: &CodeGenCtx<'b>, func: FunctionValue<'b>);

    /// Apply the derived ABI attributes to the given [CallSiteValue].
    fn apply_attributes_call_site(&self, builder: &mut Builder<'b>, call_site: CallSiteValue<'b>);
}

impl<'b> ExtendedFnAbiMethods<'b> for FnAbi {
    fn llvm_ty(&self, ctx: &CodeGenCtx<'b>) -> AnyTypeEnum<'b> {
        let arg_count = self.args.len() + if self.ret_abi.mode.is_indirect() { 1 } else { 0 };
        let mut arg_tys = Vec::with_capacity(arg_count);

        let return_ty = match &self.ret_abi.mode {
            PassMode::Ignore => ctx.type_void(),
            PassMode::Direct(_) | PassMode::Pair(_, _) => self.ret_abi.info.immediate_llvm_ty(ctx),
            PassMode::Indirect { attributes, on_stack } => {
                // if the argument is being passed indirectly, then we push th e
                // type through the argument as a pointer.
                arg_tys.push(ctx.type_ptr_to(self.ret_abi.get_memory_ty(ctx)));

                ctx.type_void()
            }
        };

        for arg in self.args.iter() {
            match &arg.mode {
                PassMode::Ignore => continue,
                PassMode::Direct(_) => {
                    arg_tys.push(arg.info.immediate_llvm_ty(ctx));
                }
                PassMode::Pair(_, _) => {
                    arg_tys.push(arg.info.scalar_pair_element_llvm_ty(ctx, 0, true));
                    arg_tys.push(arg.info.scalar_pair_element_llvm_ty(ctx, 1, true));
                }
                PassMode::Indirect { .. } => {
                    // if the argument is being passed indirectly, then we push th e
                    // type through the argument as a pointer.
                    arg_tys.push(ctx.type_ptr_to(arg.get_memory_ty(ctx)));
                }
            }
        }

        ctx.type_function(&arg_tys, return_ty)
    }

    fn apply_attributes_to_fn(&self, ctx: &CodeGenCtx<'b>, func: FunctionValue<'b>) {
        let mut fn_attributes = SmallVec::<[Attribute; 1]>::new();

        // If the return type is un-inhabited then we can mark the
        // function as a "no-return".
        if ctx.map_layout(self.ret_abi.info.layout, |layout| layout.abi.is_uninhabited()) {
            fn_attributes.push(AttributeKind::NoReturn.create_attribute(ctx));
        }

        let mut index = 0;
        let mut apply_attributes_to_arg = |attrs: &ArgAttributes| {
            attrs.apply_attributes_to_fn(ctx, AttributeLoc::Param(index), func);
            index += 1;
            index - 1
        };

        /// Apply all of the attributes onto the return value of the function.
        match &self.ret_abi.mode {
            PassMode::Direct(attrs) => {
                apply_attributes_to_arg(attrs);
            }
            PassMode::Indirect { attributes, on_stack } => {
                debug_assert!(!on_stack); // @@Explain
                let index = apply_attributes_to_arg(attributes);

                // Now we apply the attribute that this return value is a
                // struct return type.
                let attribute = ctx.ll_ctx.create_type_attribute(
                    AttributeKind::StructRet as u32,
                    self.ret_abi.info.llvm_ty(ctx),
                );

                func.add_attribute(AttributeLoc::Return, attribute)
            }
            _ => {}
        }

        // Apply all of the arguments on each attribute to each argument.
        for arg in self.args.iter() {
            match &arg.mode {
                PassMode::Ignore => {}
                PassMode::Pair(a, b) => {
                    apply_attributes_to_arg(a);
                    apply_attributes_to_arg(b);
                }
                PassMode::Direct(attributes)
                | PassMode::Indirect { attributes, on_stack: false } => {
                    apply_attributes_to_arg(attributes);
                }
                PassMode::Indirect { attributes, on_stack: true } => {
                    // If the argument is being passed on the stack, then we
                    // emit the `by_val` attribute on the argument.
                    //
                    // https://llvm.org/docs/LangRef.html#parameter-attributes - "by_val<ty>"
                    let index = apply_attributes_to_arg(attributes);
                    let byval_attribute = ctx
                        .ll_ctx
                        .create_type_attribute(AttributeKind::ByVal as u32, arg.info.llvm_ty(ctx));

                    func.add_attribute(AttributeLoc::Param(index), byval_attribute)
                }
            }
        }
    }

    fn apply_attributes_call_site(&self, builder: &mut Builder<'b>, call_site: CallSiteValue<'b>) {
        let mut fn_attributes = SmallVec::<[Attribute; 1]>::new();

        // If the return type is un-inhabited then we can mark the
        // function as a "no-return".
        if builder.map_layout(self.ret_abi.info.layout, |layout| layout.abi.is_uninhabited()) {
            fn_attributes.push(AttributeKind::NoReturn.create_attribute(builder.ctx));
        }

        apply_attributes_call_site(AttributeLoc::Function, &fn_attributes, call_site);

        let mut index = 0;

        // Used to apply attributes that are stored on ArgAbi, returning the
        // current index at which the value was applied to.
        let mut apply_attributes_to_arg = |ctx: &CodeGenCtx<'b>, attrs: &ArgAttributes| {
            attrs.apply_attributes_to_call_site(ctx, AttributeLoc::Param(index), call_site);
            index += 1;
            index - 1
        };

        /// Apply all of the attributes onto the return value of the function.
        ///
        /// @@CopyPaste: from above function
        match &self.ret_abi.mode {
            PassMode::Direct(attrs) => {
                apply_attributes_to_arg(builder.ctx, attrs);
            }
            PassMode::Indirect { attributes, on_stack } => {
                debug_assert!(!on_stack); // @@Explain
                let index = apply_attributes_to_arg(builder.ctx, attributes);

                // Now we apply the attribute that this return value is a
                // struct return type.
                let attribute = builder.ctx.ll_ctx.create_type_attribute(
                    AttributeKind::StructRet as u32,
                    self.ret_abi.info.llvm_ty(builder.ctx),
                );

                call_site.add_attribute(AttributeLoc::Return, attribute)
            }
            _ => {}
        }

        let abi = builder.map_layout(self.ret_abi.info.layout, |layout| layout.abi);

        if let AbiRepresentation::Scalar(scalar) = abi {
            if let ScalarKind::Int { .. } = scalar.kind() {
                // @@Hack: if the value is boolean, the range metadata would become
                // 0..0 due to the fact that the type of it is `i1`. This would be rejected
                // by the LLVM IR verifier... so we don't add the range metadata for
                // boolean types.
                if !scalar.is_bool() && !scalar.is_always_valid(builder) {
                    builder.add_range_metadata_to(
                        call_site.as_any_value_enum(),
                        scalar.valid_range(builder),
                    )
                }
            }
        }

        for arg in self.args.iter() {
            match &arg.mode {
                PassMode::Ignore => {}
                PassMode::Pair(a, b) => {
                    apply_attributes_to_arg(builder.ctx, a);
                    apply_attributes_to_arg(builder.ctx, b);
                }
                PassMode::Direct(attributes)
                | PassMode::Indirect { attributes, on_stack: false } => {
                    apply_attributes_to_arg(builder.ctx, attributes);
                }
                PassMode::Indirect { attributes, on_stack: true } => {
                    let index = apply_attributes_to_arg(builder.ctx, attributes);
                    let byval_attribute = builder.ctx.ll_ctx.create_type_attribute(
                        AttributeKind::ByVal as u32,
                        arg.info.llvm_ty(builder.ctx),
                    );

                    call_site.add_attribute(AttributeLoc::Param(index), byval_attribute)
                }
            }
        }

        // Adjust the calling convention if necessary.
        if self.calling_convention != CallingConvention::C {
            call_site.set_call_convention(self.calling_convention as u32);
        }

        // @@Future: we might need to additional information about the
        // element-type attribute for some LLVM intrinsics:
        //
        // https://llvm.org/docs/LangRef.html#parameter-attributes "elementtype<type>"
    }
}

/// Given a [CallSiteValue], apply the given [Attribute]s to the given
/// [AttributeLoc]. The [AttributeLoc] specifies where the attributes should be
/// applied, either being a function parameter, return value, or the function
/// itself.
fn apply_attributes_call_site(
    location: AttributeLoc,
    attributes: &[Attribute],
    call_site: CallSiteValue<'_>,
) {
    for attribute in attributes {
        call_site.add_attribute(location, *attribute)
    }
}
