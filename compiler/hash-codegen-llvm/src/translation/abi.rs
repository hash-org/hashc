//! This implements all of the ABI specified methods for the [Builder].

use hash_codegen::{
    abi::{
        ArgAbi, ArgAttributeFlag, ArgAttributes, ArgExtension, CallingConvention, FnAbi, PassMode,
    },
    lower::{operands::OperandValue, place::PlaceRef},
    traits::{
        abi::AbiBuilderMethods, builder::BlockBuilderMethods, layout::LayoutMethods,
        ty::TypeBuilderMethods, HasCtxMethods,
    },
};
use hash_target::abi::{AbiRepresentation, ScalarKind};
use hash_utils::smallvec::SmallVec;
use inkwell::{
    attributes::{Attribute, AttributeLoc},
    types::{AnyTypeEnum, PointerType},
    values::{AnyValue, AnyValueEnum, CallSiteValue, FunctionValue},
};

use super::{ty::ExtendedTyBuilderMethods, Builder};
use crate::{ctx::CodeGenCtx, misc::AttributeKind};

impl<'b, 'm> AbiBuilderMethods<'b> for Builder<'_, 'b, 'm> {
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

    fn arg_ty(&mut self, arg_abi: &ArgAbi) -> Self::Type {
        self.backend_ty_from_info(arg_abi.info)
    }
}

pub trait ExtendedArgAbiMethods<'m> {
    /// Get the type of the memory location that is backing
    /// the given [ArgAbi].
    fn get_memory_ty(&self, ctx: &CodeGenCtx<'_, 'm>) -> AnyTypeEnum<'m>;

    /// Store the given [AnyValueEnum] into the given [PlaceRef].
    fn store(
        &self,
        builder: &mut Builder<'_, '_, 'm>,
        value: AnyValueEnum<'m>,
        destination: PlaceRef<AnyValueEnum<'m>>,
    );

    /// Store the given function argument into the given [PlaceRef].
    fn store_fn_arg(
        &self,
        builder: &mut Builder<'_, '_, 'm>,
        index: &mut usize,
        destination: PlaceRef<AnyValueEnum<'m>>,
    );
}

impl<'m> ExtendedArgAbiMethods<'m> for ArgAbi {
    fn store(
        &self,
        builder: &mut Builder<'_, '_, 'm>,
        value: AnyValueEnum<'m>,
        destination: PlaceRef<AnyValueEnum<'m>>,
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
        builder: &mut Builder<'_, '_, 'm>,
        index: &mut usize,
        destination: PlaceRef<AnyValueEnum<'m>>,
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

    fn get_memory_ty(&self, ctx: &CodeGenCtx<'_, 'm>) -> AnyTypeEnum<'m> {
        self.info.llvm_ty(ctx)
    }
}

pub trait ExtendedArgAttributeMethods<'m> {
    /// Get a list of attributes that are currently set on the
    /// [ArhAttributes].
    fn get_attributes(&self, ctx: &CodeGenCtx<'_, 'm>) -> SmallVec<[Attribute; 4]>;

    /// Apply the given [ArgAttributes] to the the [FunctionValue]
    /// with the specified [AttributeLoc] which indicates whether
    /// to apply the attributes onto an argument, return value or the
    /// function definition itself.
    fn apply_attributes_to_fn(
        &self,
        ctx: &CodeGenCtx<'_, 'm>,
        index: AttributeLoc,
        value: FunctionValue<'m>,
    );

    /// Apply the given [ArgAttributes] to the the [CallSiteValue]
    /// with the specified [AttributeLoc] which indicates whether
    /// to apply the attributes onto an argument, return value or the
    /// function call itself.
    fn apply_attributes_to_call_site(
        &self,
        ctx: &CodeGenCtx<'_, 'm>,
        index: AttributeLoc,
        value: CallSiteValue<'m>,
    );
}

/// Attributes that affect the ABI of a function argument. These
/// attributes (if present) are always applied onto the relevant
/// argument.
const ABI_AFFECTING_ATTRIBUTES: [(ArgAttributeFlag, AttributeKind); 1] =
    [(ArgAttributeFlag::IN_REG, AttributeKind::InReg)];

const ATTRIBUTE_MAP: [(ArgAttributeFlag, AttributeKind); 5] = [
    (ArgAttributeFlag::NO_ALIAS, AttributeKind::NoAlias),
    (ArgAttributeFlag::NO_CAPTURE, AttributeKind::NoCapture),
    (ArgAttributeFlag::NO_UNDEF, AttributeKind::NoUndef),
    (ArgAttributeFlag::NON_NULL, AttributeKind::NonNull),
    (ArgAttributeFlag::READ_ONLY, AttributeKind::ReadOnly),
];

impl<'m> ExtendedArgAttributeMethods<'m> for ArgAttributes {
    fn get_attributes(&self, ctx: &CodeGenCtx<'_, 'm>) -> SmallVec<[Attribute; 4]> {
        let mut attributes = SmallVec::new();

        // Always apply the ABI specific attributes.
        for (flag, kind) in &ABI_AFFECTING_ATTRIBUTES {
            if self.flags.contains(*flag) {
                attributes.push(kind.create_attribute(ctx));
            }
        }

        // If we need to extend the arguments, then specify this...
        match self.extension {
            ArgExtension::NoExtend => {}
            ArgExtension::ZeroExtend => {
                attributes.push(AttributeKind::ZExt.create_attribute(ctx));
            }
            ArgExtension::SignExtend => {
                attributes.push(AttributeKind::SExt.create_attribute(ctx));
            }
        }

        // If the optimisation level is set to "release" then we apply these
        // arguments...
        if ctx.settings().optimisation_level.is_release() {
            let mut flags = self.flags;
            let pointee_size = self.pointee_size.bytes();

            if pointee_size != 0 {
                let attribute = if self.flags.contains(ArgAttributeFlag::NON_NULL) {
                    ctx.ll_ctx
                        .create_enum_attribute(AttributeKind::Dereferenceable as u32, pointee_size)
                } else {
                    ctx.ll_ctx.create_enum_attribute(
                        AttributeKind::DereferenceableOrNull as u32,
                        pointee_size,
                    )
                };

                attributes.push(attribute);

                // Remove the nonnull attribute if it is present.
                flags -= ArgAttributeFlag::NON_NULL;
            }

            for (flag, kind) in &ATTRIBUTE_MAP {
                if flags.contains(*flag) {
                    attributes.push(kind.create_attribute(ctx));
                }
            }
        }

        attributes
    }

    fn apply_attributes_to_fn(
        &self,
        ctx: &CodeGenCtx<'_, 'm>,
        location: AttributeLoc,
        func: FunctionValue<'m>,
    ) {
        // Compute the attributes we need to apply to the function.
        for attribute in self.get_attributes(ctx) {
            func.add_attribute(location, attribute);
        }
    }

    fn apply_attributes_to_call_site(
        &self,
        ctx: &CodeGenCtx<'_, 'm>,
        location: AttributeLoc,
        call_site: CallSiteValue<'m>,
    ) {
        let attributes = self.get_attributes(ctx);
        apply_attributes_call_site(location, &attributes, call_site)
    }
}

pub trait ExtendedFnAbiMethods<'b, 'm> {
    /// Produce an LLVM type for the given [FnAbi].
    fn llvm_ty(&self, ctx: &CodeGenCtx<'b, 'm>) -> AnyTypeEnum<'m>;

    /// Produce an Pointer to the type of this [FnAbi].
    fn ptr_to_llvm_ty(&self, ctx: &CodeGenCtx<'b, 'm>) -> PointerType<'m> {
        ctx.type_ptr_to(self.llvm_ty(ctx)).into_pointer_type()
    }

    /// Apply the derived ABI attributes to the given [FunctionValue].
    fn apply_attributes_to_fn(&self, ctx: &CodeGenCtx<'b, 'm>, func: FunctionValue<'m>);

    /// Apply the derived ABI attributes to the given [CallSiteValue].
    fn apply_attributes_call_site(
        &self,
        builder: &mut Builder<'_, 'b, 'm>,
        call_site: CallSiteValue<'m>,
    );
}

impl<'b, 'm> ExtendedFnAbiMethods<'b, 'm> for FnAbi {
    fn llvm_ty(&self, ctx: &CodeGenCtx<'b, 'm>) -> AnyTypeEnum<'m> {
        let arg_count = self.args.len() + if self.ret_abi.mode.is_indirect() { 1 } else { 0 };
        let mut arg_tys = Vec::with_capacity(arg_count);

        let return_ty = match &self.ret_abi.mode {
            PassMode::Ignore => ctx.type_void(),
            PassMode::Direct(_) | PassMode::Pair(_, _) => self.ret_abi.info.immediate_llvm_ty(ctx),
            PassMode::Indirect { .. } => {
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

    fn apply_attributes_to_fn(&self, ctx: &CodeGenCtx<'_, 'm>, func: FunctionValue<'m>) {
        let mut fn_attributes = SmallVec::<[Attribute; 1]>::new();

        // If the return type is un-inhabited then we can mark the
        // function as a "no-return".
        if ctx.map_layout(self.ret_abi.info.layout, |layout| layout.abi.is_uninhabited()) {
            fn_attributes.push(AttributeKind::NoReturn.create_attribute(ctx));
        }

        apply_attributes_to_fn(AttributeLoc::Function, &fn_attributes, func);

        let mut index = 0;
        let mut apply_attributes_to_arg = |attrs: &ArgAttributes| {
            attrs.apply_attributes_to_fn(ctx, AttributeLoc::Param(index), func);
            index += 1;
            index - 1
        };

        // Apply all of the attributes onto the return value of the function.
        match &self.ret_abi.mode {
            PassMode::Direct(attrs) => {
                attrs.apply_attributes_to_fn(ctx, AttributeLoc::Return, func);
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

                func.add_attribute(AttributeLoc::Param(index), attribute)
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

    fn apply_attributes_call_site(
        &self,
        builder: &mut Builder<'_, '_, 'm>,
        call_site: CallSiteValue<'m>,
    ) {
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
        let mut apply_attributes_to_arg = |ctx: &CodeGenCtx<'_, 'm>, attrs: &ArgAttributes| {
            attrs.apply_attributes_to_call_site(ctx, AttributeLoc::Param(index), call_site);
            index += 1;
            index - 1
        };

        // Apply all of the attributes onto the return value of the function.
        //
        // @@CopyPaste: from above function
        match &self.ret_abi.mode {
            PassMode::Direct(attrs) => {
                attrs.apply_attributes_to_call_site(builder.ctx, AttributeLoc::Return, call_site);
            }
            PassMode::Indirect { attributes, on_stack } => {
                debug_assert!(!on_stack); // @@Explain
                let index = apply_attributes_to_arg(builder.ctx, attributes);

                // Now we apply the attribute that this return value is a
                // str]uct return type.
                let attribute = builder.ctx.ll_ctx.create_type_attribute(
                    AttributeKind::StructRet as u32,
                    self.ret_abi.info.llvm_ty(builder.ctx),
                );

                call_site.add_attribute(AttributeLoc::Param(index), attribute)
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

/// Given a [FunctionValue], apply the given [Attribute]s to the given
/// [AttributeLoc]. The [AttributeLoc] specifies where the attributes should be
/// applied, either being a function parameter, return value, or the function
/// itself.
fn apply_attributes_to_fn(
    location: AttributeLoc,
    attributes: &[Attribute],
    func: FunctionValue<'_>,
) {
    for attribute in attributes {
        func.add_attribute(location, *attribute)
    }
}
