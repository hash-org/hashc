//! Contains logic for computing ABIs of function types and their
//! arguments.

use hash_abi::{
    ArgAbi, ArgAttributeFlag, ArgAttributes, ArgExtension, CallingConvention, FnAbi, PassMode,
};
use hash_ir::ty::{InstanceId, IrTy, IrTyId, Mutability, RefKind};
use hash_layout::compute::{LayoutComputer, LayoutError};
use hash_target::abi::{Abi, Scalar, ScalarKind};
use hash_utils::store::SequenceStore;

use crate::traits::{ctx::HasCtxMethods, layout::LayoutMethods};

/// Adjust the attributes of an argument ABI based on the provided
/// [Layout] and [Scalar] information. This is required to do since
/// the scalar maybe a pair of values.
fn adjust_arg_attributes(
    ctx: &LayoutComputer,
    attributes: &mut ArgAttributes,
    ty: IrTyId,
    scalar: Scalar,
) {
    // Booleans are always "noundef" values...
    if scalar.is_bool() {
        attributes.extend_with(ArgExtension::ZeroExtend);
        attributes.set(ArgAttributeFlag::NO_UNDEF);
        return;
    }

    // If this scalar should always be initialised then we can set the "noundef"
    // attribute.
    if !scalar.is_union() {
        attributes.set(ArgAttributeFlag::NO_UNDEF);
    }

    // If this scalar represents a pointer, then we can deduce more
    // information about this particular argument.
    let Scalar::Initialised { kind: ScalarKind::Pointer { .. }, valid_range } = scalar else {
        return;
    };

    // If the pointer is never null, then we can set the "non_null" attribute.
    if !valid_range.contains(0) {
        attributes.set(ArgAttributeFlag::NON_NULL);
    }

    // If the pointer type is a read-only, then we can set the "read_only"
    // attribute.
    ctx.ir_ctx().map_ty(ty, |ty| {
        let IrTy::Ref(_, mutability, kind) = ty else {
            return;
        };

        // @@Future: can we deduce the same thing for an `Rc` pointer?
        if matches!(kind, RefKind::Raw | RefKind::Normal) && *mutability == Mutability::Immutable {
            attributes.set(ArgAttributeFlag::READ_ONLY);
        }
    });

    // @@Todo: we currently can't deduce any information about aliasing of
    // pointer data, so we can't really derive the "no_alias" attribute. If
    // we become stricter with these rules, then we can possibly emit more
    // useful information here.
}

/// Errors that may occur when computing the ABI of a function.
#[derive(Debug)]
pub enum FnAbiError {
    /// A layout error occurred when computing the layout of a type
    /// for the ABI.
    Layout(LayoutError),
}

/// Compute an [FnAbi] from a provided [IrTyId]. If the ABI
/// has already been computed for the particular instance, then
/// the cached version of the ABI is returned.
///
/// N.B. the passed "ty" must be a function type.
pub fn compute_fn_abi_from_instance<'b, Ctx: HasCtxMethods<'b> + LayoutMethods<'b>>(
    ctx: &Ctx,
    instance: InstanceId,
) -> Result<FnAbi, FnAbiError> {
    // @@Todo: add caching for the ABI computation...

    // @@Todo: add support for specifying more calling conventions, but for now
    // we only support the C calling convention.
    let calling_convention = CallingConvention::C;

    // @@Todo: we should be able to deduce the ABI from the "Instance"
    // of the type since this stores attributes which specify which
    // ABI to use.
    //
    // This probably involves introducing `extern` keyword to allow
    // overriding the default ABI.
    let abi = Abi::Hash;

    let (params, return_ty) =
        ctx.ir_ctx().map_instance(instance, |instance| (instance.params, instance.ret_ty));

    let make_arg_abi = |ty: IrTyId, index: Option<usize>| {
        let is_return = index.is_none();

        let lc = ctx.layout_computer();
        let info = ctx.layout_of(ty);

        let mut arg = ArgAbi::new(&lc, info, |scalar| {
            let mut attributes = ArgAttributes::new();
            adjust_arg_attributes(&lc, &mut attributes, ty, scalar);
            attributes
        });

        // @@Todo: we might have to adjust the attribute pass mode
        // for ZSTs on specific platforms since they don't ignore them?
        if is_return && ctx.layouts().is_zst(info.layout) {
            arg.mode = PassMode::Ignore;
        }

        Ok(arg)
    };

    let mut fn_abi = FnAbi {
        args: ctx.ir_ctx().tls().map_fast(params, |tys| {
            tys.iter()
                .enumerate()
                .map(|(i, ty)| make_arg_abi(*ty, Some(i)))
                .collect::<Result<_, _>>()
        })?,
        ret_abi: make_arg_abi(return_ty, None)?,
        calling_convention,
    };

    adjust_fn_abi_for_specified_abi(ctx, &mut fn_abi, abi);
    Ok(fn_abi)
}

/// This function adjusts the ABI of a function based on the specified
/// ABI. This is required since the ABI of a function is not always
/// the same as the ABI of the arguments.
fn adjust_fn_abi_for_specified_abi<'b, Ctx: HasCtxMethods<'b>>(
    _ctx: &Ctx,
    _fn_abi: &mut FnAbi,
    abi: Abi,
) {
    if abi == Abi::Hash {
        // @@Todo: currently unclear what optimisations we can perform
        // here...
    } else {
        // Here we adjust to a platform specific ABI, based on the
        // platform.
        unimplemented!()
    }
}
