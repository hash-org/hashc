//! Contains logic for computing ABIs of function types and their
//! arguments.

use hash_abi::{
    ArgAbi, ArgAttributeFlag, ArgAttributes, ArgExtension, CallingConvention, FnAbi, PassMode,
};
use hash_ir::ty::{Instance, InstanceId, Mutability, RefKind, ReprTy, ReprTyId, ReprTyListId};
use hash_repr::compute::LayoutError;
use hash_storage::store::statics::StoreId;
use hash_target::abi::{Scalar, ScalarKind};

use crate::traits::{layout::LayoutMethods, HasCtxMethods};

/// Adjust the attributes of an argument ABI based on the provided
/// [Layout] and [Scalar] information. This is required to do since
/// the scalar maybe a pair of values.
fn adjust_arg_attributes(
    attributes: &mut ArgAttributes,
    ty: ReprTyId,
    scalar: Scalar,
    is_return: bool,
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
    ty.map(|ty| {
        let ReprTy::Ref(_, mutability, kind) = ty else {
            return;
        };

        // @@Future: can we deduce the same thing for an `Rc` pointer?
        if !is_return
            && matches!(kind, RefKind::Raw | RefKind::Normal)
            && *mutability == Mutability::Immutable
        {
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

/// Compute an [FnAbi] from a provided [Instance]. 
pub fn compute_fn_abi_from_instance<'b, Ctx: HasCtxMethods<'b> + LayoutMethods<'b>>(
    ctx: &Ctx,
    instance: InstanceId,
) -> Result<FnAbi, FnAbiError> {
    let Instance { params, return_ty, abi, .. } = instance.value();

    // map the ABI to a calling convention whilst making any adjustments according
    // to the target.
    let calling_convention = CallingConvention::make_from_abi_and_target(abi, ctx.target());

    compute_fn_abi(ctx, params, return_ty, calling_convention)
}

/// Compute an [FnAbi] from a provided function parameter and return type, with 
/// a given calling convention.
pub fn compute_fn_abi<'b, Ctx: HasCtxMethods<'b> + LayoutMethods<'b>>(
    ctx: &Ctx,
    params: ReprTyListId,
    ret_ty: ReprTyId,
    calling_convention: CallingConvention,
) -> Result<FnAbi, FnAbiError> {
    // Closure to create a new argument for the ABI from a given type.
    let make_arg_abi = |ty: ReprTyId, index: Option<usize>| {
        let is_return = index.is_none();
        let info = ctx.layout_of(ty);

        let mut arg = ArgAbi::new(info, |scalar| {
            let mut attributes = ArgAttributes::new();
            adjust_arg_attributes(&mut attributes, ty, scalar, is_return);
            attributes
        });

        // @@Todo: we might have to adjust the attribute pass mode
        // for ZSTs on specific platforms since they don't ignore them?
        if is_return && info.is_zst() {
            arg.mode = PassMode::Ignore;
        }

        Ok(arg)
    };

    let fn_abi = FnAbi {
        args: params
            .borrow()
            .iter()
            .enumerate()
            .map(|(i, ty)| make_arg_abi(*ty, Some(i)))
            .collect::<Result<_, _>>()?,
        ret_abi: make_arg_abi(ret_ty, None)?,
        calling_convention,
    };

    Ok(fn_abi)
}
