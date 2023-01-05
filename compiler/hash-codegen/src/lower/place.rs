//! Defines logic for lowering Hash IR places into the target backend
//! IR.

use hash_target::alignment::Alignment;

use crate::{
    layout::TyInfo,
    traits::{
        builder::BlockBuilderMethods, ctx::HasCtxMethods, ty::BuildTypeMethods, CodeGenObject,
    },
};

/// A [PlaceRef] is the equivalent of an IR [Place], but within the code
/// generation context. The place holds a value that is backend dependent, type,
/// layout, and alignment information
pub struct PlaceRef<V> {
    /// The value of the place.
    pub value: V,

    /// The type and layout of the value.
    pub info: TyInfo,

    // The alignment of the value.
    pub alignment: Alignment,
}

impl<'b, V: CodeGenObject> PlaceRef<V> {
    /// Create a new [PlaceRef] from an existant value.
    pub fn new<Builder: BlockBuilderMethods<'b, Value = V>>(
        builder: &mut Builder,
        value: V,
        info: TyInfo,
    ) -> Self {
        let layout = builder.ctx().layout_info(info.layout);
        let alignment = layout.alignment.abi;

        Self { value, info, alignment }
    }

    /// Create a new [PlaceRef] which refers to a value allocated on the
    /// function stack.
    pub fn new_stack<Builder: BlockBuilderMethods<'b, Value = V>>(
        builder: &mut Builder,
        info: TyInfo,
    ) -> Self {
        let layout = builder.ctx().layout_info(info.layout);
        let alignment = layout.alignment.abi;

        let temp = builder.alloca(builder.ctx().backend_type(info), alignment);

        Self::new(builder, temp, info)
    }
}
