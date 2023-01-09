//! Defines logic for lowering Hash IR places into the target backend
//! IR.

use hash_ir::{
    ir::Place,
    ty::{IrTy, TyOfPlace, VariantIdx},
};
use hash_target::alignment::Alignment;

use super::FnBuilder;
use crate::{
    layout::TyInfo,
    traits::{
        builder::BlockBuilderMethods, ctx::HasCtxMethods, layout::LayoutMethods,
        ty::BuildTypeMethods, CodeGenObject,
    },
};

/// A [PlaceRef] is the equivalent of an IR [Place], but within the code
/// generation context. The place holds a value that is backend dependent, type,
/// layout, and alignment information
#[derive(Debug, Clone, Copy)]
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

impl<'b, V: CodeGenObject> PlaceRef<V> {
    /// Apply a "discriminant" onto the [PlaceRef].
    pub fn codegen_set_discriminant<Builder: BlockBuilderMethods<'b, Value = V>>(
        &self,
        _builder: &mut Builder,
        _discriminant: VariantIdx,
    ) {
        todo!()
    }

    /// Get the "discriminant" of the [PlaceRef] and cast it
    /// to a specified type (which must be an integer type).
    pub fn codegen_get_discriminant<Builder: BlockBuilderMethods<'b, Value = V>>(
        self,
        _builder: &mut Builder,
        _cast_to: IrTy,
    ) -> V {
        todo!()
    }

    /// Emit a hint to the code generation backend that this [PlaceRef] is
    /// alive after this point.
    pub fn storage_live<Builder: BlockBuilderMethods<'b, Value = V>>(&self, builder: &mut Builder) {
        let layout = builder.ctx().layout_info(self.info.layout);
        builder.lifetime_start(self.value, layout.size);
    }

    /// Emit a hint to the code generation backend that this [PlaceRef] is
    /// now dead after this point and can be discarded.
    pub fn storage_dead<Builder: BlockBuilderMethods<'b, Value = V>>(&self, builder: &mut Builder) {
        let layout = builder.ctx().layout_info(self.info.layout);
        builder.lifetime_end(self.value, layout.size);
    }
}

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {
    /// Compute the type and layout of a [Place]. This deals with
    /// all projections that occur on the [Place].
    pub fn compute_place_ty_info(&self, builder: &mut Builder, place: Place) -> TyInfo {
        let place_ty = TyOfPlace::from_place(place, self.body, self.ctx.body_data());
        builder.layout_of_id(place_ty.ty)
    }

    /// Emit backend specific code for handling a [Place].
    ///
    /// This function will return a [PlaceRef] which can be used to
    /// store a value into the place which can be used by the called
    /// to `store` a value into the place.
    pub fn codegen_place(
        &mut self,
        _builder: &mut Builder,
        _place: Place,
    ) -> PlaceRef<Builder::Value> {
        todo!()
    }
}
