//! Defines logic for lowering Hash IR places into the target backend
//! IR.

use hash_target::alignment::Alignment;

use crate::layout::TyInfo;

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
