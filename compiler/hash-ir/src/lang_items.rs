//! Defines all of the intrinsics that are expected to be
//! declared within the language prelude.

use crate::ty::{InstanceId, IrTyId};

/// Defines all of the language items that are required for
/// facilitating the feature's of the language.
pub enum LangItem {
    /// The `panic` intrinsic function. This will cause the program
    /// to terminate.
    Panic,

    /// The `str_eq` intrinsic function. This will compare two strings
    /// and return a boolean value.
    StrEq,
}

impl LangItem {
    /// Get the appropriate [LangItem] for the specified name.
    pub fn from_str_name(name: &str) -> Self {
        match name {
            "panic" => Self::Panic,
            "str_eq" => Self::StrEq,
            _ => panic!("unknown language item: {name}"),
        }
    }
}

/// Stored information about an intrinsic that has been referenced within
/// the program. The name "intrinsic" in this context refers to something
/// that is an intrinsic operation that must be filled in by the compiler i.e.
/// "ptr_offset", or it is an item definition that is crucial to the language
/// runtime i.e. "panic".
#[derive(Debug, Clone, Copy)]
pub struct LangItemData {
    /// The defined instance that corresponds to the intrinsic.
    instance: InstanceId,

    /// The type of the lang item.
    ty: IrTyId,
}

/// This struct is used to map the [Intrinsic] enum to the
/// associated type that is used to represent the intrinsic.
#[derive(Default)]
pub struct LangItems {
    /// The intrinsic map.
    items: [Option<LangItemData>; std::mem::variant_count::<LangItem>()],
}

impl LangItems {
    /// Create a new [Intrinsics] map instance. This will create
    /// all the associated types for the intrinsics, and will populate
    /// the map with them.
    pub fn new() -> Self {
        Self { items: [None; std::mem::variant_count::<LangItem>()] }
    }

    /// Set the [IrTyId] for the specified intrinsic.
    pub fn set(&mut self, item: LangItem, instance: InstanceId, ty: IrTyId) {
        self.items[item as usize] = Some(LangItemData { instance, ty });
    }

    /// Get the [InstanceId] for the specified intrinsic.
    pub fn get(&self, item: LangItem) -> Option<InstanceId> {
        self.items[item as usize].map(|item| item.instance)
    }

    /// Get the [IrTyId] for the specified intrinsic.
    pub fn get_ty(&self, item: LangItem) -> Option<IrTyId> {
        self.items[item as usize].map(|item| item.ty)
    }
}
