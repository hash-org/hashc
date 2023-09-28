//! Defines all of the intrinsics that are expected to be
//! declared within the language prelude.

use crate::ty::{InstanceId, IrTyId};

/// Defines all of the intrinsics that are present within the
/// language runtime, and will be filled in at code generation.
///
/// [Intrinsics] differ from language items in that they have no
/// defined body within the source, and are always filled in by
/// the compiler. This is because they require additional information
/// or access to the compiler internals that are not available to
/// the runtime. Furthermore, intrinsic behaviour differs from backend
/// to backend which makes it harder to define such items in the
/// source.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Intrinsic {
    /// The `ptr_offset` intrinsic function. This will offset a pointer
    /// by the specified amount.
    PtrOffset,

    /// The `transmute` intrinsic, documented in the prelude.
    Transmute,

    /// The `abort` intrinsic, terminates the program.
    Abort,

    /// Memory copy intrinsic.
    Memcpy,

    /// Memory compare intrinsic.
    Memcmp,
}

impl Intrinsic {
    /// Get the appropriate [Intrinsic] for the specified name.
    pub fn from_str_name(name: &str) -> Option<Self> {
        match name {
            "ptr_offset" => Some(Self::PtrOffset),
            "transmute" => Some(Self::Transmute),
            "memcpy" => Some(Self::Memcpy),
            "memcmp" => Some(Self::Memcmp),
            "abort" => Some(Self::Abort),
            _ => None,
        }
    }
}

/// Stored information about an intrinsic that has been referenced within
/// the program. The name "intrinsic" in this context refers to something
/// that is an intrinsic operation that must be filled in by the compiler i.e.
/// "ptr_offset", or it is an item definition that is crucial to the language
/// runtime i.e. "panic".
#[derive(Debug, Clone, Copy)]
pub struct IntrinsicData {
    /// The defined instance that corresponds to the intrinsic.
    instance: InstanceId,

    /// The type of the lang item.
    ty: IrTyId,
}

/// This struct is used to map the [Intrinsic] enum to the
/// associated type that is used to represent the intrinsic.
#[derive(Default)]
pub struct Intrinsics {
    /// The intrinsic map.
    intrinsics: [Option<IntrinsicData>; std::mem::variant_count::<Intrinsic>()],
}

impl Intrinsics {
    /// Create a new [Intrinsics] map instance. This will create
    /// all the associated types for the intrinsics, and will populate
    /// the map with them.
    pub fn new() -> Self {
        Self { intrinsics: [None; std::mem::variant_count::<Intrinsic>()] }
    }

    /// Set the [IrTyId] for the specified intrinsic.
    pub fn set(&mut self, intrinsic: Intrinsic, instance: InstanceId, ty: IrTyId) {
        self.intrinsics[intrinsic as usize] = Some(IntrinsicData { instance, ty });
    }

    /// Get the [InstanceId] for the specified intrinsic.
    pub fn get(&self, intrinsic: Intrinsic) -> Option<InstanceId> {
        self.intrinsics[intrinsic as usize].map(|item| item.instance)
    }

    /// Get the [InstanceId] for the specified intrinsic.
    pub fn get_ty(&self, intrinsic: Intrinsic) -> Option<IrTyId> {
        self.intrinsics[intrinsic as usize].map(|item| item.ty)
    }
}
