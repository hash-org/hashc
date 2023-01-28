//! Defines all of the intrinsics that are expected to be
//! declared within the language prelude.

use crate::ty::IrTyId;

/// Defines all of the intrinsics that are present within the
/// language runtime, and can be accessed by the language. This
/// does not capture "all" intrinsics since some are defined
/// at the backend level and might not be generally available.
/// The [Intrinsic] items are intrinsics that are required by the
/// language to provide functionality that cannot be provided
/// by the runtime itself, i.e. "panic".
///
/// @@Todo: this needs to record the number of arguments the intrinsic
/// takes, and possibly other information.
pub enum Intrinsic {
    /// The `panic` intrinsic function. This will cause the program
    /// to terminate.
    Panic,
}

/// This struct is used to map the [Intrinsic] enum to the
/// associated type that is used to represent the intrinsic.
#[derive(Default)]
pub struct Intrinsics {
    /// The intrinsic map.
    intrinsics: [Option<IrTyId>; std::mem::variant_count::<Intrinsic>()],
}

impl Intrinsics {
    /// Create a new [Intrinsics] map instance. This will create
    /// all the associated types for the intrinsics, and will populate
    /// the map with them.
    pub fn new() -> Self {
        Self { intrinsics: [None; std::mem::variant_count::<Intrinsic>()] }
    }

    /// Set the [IrTyId] for the specified intrinsic.
    pub fn set(&mut self, intrinsic: Intrinsic, ty: IrTyId) {
        self.intrinsics[intrinsic as usize] = Some(ty);
    }

    /// Get the [IrTyId] for the specified intrinsic.
    pub fn get(&self, intrinsic: Intrinsic) -> Option<IrTyId> {
        self.intrinsics[intrinsic as usize]
    }
}
