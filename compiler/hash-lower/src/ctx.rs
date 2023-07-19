//! Defines the [BuilderCtx] which is a collection of all the
//! information required to lower all the TIR into IR, among
//! other operations.

use hash_intrinsics::{
    intrinsics::{AccessToIntrinsics, DefinedIntrinsics},
    primitives::{AccessToPrimitives, DefinedPrimitives},
};
use hash_ir::{ty::IrTyId, IrCtx};
use hash_layout::{
    compute::{LayoutComputer, LayoutError},
    LayoutCtx, LayoutId,
};
use hash_semantics::SemanticStorage;
use hash_tir::{
    environment::env::{AccessToEnv, Env},
    mods::ModDefId,
};

/// The [BuilderCtx] is a collection of all the information and data stores that
/// are needed to lower the TIR into IR. This is only used during the initial
/// building of the IR, and is not used when optimising the IR or when code
/// generation is happening.
#[derive(Clone, Copy)]
pub(crate) struct BuilderCtx<'ir> {
    /// A reference to the lowering context that is used for
    /// lowering the TIR.
    pub lcx: &'ir IrCtx,

    /// The type layout context stores all relevant information to layouts and
    /// computing them.
    layouts: &'ir LayoutCtx,

    /// The type storage needed for accessing the types of the traversed terms
    pub env: &'ir Env<'ir>,

    /// The primitive definitions that are needed for creating and comparing
    /// primitive types with the TIR.
    pub primitives: &'ir DefinedPrimitives,

    /// The intrinsic definitions that are needed for
    /// dealing with intrinsic functions within the TIR.
    pub intrinsics: &'ir DefinedIntrinsics,

    /// The prelude that is used for lowering the TIR.
    pub prelude: ModDefId,
}

impl<'ir> AccessToEnv for BuilderCtx<'ir> {
    fn env(&self) -> &Env {
        self.env
    }
}

impl<'ir> AccessToPrimitives for BuilderCtx<'ir> {
    fn primitives(&self) -> &DefinedPrimitives {
        self.primitives
    }
}

impl<'ir> AccessToIntrinsics for BuilderCtx<'ir> {
    fn intrinsics(&self) -> &DefinedIntrinsics {
        self.intrinsics
    }
}

impl<'ir> BuilderCtx<'ir> {
    /// Create a new [Ctx] from the given [Env] and
    /// [SemanticStorage].
    pub fn new(
        lcx: &'ir IrCtx,
        layouts: &'ir LayoutCtx,
        env: &'ir Env<'ir>,
        storage: &'ir SemanticStorage,
    ) -> Self {
        let primitives = match storage.primitives_or_unset.get() {
            Some(primitives) => primitives,
            None => panic!("Tried to get primitives but they are not set yet"),
        };

        let intrinsics = match storage.intrinsics_or_unset.get() {
            Some(intrinsics) => intrinsics,
            None => panic!("Tried to get intrinsics but they are not set yet"),
        };

        let prelude = match storage.prelude_or_unset.get() {
            Some(prelude) => *prelude,
            None => panic!("Tried to get prelude but it is not set yet"),
        };

        Self { env, lcx, layouts, primitives, intrinsics, prelude }
    }

    /// Get a [LayoutComputer] which can be used to compute layouts and
    /// other layout related operations.
    pub fn layout_computer(&self) -> LayoutComputer {
        LayoutComputer::new(self.layouts)
    }

    /// Compute the layout of a given [IrTyId].
    pub fn layout_of(&self, ty: IrTyId) -> Result<LayoutId, LayoutError> {
        self.layout_computer().layout_of_ty(ty)
    }

    /// Compute the size of a given [IrTyId].
    pub fn size_of(&self, ty: IrTyId) -> Result<usize, LayoutError> {
        Ok(self.layouts.size_of(self.layout_of(ty)?).bytes().try_into().unwrap())
    }
}
