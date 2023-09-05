//! Defines the [BuilderCtx] which is a collection of all the
//! information required to lower all the TIR into IR, among
//! other operations.

use hash_intrinsics::intrinsics::{AccessToIntrinsics, DefinedIntrinsics};
use hash_ir::{ty::IrTyId, IrCtx};
use hash_layout::{
    compute::{LayoutComputer, LayoutError},
    write::{LayoutWriter, LayoutWriterConfig},
    LayoutCtx, LayoutId, TyInfo,
};
use hash_pipeline::{interface::CompilerOutputStream, settings::CompilerSettings};
use hash_storage::store::statics::SequenceStoreValue;
use hash_target::{
    data_layout::{HasDataLayout, TargetDataLayout},
    HasTarget,
};
use hash_tir::{
    args::Arg,
    data::{DataDefId, DataTy},
    environment::{
        env::{AccessToEnv, Env},
        source_info::CurrentSourceInfo,
    },
    mods::ModDefId,
    node::Node,
};
use hash_utils::stream_writeln;

use crate::LoweringCtx;

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
    pub env: Env<'ir>,

    pub settings: &'ir CompilerSettings,

    /// The intrinsic definitions that are needed for
    /// dealing with intrinsic functions within the TIR.
    pub intrinsics: &'ir DefinedIntrinsics,

    /// The prelude that is used for lowering the TIR.
    pub prelude: ModDefId,
}

impl HasDataLayout for BuilderCtx<'_> {
    fn data_layout(&self) -> &TargetDataLayout {
        &self.layouts.data_layout
    }
}

impl<'ir> AccessToEnv for BuilderCtx<'ir> {
    fn env(&self) -> &Env {
        &self.env
    }
}

impl<'ir> AccessToIntrinsics for BuilderCtx<'ir> {
    fn intrinsics(&self) -> &DefinedIntrinsics {
        self.intrinsics
    }
}

impl<'ir> BuilderCtx<'ir> {
    /// Create a new [BuilderCtx] from the given [LoweringCtx].
    pub fn new(entry: &'ir CurrentSourceInfo, ctx: &'ir LoweringCtx<'ir>) -> Self {
        let LoweringCtx {
            semantic_storage, workspace, ir_storage, layout_storage, settings, ..
        } = ctx;

        let env =
            Env::new(&semantic_storage.context, &workspace.node_map, settings.target(), entry);

        let intrinsics = match semantic_storage.intrinsics_or_unset.get() {
            Some(intrinsics) => intrinsics,
            None => panic!("Tried to get intrinsics but they are not set yet"),
        };

        let prelude = match semantic_storage.prelude_or_unset.get() {
            Some(prelude) => *prelude,
            None => panic!("Tried to get prelude but it is not set yet"),
        };

        Self { env, lcx: &ir_storage.ctx, settings, layouts: layout_storage, intrinsics, prelude }
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
        Ok(self.layout_of(ty)?.size().bytes().try_into().unwrap())
    }

    /// Dump the layout of a given type.
    pub(crate) fn dump_ty_layout(&self, data_def: DataDefId, mut out: CompilerOutputStream) {
        let ty = self.ty_from_tir_data(DataTy {
            args: Node::create_at(Node::<Arg>::empty_seq(), data_def.origin()),
            data_def,
        });
        let layout = self.layout_of(ty).unwrap();

        let writer_config = LayoutWriterConfig::from_character_set(self.settings.character_set);

        // Print the layout
        stream_writeln!(
            out,
            "{}",
            LayoutWriter::new_with_config(
                TyInfo { ty, layout },
                self.layout_computer(),
                writer_config
            )
        );
    }
}
