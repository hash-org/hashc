//! Defines the [BuilderCtx] which is a collection of all the
//! information required to lower all the TIR into IR, among
//! other operations.

use hash_ir::{ty::ReprTyId, IrCtx};
use hash_layout::{
    compute::{LayoutComputer, LayoutError},
    write::{LayoutWriter, LayoutWriterConfig},
    LayoutId, LayoutStorage, TyInfo,
};
use hash_pipeline::{interface::CompilerOutputStream, settings::CompilerSettings};
use hash_storage::store::statics::SequenceStoreValue;
use hash_target::{
    data_layout::{HasDataLayout, TargetDataLayout},
    HasTarget, Target,
};
use hash_tir::{
    atom_info::{AtomInfoStore, HasAtomInfo},
    context::{Context, HasContext},
    stores::tir_stores,
    tir::{Arg, DataDefId, DataTy, ModDefId, Node, NodeId},
};
use hash_utils::stream_writeln;

use crate::LoweringCtx;

/// The [BuilderCtx] is a collection of all the information and data stores that
/// are needed to lower the TIR into IR. This is only used during the initial
/// building of the IR, and is not used when optimising the IR or when code
/// generation is happening.
#[derive(Clone)]
pub(crate) struct BuilderCtx<'ir> {
    /// A reference to the lowering context that is used for
    /// lowering the TIR.
    pub lcx: &'ir IrCtx,

    /// The type layout context stores all relevant information to layouts and
    /// computing them.
    layouts: &'ir LayoutStorage,

    pub settings: &'ir CompilerSettings,

    /// The prelude that is used for lowering the TIR.
    pub prelude: ModDefId,

    /// The context
    pub context: Context,
}

impl HasDataLayout for BuilderCtx<'_> {
    fn data_layout(&self) -> &TargetDataLayout {
        &self.layouts.data_layout
    }
}

impl HasContext for BuilderCtx<'_> {
    fn context(&self) -> &Context {
        &self.context
    }
}

impl HasTarget for BuilderCtx<'_> {
    fn target(&self) -> &Target {
        self.settings.target()
    }
}

impl HasAtomInfo for BuilderCtx<'_> {
    fn atom_info(&self) -> &AtomInfoStore {
        tir_stores().atom_info()
    }
}

impl<'ir> BuilderCtx<'ir> {
    /// Create a new [BuilderCtx] from the given [LoweringCtx].
    pub fn new(ctx: &'ir LoweringCtx<'ir>) -> Self {
        let LoweringCtx {
            semantic_storage,
            workspace: _,
            icx: ir_storage,
            lcx: layout_storage,
            settings,
            ..
        } = ctx;

        let prelude = match semantic_storage.distinguished_items.prelude_mod.get() {
            Some(prelude) => *prelude,
            None => panic!("Tried to get prelude but it is not set yet"),
        };

        Self {
            lcx: &ir_storage.ctx,
            settings,
            layouts: layout_storage,
            prelude,
            context: Context::new(),
        }
    }

    /// Get a [LayoutComputer] which can be used to compute layouts and
    /// other layout related operations.
    pub fn layout_computer(&self) -> LayoutComputer {
        LayoutComputer::new(self.layouts)
    }

    /// Compute the layout of a given [ReprTyId].
    pub fn layout_of(&self, ty: ReprTyId) -> Result<LayoutId, LayoutError> {
        self.layout_computer().layout_of_ty(ty)
    }

    /// Compute the size of a given [ReprTyId].
    pub fn size_of(&self, ty: ReprTyId) -> Result<usize, LayoutError> {
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
