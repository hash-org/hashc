//! Defines a IR Builder for function blocks. This is essentially a builder
//! pattern for lowering declarations into the associated IR.

use hash_ast::ast::{AstNodeRef, Expr, FnDef};
use hash_ir::ir::{BasicBlock, BasicBlockData, Body, Terminator, TerminatorKind};
use hash_source::location::{SourceLocation, Span};
use hash_typecheck::storage::GlobalStorage;
use index_vec::IndexVec;

pub struct Builder<'tcx> {
    /// The [Span] of the function and the function body
    span: SourceLocation,

    /// The number of arguments that is passed
    arg_count: usize,

    /// The type storage needed for accessing the types of the traversed terms
    tcx: &'tcx GlobalStorage,

    /// The body control-flow graph
    control_flow_graph: ControlFlowGraph<'tcx>,
}

impl<'tcx> Builder<'tcx> {
    fn build_fn(&mut self, _node: AstNodeRef<FnDef>) -> Body<'tcx> {
        todo!()
    }

    /// Build a [Body] for a constant expression that occurs on the
    /// top-level of a module. If this function receives something that
    /// is non-constant, then the function will panic since it can't
    /// be sure that the provided block will be constant.
    ///
    /// This is a different concept from `compile-time` since in the future we
    /// will allow compile time expressions to run any arbitrary code.
    fn build_const(&mut self, _node: AstNodeRef<Expr>) -> Body<'tcx> {
        todo!()
    }
}

pub struct ControlFlowGraph<'tcx> {
    basic_blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>,
}

impl<'tcx> ControlFlowGraph<'tcx> {
    /// Get a reference to a [BasicBlock] inner [BasicBlockData].
    pub(crate) fn block_data(&self, blk: BasicBlock) -> &BasicBlockData<'tcx> {
        &self.basic_blocks[blk]
    }

    /// Get a mutable reference to a [BasicBlock] inner [BasicBlockData].
    pub(crate) fn block_data_mut(&mut self, blk: BasicBlock) -> &mut BasicBlockData<'tcx> {
        &mut self.basic_blocks[blk]
    }

    /// Create a new [BasicBlock]
    pub(crate) fn start_new_block(&mut self) -> BasicBlock {
        self.basic_blocks.push(BasicBlockData::new(None))
    }

    /// Function to terminate a particular [BasicBlock] provided that it has not
    /// been already terminated.
    pub(crate) fn terminate(&mut self, block: BasicBlock, span: Span, kind: TerminatorKind) {
        debug_assert!(
            self.block_data(block).terminator.is_none(),
            "terminate: block {:?}={:?} already has a terminator set",
            block,
            self.block_data(block)
        );
        self.block_data_mut(block).terminator = Some(Terminator { span, kind });
    }
}
