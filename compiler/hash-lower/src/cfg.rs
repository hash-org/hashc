//! Data structure representing the Control-Flow-Graph(CFG) that is used to
//! represent lowered functions or constant blocks.

use hash_ir::{
    ir::{
        BasicBlock, BasicBlockData, Place, RValue, RValueId, Statement, StatementKind, Terminator,
        TerminatorKind,
    },
    IrStorage,
};
use hash_source::location::Span;
use index_vec::IndexVec;

pub struct ControlFlowGraph {
    /// The basic blocks that this control flow graph contains.
    pub(crate) basic_blocks: IndexVec<BasicBlock, BasicBlockData>,
}

impl ControlFlowGraph {
    /// Create a new empty control-flow graph
    pub fn new() -> Self {
        Self { basic_blocks: IndexVec::new() }
    }

    /// Get a reference to a [BasicBlock] inner [BasicBlockData].
    pub(crate) fn block_data(&self, block: BasicBlock) -> &BasicBlockData {
        &self.basic_blocks[block]
    }

    /// Get a mutable reference to a [BasicBlock] inner [BasicBlockData].
    pub(crate) fn block_data_mut(&mut self, block: BasicBlock) -> &mut BasicBlockData {
        &mut self.basic_blocks[block]
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

    /// Add a [Statement] to the specified [BasicBlock]
    pub(crate) fn push(&mut self, block: BasicBlock, statement: Statement) {
        self.block_data_mut(block).statements.push(statement);
    }

    /// Add a [Statement] with kind [StatementKind::Assign]
    pub(crate) fn push_assign(
        &mut self,
        block: BasicBlock,
        place: Place,
        value: RValueId,
        span: Span,
    ) {
        self.push(block, Statement { kind: StatementKind::Assign(place, value), span });
    }

    /// Terminate a [BasicBlock] by adding a [TerminatorKind::Goto]
    pub(crate) fn goto(&mut self, source: BasicBlock, target: BasicBlock, span: Span) {
        self.terminate(source, span, TerminatorKind::Goto(target));
    }
}
