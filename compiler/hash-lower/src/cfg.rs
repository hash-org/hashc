//! Data structure representing the Control-Flow-Graph(CFG) that is used to
//! represent lowered functions or constant blocks.

use std::fmt;

use hash_ir::ir::{
    BasicBlock, BasicBlockData, Place, RValueId, Statement, StatementKind, Terminator,
    TerminatorKind,
};
use hash_source::location::Span;
use index_vec::IndexVec;

pub struct ControlFlowGraph {
    /// The basic blocks that this control flow graph contains.
    pub(crate) basic_blocks: IndexVec<BasicBlock, BasicBlockData>,
}

impl fmt::Debug for ControlFlowGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (id, block) in self.basic_blocks.iter_enumerated() {
            write!(f, "{:?}", id)?;

            if let Some(terminator) = &block.terminator {
                writeln!(f, " -> {:?}", terminator)?;
            } else {
                writeln!(f, " -> <none>")?;
            }
        }

        Ok(())
    }
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

    /// Create a [BasicBlock] that is terminated by a [TerminatorKind::Return]
    /// and has no other present statements.
    pub(crate) fn make_return_block(&mut self) -> BasicBlock {
        let block = self.start_new_block();
        self.block_data_mut(block).terminator =
            Some(Terminator { kind: TerminatorKind::Return, span: Span::default() });
        block
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

    /// Check whether a block has been terminated or not.
    pub(crate) fn is_terminated(&self, block: BasicBlock) -> bool {
        self.block_data(block).terminator.is_some()
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
