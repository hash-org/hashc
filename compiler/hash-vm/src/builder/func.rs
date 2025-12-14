//! Function builder related logic for the Hash VM.

use hash_abi::FnAbiId;
use hash_utils::index_vec::IndexVec;

use crate::bytecode::{Instruction, op::LabelOffset, pretty::FunctionBody};

// Import FunctionBuilder if it's defined in another module
#[derive(Debug)]
pub struct FunctionBuilder {
    /// The ABI of the function, this is used to generate
    /// the correct instructions for the function, to read the
    /// arguments and return values correctly.
    pub abi: FnAbiId,

    /// The body of the function. All instructions that make up the function
    /// are stored within the body. However, labels are stored separately to
    /// allow for easier management of jumps and branches.
    pub body: IndexVec<LabelOffset, Instruction>,

    /// The labels within the function body, these are used to
    /// manage jumps and branches. The labels store the literal index
    /// within the function body where the label is located. This is essentially
    /// a mapping from instruction labels to their offsets:
    ///
    ///  0 -=-> LabelOffset(0)
    ///     |
    ///     \  Instruction 0
    ///        Instruction 1
    ///        ...
    ///  1---> LabelOffset(5):
    ///    |
    ///     \ Instruction 5
    ///       ...
    pub labels: IndexVec<LabelOffset, LabelOffset>,
}

impl FunctionBuilder {
    /// Create a new [FunctionBuilder] with the given ABI.
    pub fn new(abi: FnAbiId) -> Self {
        Self { abi, body: IndexVec::new(), labels: IndexVec::new() }
    }

    /// Add an instruction to the function body.
    pub fn emit(&mut self, instruction: Instruction) {
        self.body.push(instruction);
    }

    /// Append multiple instructions to the function body.
    pub fn append(&mut self, instructions: Vec<Instruction>) {
        self.body.extend(instructions);
    }

    /// Append a new block with its own label to the function body.
    pub fn append_block(&mut self, instructions: Vec<Instruction>) {
        let label = LabelOffset::new(self.body.len());
        self.body.extend(instructions);
        self.labels.push(label);
    }
}

impl FunctionBody for FunctionBuilder {
    fn labels(&self) -> &IndexVec<LabelOffset, LabelOffset> {
        &self.labels
    }

    fn instructions(&self) -> &IndexVec<LabelOffset, Instruction> {
        &self.body
    }
}
