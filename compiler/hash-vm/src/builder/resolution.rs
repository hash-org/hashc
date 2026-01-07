use crate::{
    builder::{BytecodeBuilder, FunctionBuilder},
    bytecode::{Instruction, Operand},
};

impl BytecodeBuilder {
    pub fn absorb(&mut self, func: &FunctionBuilder) -> usize {
        let body = func.body();
        let labels = func.label_offsets();
        let offset = self.instructions.len();

        // Reserve space for the function body instructions.
        self.instructions.reserve(body.len());

        // We need to resolve all of the labels within the function body, i.e. they
        // should now use the "global" offsets within the entire bytecode
        // program, rather than the relative offsets within the function body.
        for mut instruction in body.into_iter().copied() {
            match &mut instruction {
                Instruction::Jmp { location, .. }
                | Instruction::JmpPos { location, .. }
                | Instruction::JmpNeg { location, .. }
                | Instruction::JmpZero { location, .. } => {
                    if let Operand::Label(label) = *location {
                        // Resolve the label offset to the global instruction offset
                        let function_label = labels[label].get();
                        let global_offset = function_label + offset;
                        *location = Operand::Immediate(global_offset);
                    }
                }
                _ => {}
            }

            self.instructions.push(instruction);
        }

        offset
    }

    pub fn build(self) -> Vec<Instruction> {
        self.instructions
    }
}
