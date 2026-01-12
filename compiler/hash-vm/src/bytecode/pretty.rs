//! This module contains the logic and implementation in order to
//! write bytecode as a human-readable string format. The specific
//! implementation is reliant on passing a "function" body that is to
//! be pretty printed.

use std::fmt;

use hash_utils::index_vec::IndexVec;

use crate::bytecode::{Instruction, LabelOffset};

pub trait FunctionBody {
    /// Get the labels within the function body.
    fn labels(&self) -> &IndexVec<LabelOffset, LabelOffset>;

    /// Get the instructions within the function body.
    fn instructions(&self) -> &IndexVec<LabelOffset, Instruction>;
}

pub struct BytecodePrettyPrinter<'a, F: FunctionBody> {
    body: &'a F,
}

impl<'a, F: FunctionBody> BytecodePrettyPrinter<'a, F> {
    /// Create a new [BytecodePrettyPrinter] for the given function body.
    pub fn new(body: &'a F) -> Self {
        Self { body }
    }
}

impl<F: FunctionBody> fmt::Display for BytecodePrettyPrinter<'_, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut counter = 0;
        let mut label_counter: usize = 0;

        // @Todo: print some kind of header information for the function, or maybe
        // support a way to add some kind of annotations to the specific
        // instructions.

        // iterate over the labels in windows, that should give us the start and end of
        // each label range
        for window in self.body.labels().windows(2) {
            let (start, end) = (window[0], window[1]);

            // print the label with indentation matching instruction format
            writeln!(f, "{:>4}:", format!("${}", label_counter))?;
            label_counter += 1;

            // now write the instructions under this label:
            for instruction in self.body.instructions()[start..end].iter() {
                Self::write_instruction(f, counter, instruction)?;
                counter += 1;
            }
        }

        // we need to print the remaining instructions after the last label
        if let Some(last_label) = self.body.labels().last() {
            writeln!(f, "{:>4}:", format!("${}", label_counter))?;

            for instruction in self.body.instructions()[*last_label..].iter() {
                Self::write_instruction(f, counter, instruction)?;
                counter += 1;
            }
        }

        Ok(())
    }
}

impl<F: FunctionBody> BytecodePrettyPrinter<'_, F> {
    /// Write a single instruction with proper alignment.
    fn write_instruction(
        f: &mut fmt::Formatter<'_>,
        counter: usize,
        instruction: &Instruction,
    ) -> fmt::Result {
        // Convert the instruction to a string and split it into name and operands
        let instruction_str = instruction.to_string();

        if let Some((name, operands)) = instruction_str.split_once(' ') {
            // Instruction has operands - align them
            writeln!(f, "{:04}: {:>7} {}", counter, name, operands)?;
        } else {
            // Instruction has no operands (e.g., "return")
            writeln!(f, "{:04}: {:>7}", counter, instruction_str)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use hash_utils::index_vec::index_vec;

    use super::*;
    use crate::bytecode::{Instruction, op::Operand, register::Register};

    // Test implementation of FunctionBody
    struct TestFunctionBody {
        labels: IndexVec<LabelOffset, LabelOffset>,
        instructions: IndexVec<LabelOffset, Instruction>,
    }

    impl FunctionBody for TestFunctionBody {
        fn labels(&self) -> &IndexVec<LabelOffset, LabelOffset> {
            &self.labels
        }

        fn instructions(&self) -> &IndexVec<LabelOffset, Instruction> {
            &self.instructions
        }
    }

    #[test]
    fn test_bytecode_pretty_printer_formatting() {
        // Create a test function body with multiple labels and instructions
        let test_body = TestFunctionBody {
            // Labels at positions 0, 4, 6
            labels: index_vec![LabelOffset::new(0), LabelOffset::new(4), LabelOffset::new(6),],
            // Instructions matching the test case
            instructions: index_vec![
                Instruction::Write32 { op: Operand::Register(Register::new(0)), value: 10 },
                Instruction::Write32 { op: Operand::Register(Register::new(1)), value: 20 },
                Instruction::Add32 { l1: Register::new(0), l2: Register::new(1) },
                Instruction::JmpPos {
                    l1: Register::new(0),
                    location: Operand::Label(LabelOffset::new(2))
                },
                Instruction::Write32 { op: Operand::Register(Register::new(0)), value: 0 },
                Instruction::Return,
                Instruction::Write32 { op: Operand::Register(Register::new(0)), value: 1 },
                Instruction::Return,
            ],
        };

        let output = format!("{}", BytecodePrettyPrinter::new(&test_body));

        // Verify the output has the expected format
        assert!(output.contains("$0:"), "Output should contain label $0");
        assert!(output.contains("$1:"), "Output should contain label $1");
        assert!(output.contains("$2:"), "Output should contain label $2");

        // Verify instructions are formatted with proper alignment
        assert!(output.contains("0000:"), "Output should start with instruction 0000");
        assert!(output.contains("write32"), "Output should contain write32 instruction");
        assert!(output.contains("add32"), "Output should contain add32 instruction");
        assert!(output.contains("jp"), "Output should contain jp (jump positive) instruction");
        assert!(output.contains("return"), "Output should contain return instruction");

        // Print for visual inspection during test runs with --nocapture
        println!("Bytecode Pretty Printer Output:\n{}", output);
    }
}
