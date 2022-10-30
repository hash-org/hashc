//! Hash IR writing utilities. This module contains functionality
//! for printing out the IR in a human readable format. The format
//! is similar to the format used by the Rust compiler. Each IR Body
//! is printed out as a function, the body of the function shows
//! all of the declarations made by the body, followed by all of
//! the basic blocks that are used within the function body definition.

use std::fmt;

use hash_types::{fmt::PrepareForFormatting, storage::GlobalStorage};

use super::ir::*;

/// A trait for printing out the IR in a human readable format.
pub trait WriteIr<'ir> {
    /// Write an IR [Body] to the given formatter.
    fn write_body(&self, f: &mut fmt::Formatter) -> fmt::Result;

    /// Write an IR [Block] to the given formatter.
    fn write_block(&self, block: BasicBlock, f: &mut fmt::Formatter) -> fmt::Result;

    /// Write an IR [Statement] to the given formatter.
    fn write_statement(&self, statement: &'ir Statement, f: &mut fmt::Formatter) -> fmt::Result;

    /// Write a IR [Terminator] to the given formatter.
    fn write_terminator(&self, terminator: &'ir Terminator, f: &mut fmt::Formatter) -> fmt::Result;

    /// Write an IR [RValue] to the given formatter.
    fn write_rvalue(&self, value: &'ir RValue, f: &mut fmt::Formatter) -> fmt::Result;
}

pub struct IrWriter<'ir> {
    /// The type context allowing for printing any additional
    /// metadata about types within the ir.
    tcx: &'ir GlobalStorage,
    /// The body that is being printed
    body: &'ir Body<'ir>,
}

impl<'ir> IrWriter<'ir> {
    /// Create a new IR writer for the given body.
    pub fn new(tcx: &'ir GlobalStorage, body: &'ir Body<'ir>) -> Self {
        Self { tcx, body }
    }
}

impl<'ir> WriteIr<'ir> for IrWriter<'ir> {
    fn write_body(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}(", self.body.name)?;

        let mut declarations = self.body.declarations.iter();

        // return_type declaration, this is always located at `0`
        let return_ty_decl = declarations.next().unwrap();

        for (i, param) in declarations.take(self.body.arg_count).enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            write!(f, "_{i}: {}", param.ty().for_formatting(self.tcx))?;
        }
        writeln!(f, ") -> {} {{", return_ty_decl.ty().for_formatting(self.tcx))?;

        // Print all of the declarations within the function
        writeln!(f, "_0: {}", return_ty_decl.ty().for_formatting(self.tcx))?;

        let declarations = self.body.declarations.iter_enumerated();
        let offset = 1 + self.body.arg_count;

        for (local, decl) in declarations.skip(offset) {
            writeln!(f, "    {local:?}:{}", decl.ty().for_formatting(self.tcx))?;
        }

        // Print all of the basic blocks
        for (bb, _) in self.body.blocks.iter_enumerated() {
            self.write_block(bb, f)?;

            // add a space if it is not the last time
            if bb.index() < self.body.blocks.len() - 1 {
                writeln!(f)?;
            }
        }

        writeln!(f, "}}")
    }

    fn write_block(&self, block: BasicBlock, f: &mut fmt::Formatter) -> fmt::Result {
        // Print the label for the block
        writeln!(f, "{: <0$}{:?} {{", 4, block)?;
        let block_data = &self.body.blocks[block];

        for statement in &block_data.statements {
            self.write_statement(statement, f)?;
        }

        writeln!(f, "{: <0$}}}", 4)
    }

    fn write_statement(&self, statement: &'ir Statement, f: &mut fmt::Formatter) -> fmt::Result {
        // always write the indent
        write!(f, "{: <0$}", 8)?;

        match &statement.kind {
            StatementKind::Nop => write!(f, "nop;"),
            StatementKind::Assign(place, value) => {
                write!(f, "{place:?} = {value:?};")
            }

            // @@Todo: figure out format for printing out the allocations that
            // are made.
            StatementKind::Alloc(_) => todo!(),
            StatementKind::AllocRaw(_) => todo!(),
        }
    }

    fn write_rvalue(&self, value: &'ir RValue, f: &mut fmt::Formatter) -> fmt::Result {
        match value {
            RValue::Use(place) => write!(f, "{place:?}"),
            RValue::Const(operand) => write!(f, "const {operand:?}"),
            RValue::BinaryOp(op, lhs, rhs) => write!(f, "{lhs:?} {op:?} {rhs:?}"),
            RValue::UnaryOp(op, operand) => write!(f, "{op:?}({operand:?})"),
            RValue::ConstOp(op, operand) => write!(f, "{op:?}({operand:?})"),
            RValue::Discriminant(place) => write!(f, "discriminant({place:?})"),
            RValue::Ref(region, borrow_kind, place) => {
                write!(f, "&{region:?} {borrow_kind:?} {place:?}")
            }
            RValue::Aggregate(aggregate_kind, operands) => {
                write!(f, "{aggregate_kind:?}({operands:?})")
            }
        }
    }

    fn write_terminator(&self, terminator: &'ir Terminator, f: &mut fmt::Formatter) -> fmt::Result {
        // always write the indent
        write!(f, "{: <0$}", 8)?;

        match &terminator.kind {
            TerminatorKind::Goto(place) => write!(f, "goto -> {place:?};"),
            TerminatorKind::Return => write!(f, "return;"),
            TerminatorKind::Call { op, args, target } => {
                write!(f, "{op:?}(")?;

                // write all of the arguments
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }

                    // @@Todo: should we write the type of the operand here?
                    write!(f, "{arg:?}")?;
                }

                write!(f, ") -> {target:?};")
            }
            TerminatorKind::Unreachable => write!(f, "unreachable;"),
            TerminatorKind::Switch(value, branches, otherwise) => {
                write!(f, "switch({value:?}) -> [")?;

                for (i, (value, target)) in branches.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{value:?} -> {target:?}")?;
                }

                write!(f, "otherwise -> {otherwise:?}];")
            }
            TerminatorKind::Assert { condition, expected, kind, target } => {
                write!(f, "assert({condition:?}, {expected:?}, {kind:?}) -> {target:?};")
            }
        }
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // First we, need to deal with the `deref` projections, since
        // they need to be printed in reverse
        for projection in self.projections.iter().rev() {
            match projection {
                PlaceProjection::Downcast(_) | PlaceProjection::Field(_) => write!(f, "(")?,
                PlaceProjection::Deref => write!(f, "(*")?,
                PlaceProjection::Index(_) => {}
            }
        }

        write!(f, "{:?}", self.local)?;

        for projection in &self.projections {
            match projection {
                PlaceProjection::Downcast(index) => write!(f, " as variant#{index})")?,
                PlaceProjection::Index(local) => write!(f, "[{local:?}]")?,
                PlaceProjection::Field(index) => write!(f, ".{index})")?,
                PlaceProjection::Deref => write!(f, ")")?,
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::ir::*;

    #[test]
    fn test_place_display() {
        let place = Place {
            local: Local::new(0),
            projections: vec![
                PlaceProjection::Deref,
                PlaceProjection::Field(0),
                PlaceProjection::Index(Local::new(1)),
                PlaceProjection::Downcast(0),
            ],
        };

        assert_eq!(format!("{place}"), "(((*_0).0)[_1] as variant#0)");

        let place = Place {
            local: Local::new(0),
            projections: vec![
                PlaceProjection::Deref,
                PlaceProjection::Deref,
                PlaceProjection::Deref,
            ],
        };

        assert_eq!(format!("{place}"), "(*(*(*_0)))");
    }
}
