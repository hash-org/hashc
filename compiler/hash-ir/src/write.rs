//! Hash IR writing utilities. This module contains functionality
//! for printing out the IR in a human readable format. The format
//! is similar to the format used by the Rust compiler. Each IR Body
//! is printed out as a function, the body of the function shows
//! all of the declarations made by the body, followed by all of
//! the basic blocks that are used within the function body definition.

use std::fmt;

use hash_utils::store::CloneStore;

use super::ir::*;
use crate::{
    ty::{AdtId, IrTyId, IrTyListId},
    IrStorage,
};

/// Struct that is used to write [IrTy]s.
pub struct ForFormatting<'ir, T> {
    pub t: T,
    pub storage: &'ir IrStorage,
}

pub trait WriteTyIr: Sized {
    fn for_fmt(self, storage: &IrStorage) -> ForFormatting<Self> {
        ForFormatting { t: self, storage }
    }
}

impl WriteTyIr for IrTyId {}
impl WriteTyIr for IrTyListId {}
impl WriteTyIr for AdtId {}

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
    fn write_rvalue(&self, value: RValueId, f: &mut fmt::Formatter) -> fmt::Result;
}

pub struct IrWriter<'ir> {
    /// The type context allowing for printing any additional
    /// metadata about types within the ir.
    ctx: &'ir IrStorage,
    /// The body that is being printed
    body: &'ir Body,
}

impl<'ir> IrWriter<'ir> {
    /// Create a new IR writer for the given body.
    pub fn new(ctx: &'ir IrStorage, body: &'ir Body) -> Self {
        Self { ctx, body }
    }
}

impl fmt::Display for IrWriter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.write_body(f)
    }
}

impl<'ir> WriteIr<'ir> for IrWriter<'ir> {
    fn write_body(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.body.name)?;

        let mut declarations = self.body.declarations.iter();

        // return_type declaration, this is always located at `0`
        let return_ty_decl = declarations.next().unwrap();

        for (i, param) in declarations.take(self.body.arg_count).enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            // We add 1 to the index because the return type is always
            // located at `0`.
            write!(f, "_{}: {}", i + 1, param.ty().for_fmt(self.ctx))?;
        }
        writeln!(f, ") -> {} {{", return_ty_decl.ty().for_fmt(self.ctx))?;

        // Print all of the declarations within the function
        writeln!(
            f,
            "    {}_0: {};",
            return_ty_decl.mutability(),
            return_ty_decl.ty().for_fmt(self.ctx)
        )?;

        let declarations = self.body.declarations.iter_enumerated();
        let offset = 1 + self.body.arg_count;

        for (local, decl) in declarations.skip(offset) {
            writeln!(f, "    {}{local:?}:{};", decl.mutability(), decl.ty().for_fmt(self.ctx))?;
        }

        // Print all of the basic blocks
        for (bb, _) in self.body.blocks.iter_enumerated() {
            writeln!(f)?;
            self.write_block(bb, f)?;
        }

        writeln!(f, "}}")
    }

    fn write_block(&self, block: BasicBlock, f: &mut fmt::Formatter) -> fmt::Result {
        // Print the label for the block
        writeln!(f, "{: <1$}{block:?} {{", "", 4)?;
        let block_data = &self.body.blocks[block];

        // Write all of the statements within the block
        for statement in &block_data.statements {
            self.write_statement(statement, f)?;
        }

        // Write the terminator of the block. If the terminator is
        // not present, this is an invariant but we don't care here.
        if let Some(terminator) = &block_data.terminator {
            self.write_terminator(terminator, f)?;
        }

        writeln!(f, "{: <1$}}}", "", 4)
    }

    fn write_statement(&self, statement: &'ir Statement, f: &mut fmt::Formatter) -> fmt::Result {
        // always write the indent
        write!(f, "{: <1$}", "", 8)?;

        match &statement.kind {
            StatementKind::Nop => write!(f, "nop;"),
            StatementKind::Assign(place, value) => {
                write!(f, "{place} = ")?;
                self.write_rvalue(*value, f)?;
                writeln!(f, ";")
            }

            // @@Todo: figure out format for printing out the allocations that
            // are made.
            StatementKind::Alloc(_) => todo!(),
            StatementKind::AllocRaw(_) => todo!(),
        }
    }

    fn write_rvalue(&self, value: RValueId, f: &mut fmt::Formatter) -> fmt::Result {
        let rvalue = self.ctx.rvalue_store().get(value);

        match rvalue {
            RValue::Use(place) => write!(f, "{place}"),
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
        write!(f, "{: <1$}", "", 8)?;

        match &terminator.kind {
            TerminatorKind::Goto(place) => writeln!(f, "goto -> {place:?};"),
            TerminatorKind::Return => writeln!(f, "return;"),
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

                writeln!(f, ") -> {target:?};")
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

                writeln!(f, "otherwise -> {otherwise:?}];")
            }
            TerminatorKind::Assert { condition, expected, kind, target } => {
                writeln!(f, "assert({condition:?}, {expected:?}, {kind:?}) -> {target:?};")
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
