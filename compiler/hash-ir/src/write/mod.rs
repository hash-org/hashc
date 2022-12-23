//! Hash IR writing utilities. This module contains functionality
//! for printing out the IR in a human readable format. The format
//! is similar to the format used by the Rust compiler. Each IR Body
//! is printed out as a function, the body of the function shows
//! all of the declarations made by the body, followed by all of
//! the basic blocks that are used within the function body definition.

pub mod graphviz;
pub mod pretty;

use std::fmt;

use hash_utils::store::{SequenceStore, Store};

use super::ir::*;
use crate::{
    ty::{AdtId, IrTyId, IrTyListId},
    IrStorage,
};

/// Struct that is used to write [IrTy]s.
pub struct ForFormatting<'ir, T> {
    /// The item that is being printed.
    pub item: T,

    /// Whether the formatting should be verbose or not.
    pub verbose: bool,

    /// Whether the formatting implementations should write
    /// edges for IR items, this mostly applies to [Terminator]s.
    pub with_edges: bool,

    /// The storage used to print various IR constructs.
    pub storage: &'ir IrStorage,
}

pub trait WriteIr: Sized {
    fn for_fmt(self, storage: &IrStorage) -> ForFormatting<Self> {
        ForFormatting { item: self, storage, verbose: false, with_edges: true }
    }

    fn fmt_with_opts(
        self,
        storage: &IrStorage,
        verbose: bool,
        with_edges: bool,
    ) -> ForFormatting<Self> {
        ForFormatting { item: self, storage, verbose, with_edges }
    }
}

impl WriteIr for IrTyId {}
impl WriteIr for IrTyListId {}
impl WriteIr for AdtId {}

impl WriteIr for Place {}

impl fmt::Display for ForFormatting<'_, Place> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.storage.projections().map_fast(self.item.projections, |projections| {
            // First we, need to deal with the `deref` projections, since
            // they need to be printed in reverse
            for projection in projections.iter().rev() {
                match projection {
                    PlaceProjection::Downcast(_) | PlaceProjection::Field(_) => write!(f, "(")?,
                    PlaceProjection::Deref => write!(f, "(*")?,
                    PlaceProjection::SubSlice { .. }
                    | PlaceProjection::ConstantIndex { .. }
                    | PlaceProjection::Index(_) => {}
                }
            }

            write!(f, "{:?}", self.item.local)?;

            for projection in projections.iter() {
                match projection {
                    PlaceProjection::Downcast(index) => write!(f, " as variant#{index})")?,
                    PlaceProjection::Index(local) => write!(f, "[{local:?}]")?,
                    PlaceProjection::ConstantIndex { offset, min_length, from_end: true } => {
                        write!(f, "[-{offset:?} of {min_length:?}]")?;
                    }
                    PlaceProjection::ConstantIndex { offset, min_length, from_end: false } => {
                        write!(f, "[{offset:?} of {min_length:?}]")?;
                    }
                    PlaceProjection::SubSlice { from, to, from_end: true } if *to == 0 => {
                        write!(f, "[{from}:]")?;
                    }
                    PlaceProjection::SubSlice { from, to, from_end: false } if *from == 0 => {
                        write!(f, "[:-{to:?}]")?;
                    }
                    PlaceProjection::SubSlice { from, to, from_end: true } => {
                        write!(f, "[{from}:-{to:?}]")?;
                    }
                    PlaceProjection::SubSlice { from, to, from_end: false } => {
                        write!(f, "[{from:?}:{to:?}]")?;
                    }
                    PlaceProjection::Field(index) => write!(f, ".{index})")?,
                    PlaceProjection::Deref => write!(f, ")")?,
                }
            }

            Ok(())
        })
    }
}

impl WriteIr for Operand {}

impl fmt::Display for ForFormatting<'_, Operand> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.item {
            Operand::Place(place) => write!(f, "{}", place.for_fmt(self.storage)),
            Operand::Const(ConstKind::Value(Const::Zero(ty))) => {
                write!(f, "{}", ty.for_fmt(self.storage))
            }
            Operand::Const(const_value) => write!(f, "const {const_value}"),
        }
    }
}

impl WriteIr for &RValue {}

impl fmt::Display for ForFormatting<'_, &RValue> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.item {
            RValue::Use(operand) => write!(f, "{}", operand.for_fmt(self.storage)),
            RValue::BinaryOp(op, operands) => {
                let (lhs, rhs) = operands.as_ref();

                write!(f, "{op:?}({}, {})", lhs.for_fmt(self.storage), rhs.for_fmt(self.storage))
            }
            RValue::CheckedBinaryOp(op, operands) => {
                let (lhs, rhs) = operands.as_ref();

                write!(
                    f,
                    "Checked{op:?}({}, {})",
                    lhs.for_fmt(self.storage),
                    rhs.for_fmt(self.storage)
                )
            }
            RValue::Len(place) => write!(f, "len({})", place.for_fmt(self.storage)),
            RValue::UnaryOp(op, operand) => {
                write!(f, "{op:?}({})", operand.for_fmt(self.storage))
            }
            RValue::ConstOp(op, operand) => write!(f, "{op:?}({operand:?})"),
            RValue::Discriminant(place) => {
                write!(f, "discriminant({})", place.for_fmt(self.storage))
            }
            RValue::Ref(region, borrow_kind, place) => {
                write!(f, "&{region:?} {borrow_kind:?} {place:?}")
            }
            RValue::Aggregate(aggregate_kind, operands) => {
                let fmt_operands = |f: &mut fmt::Formatter, start: char, end: char| {
                    write!(f, "{start}")?;

                    for (i, operand) in operands.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", operand.for_fmt(self.storage))?;
                    }

                    write!(f, "{end}")
                };

                match aggregate_kind {
                    AggregateKind::Tuple => fmt_operands(f, '(', ')'),
                    AggregateKind::Array(_) => fmt_operands(f, '[', ']'),
                    AggregateKind::Enum(adt, index) => {
                        self.storage.adts().map_fast(*adt, |def| {
                            let name = def.variants.get(*index).unwrap().name;

                            write!(f, "{}::{name}", adt.for_fmt(self.storage))
                        })?;

                        fmt_operands(f, '(', ')')
                    }
                    AggregateKind::Struct(adt) => {
                        write!(f, "{}", adt.for_fmt(self.storage))?;
                        fmt_operands(f, '(', ')')
                    }
                }
            }
        }
    }
}

impl WriteIr for &Statement {}

impl fmt::Display for ForFormatting<'_, &Statement> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.item.kind {
            StatementKind::Nop => write!(f, "nop"),
            StatementKind::Assign(place, value) => {
                write!(f, "{} = {}", place.for_fmt(self.storage), value.for_fmt(self.storage))
            }
            StatementKind::Discriminate(place, index) => {
                write!(f, "discriminant({}) = {index}", place.for_fmt(self.storage))
            }
            // @@Todo: figure out format for printing out the allocations that
            // are made.
            StatementKind::Alloc(_) => todo!(),
            StatementKind::AllocRaw(_) => todo!(),
        }
    }
}

impl WriteIr for &Terminator {}

impl fmt::Display for ForFormatting<'_, &Terminator> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.item.kind {
            TerminatorKind::Goto(place) if self.with_edges => write!(f, "goto -> {place:?}"),
            TerminatorKind::Goto(_) => write!(f, "goto"),
            TerminatorKind::Return => write!(f, "return"),
            TerminatorKind::Call { op, args, target, destination } => {
                write!(f, "{} = {}(", destination.for_fmt(self.storage), op.for_fmt(self.storage))?;

                // write all of the arguments
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", arg.for_fmt(self.storage))?;
                }

                // Only print the target if there is a target, and if the formatting
                // specifies that edges should be printed.
                if let Some(target) = target && self.with_edges {
                    write!(f, ") -> {target:?}")
                } else {
                    write!(f, ")")
                }
            }
            TerminatorKind::Unreachable => write!(f, "unreachable"),
            TerminatorKind::Switch { value, targets } => {
                write!(f, "switch({})", value.for_fmt(self.storage))?;

                if self.with_edges {
                    write!(f, " [")?;

                    // Iterate over each value in the table, and add a arrow denoting
                    // that the CF will go to the specified block given the specified
                    // `value`.
                    for (i, (value, target)) in targets.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }

                        // We want to create an a constant from this value
                        // with the type, and then print it.
                        let value = Const::from_scalar(value, targets.ty, self.storage);

                        write!(f, "{value} -> {target:?}")?;
                    }

                    // Write the default case
                    if let Some(otherwise) = targets.otherwise {
                        write!(f, ", otherwise -> {otherwise:?}]")?;
                    }
                }

                Ok(())
            }
            TerminatorKind::Assert { condition, expected, kind, target } => {
                write!(f, "assert({}, {expected:?}, {kind:?})", condition.for_fmt(self.storage))?;

                if self.with_edges {
                    write!(f, " -> {target:?}")?;
                }

                Ok(())
            }
        }
    }
}
