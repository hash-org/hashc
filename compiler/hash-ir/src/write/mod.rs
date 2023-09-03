//! Hash IR writing utilities. This module contains functionality
//! for printing out the IR in a human readable format. The format
//! is similar to the format used by the Rust compiler. Each IR Body
//! is printed out as a function, the body of the function shows
//! all of the declarations made by the body, followed by all of
//! the basic blocks that are used within the function body definition.

pub mod graphviz;
pub mod pretty;

use std::fmt;

use hash_storage::store::statics::StoreId;

use super::ir::*;
use crate::ty::Mutability;

/// Struct that is used to write interned IR components.
pub struct ForFormatting<T> {
    /// The item that is being printed.
    pub item: T,

    /// Whether the formatting implementations should write
    /// edges for IR items, this mostly applies to [Terminator]s.
    pub with_edges: bool,
}

pub trait WriteIr: Sized {
    fn with_edges(self, with_edges: bool) -> ForFormatting<Self> {
        ForFormatting { item: self, with_edges }
    }
}

impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.projections.map(|projections| {
            f.debug_struct("Place")
                .field("local", &self.local)
                .field("projections", &projections)
                .finish()
        })
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // First we, need to deal with the `deref` projections, since
        // they need to be printed in reverse
        for projection in self.projections.borrow().iter().rev() {
            match projection {
                PlaceProjection::Downcast(_) | PlaceProjection::Field(_) => write!(f, "(")?,
                PlaceProjection::Deref => write!(f, "(*")?,
                PlaceProjection::SubSlice { .. }
                | PlaceProjection::ConstantIndex { .. }
                | PlaceProjection::Index(_) => {}
            }
        }

        write!(f, "{:?}", self.local)?;

        for projection in self.projections.borrow().iter() {
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
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Place(place) => write!(f, "{place}"),
            Operand::Const(Const::Zero(ty)) => write!(f, "{ty}"),
            Operand::Const(const_value) => write!(f, "const {const_value}"),
        }
    }
}

impl fmt::Display for &RValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RValue::Use(operand) => write!(f, "{}", operand),
            RValue::BinaryOp(op, operands) => {
                let (lhs, rhs) = operands.as_ref();

                write!(f, "{op:?}({}, {})", lhs, rhs)
            }
            RValue::CheckedBinaryOp(op, operands) => {
                let (lhs, rhs) = operands.as_ref();

                write!(f, "Checked{op:?}({}, {})", lhs, rhs)
            }
            RValue::Len(place) => write!(f, "len({})", place),
            RValue::Cast(_, op, ty) => {
                // We write out the type fully for the cast.
                write!(f, "cast({}, {})", ty, op)
            }
            RValue::UnaryOp(op, operand) => {
                write!(f, "{op:?}({})", operand)
            }
            RValue::ConstOp(op, operand) => write!(f, "{op:?}({operand:?})"),
            RValue::Discriminant(place) => {
                write!(f, "discriminant({})", place)
            }
            RValue::Ref(mutability, place, kind) => match mutability {
                Mutability::Mutable => write!(f, "&mut {kind}{}", place),
                Mutability::Immutable => write!(f, "&{kind}{}", place),
            },
            RValue::Aggregate(aggregate_kind, operands) => {
                let fmt_operands = |f: &mut fmt::Formatter, start: char, end: char| {
                    write!(f, "{start}")?;

                    for (i, operand) in operands.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{operand}")?;
                    }

                    write!(f, "{end}")
                };

                match aggregate_kind {
                    AggregateKind::Tuple(_) => fmt_operands(f, '(', ')'),
                    AggregateKind::Array(_) => fmt_operands(f, '[', ']'),
                    AggregateKind::Enum(adt, index) => {
                        let name = adt.borrow().variants.get(*index).unwrap().name;
                        write!(f, "{}::{name}", adt)?;
                        fmt_operands(f, '(', ')')
                    }
                    AggregateKind::Struct(adt) => {
                        write!(f, "{}", adt)?;
                        fmt_operands(f, '(', ')')
                    }
                }
            }
        }
    }
}

impl fmt::Display for &Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StatementKind::Nop => write!(f, "nop"),
            StatementKind::Assign(place, value) => {
                write!(f, "{} = {}", place, value)
            }
            StatementKind::Discriminate(place, index) => {
                write!(f, "discriminant({}) = {index}", place)
            }
            StatementKind::Live(local) => {
                write!(f, "live({local:?})")
            }
            StatementKind::Dead(local) => {
                write!(f, "dead({local:?})")
            }
        }
    }
}

impl WriteIr for &Terminator {}

impl fmt::Display for ForFormatting<&Terminator> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.item.kind {
            TerminatorKind::Goto(place) if self.with_edges => write!(f, "goto -> {place:?}"),
            TerminatorKind::Goto(_) => write!(f, "goto"),
            TerminatorKind::Return => write!(f, "return"),
            TerminatorKind::Call { op, args, target, destination } => {
                write!(f, "{} = {}(", destination, op)?;

                // write all of the arguments
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{arg}")?;
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
                write!(f, "switch({value})")?;

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
                        let value = Const::from_scalar(value, targets.ty);

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
                write!(f, "assert({condition}, {expected:?}, \"{kind}\")")?;

                if self.with_edges {
                    write!(f, " -> {target:?}")?;
                }

                Ok(())
            }
        }
    }
}

impl fmt::Display for &AssertKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AssertKind::DivisionByZero { operand } => {
                write!(f, "attempt to divide `{operand}` by zero")
            }
            AssertKind::RemainderByZero { operand } => {
                write!(f, "attempt to take the remainder of `{operand}` by zero")
            }
            AssertKind::Overflow { op, lhs, rhs } => {
                write!(f, "attempt to compute `{lhs} {op} {rhs}`, which would overflow",)
            }
            AssertKind::NegativeOverflow { operand } => {
                write!(f, "attempt to negate `{operand}`, which would overflow")
            }
            AssertKind::BoundsCheck { len, index } => {
                write!(f, "index out of bounds: the length is `{len}` but index is `{index}`",)
            }
        }
    }
}
