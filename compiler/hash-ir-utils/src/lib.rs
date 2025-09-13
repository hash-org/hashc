//! Various utilities that are useful for operating on the Hash IR.
//!
//! This crate primarily depends because of the issue of Rust not allowing
//! crate dependencies to be cyclic.
//!
//! One of the main uses of this crate uses `hash-layout` to provide needed
//! information about data representation when constructing and destructing
//! Hash IR constants into various representations.
pub mod graphviz;
pub mod pretty;

use std::{fmt, ops::Deref};

use hash_const_eval::print::ConstWriter;
use hash_ir::{
    ir::{
        AggregateKind, AssertKind, BodyInfo, Operand, Place, PlaceProjection, RValue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::Mutability,
};
use hash_repr::{compute::LayoutComputer, constant::Const};
use hash_storage::store::statics::StoreId;
use hash_target::data_layout::HasDataLayout;

/// Struct that is used to write interned IR components.
pub struct IrWriter<'ctx, T> {
    /// The item that is being printed.
    pub item: T,

    /// The layout computer is used to compute the layout of the data
    /// under the constant.
    pub lc: LayoutComputer<'ctx>,

    /// The overall [Body] to which the IR belongs to.
    pub info: BodyInfo<'ctx>,

    /// Whether the formatting implementations should write
    /// edges for IR items, this mostly applies to [Terminator]s.
    pub with_edges: bool,
}

impl<'ctx, T> IrWriter<'ctx, T> {
    /// Create a new IR writer for the given body.
    pub fn new(item: T, info: BodyInfo<'ctx>, lc: LayoutComputer<'ctx>) -> Self {
        Self { item, lc, info, with_edges: false }
    }
}

impl<'ctx, T> From<&'ctx IrWriter<'ctx, T>> for LayoutComputer<'ctx> {
    fn from(value: &'ctx IrWriter<'ctx, T>) -> Self {
        value.lc
    }
}

impl<T> Deref for IrWriter<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

pub trait WriteIr<'ctx>: Sized {
    #[inline]
    fn with_edges(
        self,
        info: BodyInfo<'ctx>,
        lc: LayoutComputer<'ctx>,
        with_edges: bool,
    ) -> IrWriter<'ctx, Self> {
        IrWriter { item: self, info, lc, with_edges }
    }

    fn with<U>(self, other: &IrWriter<'ctx, U>) -> IrWriter<'ctx, Self> {
        IrWriter::new(self, other.info, other.lc)
    }
}

impl WriteIr<'_> for &Place {}
impl fmt::Display for IrWriter<'_, &Place> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (local, projections) = (self.item.local, self.item.projections);

        // First we, need to deal with the `deref` projections, since
        // they need to be printed in reverse
        for projection in self.info.projections.borrow(projections).iter().rev() {
            match projection {
                PlaceProjection::Downcast(_) | PlaceProjection::Field(_) => write!(f, "(")?,
                PlaceProjection::Deref => write!(f, "(*")?,
                PlaceProjection::SubSlice { .. }
                | PlaceProjection::ConstantIndex { .. }
                | PlaceProjection::Index(_) => {}
            }
        }

        write!(f, "{:?}", local)?;

        for projection in self.info.projections.borrow(projections) {
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

impl WriteIr<'_> for &Operand {}
impl fmt::Display for IrWriter<'_, &Operand> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.item {
            Operand::Place(place) => write!(f, "{}", place.with(self)),
            Operand::Const(constant) => {
                if !constant.is_zero() {
                    write!(f, "const ")?;
                }

                write!(f, "{}", ConstWriter::new(constant, self.lc))
            }
        }
    }
}

impl WriteIr<'_> for &RValue {}
impl fmt::Display for IrWriter<'_, &RValue> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.item {
            RValue::Use(operand) => write!(f, "{}", operand.with(self)),
            RValue::BinaryOp(op, operands) => {
                let (lhs, rhs) = operands.as_ref();

                write!(f, "{op:?}({}, {})", lhs.with(self), rhs.with(self))
            }
            RValue::CheckedBinaryOp(op, operands) => {
                let (lhs, rhs) = operands.as_ref();

                write!(f, "Checked{op:?}({}, {})", lhs.with(self), rhs.with(self))
            }
            RValue::Len(place) => write!(f, "len({})", place.with(self)),
            RValue::Cast(_, op, ty) => {
                // We write out the type fully for the cast.
                write!(f, "cast({}, {})", ty, op.with(self))
            }
            RValue::UnaryOp(op, operand) => {
                write!(f, "{op:?}({})", operand.with(self))
            }
            RValue::ConstOp(op, operand) => write!(f, "{op:?}({operand:?})"),
            RValue::Discriminant(place) => {
                write!(f, "discriminant({})", place.with(self))
            }
            RValue::Ref(mutability, place, kind) => match mutability {
                Mutability::Mutable => write!(f, "&mut {kind}{}", place.with(self)),
                Mutability::Immutable => write!(f, "&{kind}{}", place.with(self)),
            },
            RValue::Aggregate(aggregate_kind, operands) => {
                let fmt_operands = |f: &mut fmt::Formatter, start: char, end: char| {
                    write!(f, "{start}")?;

                    for (i, operand) in operands.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", operand.with(self))?;
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
            RValue::Repeat(op, repeat) => {
                write!(f, "[{}; {}]", op.with(self), repeat)
            }
        }
    }
}

impl WriteIr<'_> for &Statement {}
impl fmt::Display for IrWriter<'_, &Statement> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StatementKind::Nop => write!(f, "nop"),
            StatementKind::Assign(place, value) => {
                write!(f, "{} = {}", place.with(self), value.with(self))
            }
            StatementKind::Discriminate(place, index) => {
                write!(f, "discriminant({}) = {index}", place.with(self))
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

impl WriteIr<'_> for &Terminator {}
impl fmt::Display for IrWriter<'_, &Terminator> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.item.kind {
            TerminatorKind::Goto(place) if self.with_edges => write!(f, "goto -> {place:?}"),
            TerminatorKind::Goto(_) => write!(f, "goto"),
            TerminatorKind::Return => write!(f, "return"),
            TerminatorKind::Call { op, args, target, destination } => {
                write!(f, "{} = {}(", destination.with(self), op.with(self))?;

                // write all of the arguments
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", arg.with(self))?;
                }

                // Only print the target if there is a target, and if the formatting
                // specifies that edges should be printed.
                if let Some(target) = target
                    && self.with_edges
                {
                    write!(f, ") -> {target:?}")
                } else {
                    write!(f, ")")
                }
            }
            TerminatorKind::Unreachable => write!(f, "unreachable"),
            TerminatorKind::Switch { value, targets } => {
                write!(f, "switch({})", value.with(self))?;

                if self.with_edges {
                    write!(f, " [")?;

                    let target_ty = value.ty(&self.info);

                    // Iterate over each value in the table, and add a arrow denoting
                    // that the CF will go to the specified block given the specified
                    // `value`.
                    for (i, (value, target)) in targets.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }

                        // We want to create an a constant from this value
                        // with the type, and then print it.
                        let value =
                            Const::from_scalar_like(value, target_ty, self.lc.data_layout());

                        write!(f, "{} -> {target:?}", ConstWriter::new(&value, self.lc))?;
                    }

                    // Write the default case
                    if let Some(otherwise) = targets.otherwise {
                        write!(f, ", otherwise -> {otherwise:?}]")?;
                    }
                }

                Ok(())
            }
            TerminatorKind::Assert { condition, expected, kind, target } => {
                write!(
                    f,
                    "assert({}, {expected:?}, \"{}\")",
                    condition.with(self),
                    kind.with(self)
                )?;

                if self.with_edges {
                    write!(f, " -> {target:?}")?;
                }

                Ok(())
            }
        }
    }
}

impl WriteIr<'_> for &AssertKind {}
impl fmt::Display for IrWriter<'_, &AssertKind> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.item {
            AssertKind::DivisionByZero { operand } => {
                write!(f, "attempt to divide `{}` by zero", operand.with(self))
            }
            AssertKind::RemainderByZero { operand } => {
                write!(f, "attempt to take the remainder of `{}` by zero", operand.with(self))
            }
            AssertKind::Overflow { op, lhs, rhs } => {
                write!(
                    f,
                    "attempt to compute `{} {op} {}`, which would overflow",
                    lhs.with(self),
                    rhs.with(self)
                )
            }
            AssertKind::NegativeOverflow { operand } => {
                write!(f, "attempt to negate `{}`, which would overflow", operand.with(self))
            }
            AssertKind::BoundsCheck { len, index } => {
                write!(
                    f,
                    "index out of bounds: the length is `{}` but index is `{}`",
                    len.with(self),
                    index.with(self)
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use hash_ir::{
        ir::{BodyInfo, Local, LocalDecls, Place, PlaceProjection, Projections},
        ty::VariantIdx,
    };
    use hash_repr::{LayoutStorage, compute::LayoutComputer};
    use hash_target::data_layout::TargetDataLayout;

    use crate::IrWriter;

    #[test]
    fn test_place_display() {
        let lcx = LayoutStorage::new(TargetDataLayout::default());
        let lc = LayoutComputer::new(&lcx);
        let mut projections = Projections::new();
        let locals = LocalDecls::new();

        let place = Place {
            local: Local::new(0),
            projections: projections.create_from_slice(&[
                PlaceProjection::Deref,
                PlaceProjection::Field(0),
                PlaceProjection::Index(Local::new(1)),
                PlaceProjection::Downcast(VariantIdx::from_usize(0)),
            ]),
        };

        let info = BodyInfo { locals: &locals, projections: &projections };
        let item = IrWriter::new(&place, info, lc);
        assert_eq!(format!("{}", item), "(((*_0).0)[_1] as variant#0)");

        let place = Place {
            local: Local::new(0),
            projections: projections.create_from_slice(&[
                PlaceProjection::Deref,
                PlaceProjection::Deref,
                PlaceProjection::Deref,
            ]),
        };

        let info = BodyInfo { locals: &locals, projections: &projections };
        let item = IrWriter::new(&place, info, lc);
        assert_eq!(format!("{}", item), "(*(*(*_0)))");
    }
}
