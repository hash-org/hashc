//! Contains various mappings and conversions between the generic code
//! generation types and the LLVM backend specific data types.

use hash_codegen::common::{AtomicOrdering, IntComparisonKind, RealComparisonKind};
use hash_target::abi::AddressSpace;

/// Wrapper type around [inkwell::IntPredicate] to allow for conversion from
/// [IntComparisonKind].
pub struct IntPredicateWrapper(pub inkwell::IntPredicate);

impl From<IntComparisonKind> for IntPredicateWrapper {
    fn from(value: IntComparisonKind) -> Self {
        match value {
            IntComparisonKind::Eq => Self(inkwell::IntPredicate::EQ),
            IntComparisonKind::Ne => Self(inkwell::IntPredicate::NE),
            IntComparisonKind::Ugt => Self(inkwell::IntPredicate::UGT),
            IntComparisonKind::Uge => Self(inkwell::IntPredicate::UGE),
            IntComparisonKind::Ult => Self(inkwell::IntPredicate::ULT),
            IntComparisonKind::Ule => Self(inkwell::IntPredicate::ULE),
            IntComparisonKind::Sgt => Self(inkwell::IntPredicate::SGT),
            IntComparisonKind::Sge => Self(inkwell::IntPredicate::SGE),
            IntComparisonKind::Slt => Self(inkwell::IntPredicate::SLT),
            IntComparisonKind::Sle => Self(inkwell::IntPredicate::SLE),
        }
    }
}

/// Wrapper type around [inkwell::FloatPredicate] to allow for conversion from
/// [RealComparisonKind].
pub struct FloatPredicateWrapper(pub inkwell::FloatPredicate);

impl From<RealComparisonKind> for FloatPredicateWrapper {
    fn from(value: RealComparisonKind) -> Self {
        match value {
            RealComparisonKind::False => Self(inkwell::FloatPredicate::PredicateFalse),
            RealComparisonKind::Oeq => Self(inkwell::FloatPredicate::OEQ),
            RealComparisonKind::Ogt => Self(inkwell::FloatPredicate::OGT),
            RealComparisonKind::Oge => Self(inkwell::FloatPredicate::OGE),
            RealComparisonKind::Olt => Self(inkwell::FloatPredicate::OLT),
            RealComparisonKind::Ole => Self(inkwell::FloatPredicate::OLE),
            RealComparisonKind::One => Self(inkwell::FloatPredicate::ONE),
            RealComparisonKind::Ord => Self(inkwell::FloatPredicate::ORD),
            RealComparisonKind::Uno => Self(inkwell::FloatPredicate::UNO),
            RealComparisonKind::Ueq => Self(inkwell::FloatPredicate::UEQ),
            RealComparisonKind::Ugt => Self(inkwell::FloatPredicate::UGT),
            RealComparisonKind::Uge => Self(inkwell::FloatPredicate::UGE),
            RealComparisonKind::Ult => Self(inkwell::FloatPredicate::ULT),
            RealComparisonKind::Ule => Self(inkwell::FloatPredicate::ULE),
            RealComparisonKind::Une => Self(inkwell::FloatPredicate::UNE),
            RealComparisonKind::True => Self(inkwell::FloatPredicate::PredicateTrue),
        }
    }
}

/// Wrapper type around [inkwell::AtomicOrdering] to allow for conversion from
/// [AtomicOrdering].
pub struct AtomicOrderingWrapper(pub inkwell::AtomicOrdering);

impl From<AtomicOrdering> for AtomicOrderingWrapper {
    fn from(value: AtomicOrdering) -> Self {
        match value {
            AtomicOrdering::NotAtomic => Self(inkwell::AtomicOrdering::NotAtomic),
            AtomicOrdering::Unordered => Self(inkwell::AtomicOrdering::Unordered),
            AtomicOrdering::Monotonic => Self(inkwell::AtomicOrdering::Monotonic),
            AtomicOrdering::Acquire => Self(inkwell::AtomicOrdering::Acquire),
            AtomicOrdering::Release => Self(inkwell::AtomicOrdering::Release),
            AtomicOrdering::AcquireRelease => Self(inkwell::AtomicOrdering::AcquireRelease),
            AtomicOrdering::SequentiallyConsistent => {
                Self(inkwell::AtomicOrdering::SequentiallyConsistent)
            }
        }
    }
}

pub struct AddressSpaceWrapper(pub inkwell::AddressSpace);

impl From<AddressSpace> for AddressSpaceWrapper {
    fn from(value: AddressSpace) -> Self {
        AddressSpaceWrapper(inkwell::AddressSpace::try_from(value.0).unwrap())
    }
}

/// This defines the ids for the various `MetadataKind`s that are used in LLVM
/// to annotate values with particular properties.
///
/// Defined in <https://github.com/llvm-mirror/llvm/blob/master/include/llvm/IR/FixedMetadataKinds.def>
#[derive(Copy, Clone)]
#[repr(C)]
pub enum MetadataTypeKind {
    FpMath = 3,
    Range = 4,
    InvariantLoad = 6,
    AliasScope = 7,
    NoAlias = 8,
    NonTemporal = 9,
    NonNull = 11,
    Align = 17,
    Type = 19,
    NoUndef = 29,
}
