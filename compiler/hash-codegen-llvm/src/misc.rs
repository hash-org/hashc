//! Contains various mappings and conversions between the generic code
//! generation types and the LLVM backend specific data types.

use hash_codegen::common::{AtomicOrdering, IntComparisonKind, RealComparisonKind};
use hash_target::abi::AddressSpace;
use inkwell::attributes::Attribute;

use crate::context::CodeGenCtx;

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

/// Represents a **subset** the attribute kinds that can be applied to a
/// function or a call site of a function. This mimics the LLVM `AttributeKind`
/// enum defined in `llvm/IR/Attributes.h`, more specifically at
/// <https://github.com/llvm/llvm-project/blob/bf47ffaa76fbda1ba96d41ee2681e45d2445be1e/llvm/include/llvm/IR/Attributes.td#L63>
#[derive(Copy, Clone, Debug)]
pub enum AttributeKind {
    ByRef,
    Cold,
    Convergent,
    InAlloca,
    InlineHint,
    InReg = 12,
    ElementType,
    JumpTable,
    Memory,
    MinSize,
    Naked,
    NoAlias = 21,
    NoBuiltin,
    NoCallback,
    NoCapture = 24,
    NoDuplicate,
    NoFree,
    NoReturn = 34,
    NoImplicitFloat,
    NoInline,
    NoUndef = 38,
    NoMerge,
    NoRecurse,
    NonNull = 41,
    NoRedZone,
    NoSync,
    NoUnwind,
    NoSanitizeBounds,
    NoSanitizeCoverage,
    ReadOnly = 48,
    NullPointerIsValid,
    OptimizeForSize,
    SExt = 51,
    OptimizeNone,
    Preallocated,
    ReadNone,
    Returned,
    SafeStack,
    StackAlignment,
    StackProtect,
    StackProtectReq,
    ZExt = 70,
    StackProtectStrong,
    ByVal = 72,
    StructRet = 76,
    SanitizeAddress,
    SanitizeThread,
    SanitizeMemory,

    Dereferenceable = 80,
    DereferenceableOrNull = 81,

    UWTable,
    Alignment,
    AllocAlign,
    AllocKind,
    AllocatedPointer,
    AllocSize,
    AlwaysInline,
}

impl AttributeKind {
    pub fn to_str(&self) -> &'static str {
        match self {
            AttributeKind::Alignment => "align",
            AttributeKind::AllocAlign => "allocalign",
            AttributeKind::AllocKind => "allockind",
            AttributeKind::AllocatedPointer => "allocptr",
            AttributeKind::AllocSize => "allocsize",
            AttributeKind::AlwaysInline => "alwaysinline",
            AttributeKind::ByVal => "byval",
            AttributeKind::ByRef => "byref",
            AttributeKind::NoUndef => "noundef",
            AttributeKind::Cold => "cold",
            AttributeKind::Convergent => "convergent",
            AttributeKind::Dereferenceable => "dereferenceable",
            AttributeKind::DereferenceableOrNull => "dereferenceable_or_null",
            AttributeKind::ElementType => "elementtype",
            AttributeKind::InAlloca => "inalloca",
            AttributeKind::InlineHint => "inlinehint",
            AttributeKind::InReg => "inreg",
            AttributeKind::JumpTable => "jumptable",
            AttributeKind::Memory => "memory",
            AttributeKind::MinSize => "minsize",
            AttributeKind::Naked => "naked",
            AttributeKind::NoAlias => "noalias",
            AttributeKind::NoBuiltin => "nobuiltin",
            AttributeKind::NoCallback => "nocallback",
            AttributeKind::NoCapture => "nocapture",
            AttributeKind::NoDuplicate => "noduplicate",
            AttributeKind::NoFree => "nofree",
            AttributeKind::NoImplicitFloat => "noimplicitfloat",
            AttributeKind::NoInline => "noinline",
            AttributeKind::NoMerge => "nomerge",
            AttributeKind::NonNull => "nonnull",
            AttributeKind::NoRecurse => "norecurse",
            AttributeKind::NoRedZone => "noredzone",
            AttributeKind::NoReturn => "noreturn",
            AttributeKind::NoSync => "nosync",
            AttributeKind::NoUnwind => "nounwind",
            AttributeKind::NoSanitizeBounds => "nosanitize_bounds",
            AttributeKind::NoSanitizeCoverage => "nosanitize_coverage",
            AttributeKind::NullPointerIsValid => "null_pointer_is_valid",
            AttributeKind::OptimizeForSize => "optsize",
            AttributeKind::OptimizeNone => "optnone",
            AttributeKind::Preallocated => "preallocated",
            AttributeKind::ReadNone => "readnone",
            AttributeKind::ReadOnly => "readonly",
            AttributeKind::Returned => "returned",
            AttributeKind::SafeStack => "safestack",
            AttributeKind::SExt => "signext",
            AttributeKind::StackAlignment => "stackalign",
            AttributeKind::StackProtect => "ssp",
            AttributeKind::StackProtectReq => "sspreq",
            AttributeKind::StackProtectStrong => "sspstrong",
            AttributeKind::StructRet => "sret",
            AttributeKind::SanitizeAddress => "sanitize_address",
            AttributeKind::SanitizeThread => "sanitize_thread",
            AttributeKind::SanitizeMemory => "sanitize_memory",
            AttributeKind::UWTable => "uwtable",
            AttributeKind::ZExt => "zeroext",
        }
    }

    /// Create an [Attribute] from an [AttributeKind].
    pub fn create_attribute(&self, ctx: &CodeGenCtx<'_>) -> Attribute {
        // @@Naming: the `create_enum_attribute` will create an attribute
        // with just an integer value, furthermore the value "0" denotes that
        // the attribute is just a flag. This is a really bad design
        // decision on the wrapper, but we can't do much here beyond complaining...
        // or patching an existing wrapper.
        //
        // This comes from having a look at https://docs.hdoc.io/hdoc/llvm-project/rA9A65D21E1B5E7CF.html#DEBC8EEACD63FC31
        ctx.ll_ctx.create_enum_attribute(*self as u32, 0)
    }
}

// get_named_enum_kind_id
#[cfg(test)]
mod tests {
    use inkwell::attributes::Attribute;

    use crate::misc::AttributeKind;

    #[test]
    fn verify_attribute_kinds_match() {
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::NoAlias.to_str()),
            AttributeKind::NoAlias as u32
        );
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::NoCapture.to_str()),
            AttributeKind::NoCapture as u32
        );
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::NoUndef.to_str()),
            AttributeKind::NoUndef as u32
        );
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::NonNull.to_str()),
            AttributeKind::NonNull as u32
        );
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::ReadOnly.to_str()),
            AttributeKind::ReadOnly as u32
        );
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::ByVal.to_str()),
            AttributeKind::ByVal as u32
        );
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::StructRet.to_str()),
            AttributeKind::StructRet as u32
        );
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::NoReturn.to_str()),
            AttributeKind::NoReturn as u32
        );
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::Dereferenceable.to_str()),
            AttributeKind::Dereferenceable as u32
        );
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::DereferenceableOrNull.to_str()),
            AttributeKind::DereferenceableOrNull as u32
        );
        assert_eq!(
            Attribute::get_named_enum_kind_id(AttributeKind::Dereferenceable.to_str()),
            AttributeKind::Dereferenceable as u32
        );

        assert_eq!(Attribute::get_named_enum_kind_id("signext"), AttributeKind::SExt as u32);
        assert_eq!(Attribute::get_named_enum_kind_id("zeroext"), AttributeKind::ZExt as u32);
    }
}
