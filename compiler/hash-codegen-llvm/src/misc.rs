//! Contains various mappings and conversions between the generic code
//! generation types and the LLVM backend specific data types.

use hash_codegen::{
    common::{AtomicOrdering, IntComparisonKind, RealComparisonKind},
    target::link::{CodeModel, RelocationModel},
};
use hash_pipeline::settings::OptimisationLevel;
use inkwell::{
    attributes::Attribute,
    types::{AnyTypeEnum, BasicMetadataTypeEnum},
};

use crate::ctx::CodeGenCtx;

/// Wrapper type around [inkwell::IntPredicate] to allow for conversion from
/// [IntComparisonKind].
pub struct IntPredicateWrapper(pub inkwell::IntPredicate);

impl From<IntComparisonKind> for IntPredicateWrapper {
    fn from(value: IntComparisonKind) -> Self {
        use inkwell::IntPredicate::*;

        match value {
            IntComparisonKind::Eq => Self(EQ),
            IntComparisonKind::Ne => Self(NE),
            IntComparisonKind::Ugt => Self(UGT),
            IntComparisonKind::Uge => Self(UGE),
            IntComparisonKind::Ult => Self(ULT),
            IntComparisonKind::Ule => Self(ULE),
            IntComparisonKind::Sgt => Self(SGT),
            IntComparisonKind::Sge => Self(SGE),
            IntComparisonKind::Slt => Self(SLT),
            IntComparisonKind::Sle => Self(SLE),
        }
    }
}

/// Wrapper type around [inkwell::FloatPredicate] to allow for conversion from
/// [RealComparisonKind].
pub struct FloatPredicateWrapper(pub inkwell::FloatPredicate);

impl From<RealComparisonKind> for FloatPredicateWrapper {
    fn from(value: RealComparisonKind) -> Self {
        use inkwell::FloatPredicate::*;

        match value {
            RealComparisonKind::False => Self(PredicateFalse),
            RealComparisonKind::Oeq => Self(OEQ),
            RealComparisonKind::Ogt => Self(OGT),
            RealComparisonKind::Oge => Self(OGE),
            RealComparisonKind::Olt => Self(OLT),
            RealComparisonKind::Ole => Self(OLE),
            RealComparisonKind::One => Self(ONE),
            RealComparisonKind::Ord => Self(ORD),
            RealComparisonKind::Uno => Self(UNO),
            RealComparisonKind::Ueq => Self(UEQ),
            RealComparisonKind::Ugt => Self(UGT),
            RealComparisonKind::Uge => Self(UGE),
            RealComparisonKind::Ult => Self(ULT),
            RealComparisonKind::Ule => Self(ULE),
            RealComparisonKind::Une => Self(UNE),
            RealComparisonKind::True => Self(PredicateTrue),
        }
    }
}

/// Wrapper type around [inkwell::AtomicOrdering] to allow for conversion from
/// [AtomicOrdering].
pub struct AtomicOrderingWrapper(pub inkwell::AtomicOrdering);

impl From<AtomicOrdering> for AtomicOrderingWrapper {
    fn from(value: AtomicOrdering) -> Self {
        use inkwell::AtomicOrdering::*;

        match value {
            AtomicOrdering::NotAtomic => Self(NotAtomic),
            AtomicOrdering::Unordered => Self(Unordered),
            AtomicOrdering::Monotonic => Self(Monotonic),
            AtomicOrdering::Acquire => Self(Acquire),
            AtomicOrdering::Release => Self(Release),
            AtomicOrdering::AcquireRelease => Self(AcquireRelease),
            AtomicOrdering::SequentiallyConsistent => Self(SequentiallyConsistent),
        }
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
/// <https://github.com/llvm/llvm-project/blob/llvmorg-20.1.8/llvm/include/llvm/IR/Attributes.td#L63>
#[derive(Copy, Clone, Debug)]
pub enum AttributeKind {
    Alignment,
    AllocAlign,
    AllocKind,
    AllocatedPointer,
    AllocSize,
    AlwaysInline,
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
    NoAlias = 22,
    NoBuiltin,
    NoCallback,
    NoCapture = 25,
    NoDuplicate,
    NoFree,
    NoReturn = 37,
    NoImplicitFloat,
    NoInline,
    NoUndef = 41,
    NoMerge,
    NoRecurse,
    NonNull = 44,
    NoRedZone,
    NoSync,
    NoUnwind,
    NoSanitizeBounds,
    NoSanitizeCoverage,
    ReadOnly = 52,
    NullPointerIsValid,
    OptimizeForSize,
    SExt = 55,
    OptimizeNone,
    Preallocated,
    ReadNone,
    Returned,
    SafeStack,
    StackAlignment,
    StackProtect,
    StackProtectReq,
    ZExt = 80,
    StackProtectStrong,
    ByVal = 82,
    StructRet = 86,
    SanitizeAddress,
    SanitizeThread,
    SanitizeMemory,
    Dereferenceable = 91,
    DereferenceableOrNull,
    UWTable,
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
            AttributeKind::StackAlignment => "alignstack",
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
    pub fn create_attribute(&self, ctx: &CodeGenCtx<'_, '_>) -> Attribute {
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

/// A wrapper type to convert the generic [CodeModel] into the
/// [inkwell::targets::CodeModel] equivalent type.
pub struct CodeModelWrapper(pub inkwell::targets::CodeModel);

impl From<CodeModel> for CodeModelWrapper {
    fn from(value: CodeModel) -> Self {
        use inkwell::targets::CodeModel::*;

        match value {
            CodeModel::Default => CodeModelWrapper(Default),
            CodeModel::JITDefault => CodeModelWrapper(JITDefault),
            CodeModel::Small => CodeModelWrapper(Small),
            CodeModel::Kernel => CodeModelWrapper(Kernel),
            CodeModel::Medium => CodeModelWrapper(Medium),
            CodeModel::Large => CodeModelWrapper(Large),
        }
    }
}

/// A wrapper type to convert the generic [RelocationModel] into the
/// [inkwell::targets::RelocMode] equivalent type.
pub struct RelocationModeWrapper(pub inkwell::targets::RelocMode);

impl From<RelocationModel> for RelocationModeWrapper {
    fn from(value: RelocationModel) -> Self {
        use inkwell::targets::RelocMode::*;

        match value {
            RelocationModel::Static => RelocationModeWrapper(Static),
            RelocationModel::Pic | RelocationModel::Pie => RelocationModeWrapper(PIC),
            RelocationModel::DynamicNoPic => RelocationModeWrapper(DynamicNoPic),
        }
    }
}

/// A wrapper type to convert the generic [OptimisationLevel] into the
/// [inkwell::OptimizationLevel] equivalent type.
pub struct OptimisationLevelWrapper(pub inkwell::OptimizationLevel);

impl From<OptimisationLevel> for OptimisationLevelWrapper {
    fn from(value: OptimisationLevel) -> Self {
        use inkwell::OptimizationLevel::*;

        match value {
            OptimisationLevel::Debug => OptimisationLevelWrapper(None),
            OptimisationLevel::Release => OptimisationLevelWrapper(Aggressive),

            // @@Todo: there seems to be no way to specify that we want to optimise for
            // minimal size, i.e. `-Oz` in clang.
            OptimisationLevel::Size | OptimisationLevel::MinSize => {
                OptimisationLevelWrapper(Default)
            }
        }
    }
}

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

/// Convert a [BasicMetadataTypeEnum] into an [AnyTypeEnum].
///
/// This is similar to the conversion from [BasicTypeEnum] to [AnyTypeEnum],
/// but works with metadata types which are used in function parameter types.
pub fn convert_basic_metadata_ty_to_any<'m>(ty: BasicMetadataTypeEnum<'m>) -> AnyTypeEnum<'m> {
    match ty {
        BasicMetadataTypeEnum::ArrayType(ty) => AnyTypeEnum::ArrayType(ty),
        BasicMetadataTypeEnum::FloatType(ty) => AnyTypeEnum::FloatType(ty),
        BasicMetadataTypeEnum::IntType(ty) => AnyTypeEnum::IntType(ty),
        BasicMetadataTypeEnum::PointerType(ty) => AnyTypeEnum::PointerType(ty),
        BasicMetadataTypeEnum::ScalableVectorType(ty) => AnyTypeEnum::ScalableVectorType(ty),
        BasicMetadataTypeEnum::StructType(ty) => AnyTypeEnum::StructType(ty),
        BasicMetadataTypeEnum::VectorType(ty) => AnyTypeEnum::VectorType(ty),
        _ => unreachable!(),
    }
}
