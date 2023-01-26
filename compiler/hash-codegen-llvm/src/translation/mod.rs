//! Hash compiler LLVM code generation crate. This crate contains all of the
//! logic of transforming generated Hash IR into LLVM IR so that it can be
//! compiled by LLVM into a native executable with the specified target triple.
#![allow(dead_code, unused)] // @@Temporary: remove this when all items are implemented and the
                             // codegen is fully functional.

use hash_codegen::{
    common::{AtomicOrdering, IntComparisonKind, RealComparisonKind},
    layout::{compute::LayoutComputer, LayoutCtx},
    traits::{ctx::HasCtxMethods, target::HasTargetSpec, Backend, BackendTypes, Codegen},
};
use hash_ir::IrCtx;
use hash_pipeline::settings::CompilerSettings;
use hash_target::{abi::AddressSpace, Target};

use self::context::CodeGenCtx;

mod abi;
mod builder;
mod constants;
mod context;
mod debug_info;
mod declare;
mod intrinsics;
mod layouts;
mod metadata;
mod misc;
mod ty;

/// A [Builder] is defined as being a context that is used to implement
/// all of the specified builder methods.
pub struct Builder<'b> {
    /// The actual InkWell builder
    builder: inkwell::builder::Builder<'b>,

    /// The context for the builder.
    ctx: &'b CodeGenCtx<'b>,
}

/// This specifies that the [Builder] context is [CodegenCtx].
impl<'b> Codegen<'b> for Builder<'b> {
    type CodegenCtx = CodeGenCtx<'b>;
}

/// This specifies all of the common IR type kinds for [Builder].
impl<'b> BackendTypes for Builder<'b> {
    type Value = <CodeGenCtx<'b> as BackendTypes>::Value;
    type Function = <CodeGenCtx<'b> as BackendTypes>::Function;
    type Type = <CodeGenCtx<'b> as BackendTypes>::Type;
    type BasicBlock = <CodeGenCtx<'b> as BackendTypes>::BasicBlock;

    type DebugInfoScope = <CodeGenCtx<'b> as BackendTypes>::DebugInfoScope;
    type DebugInfoLocation = <CodeGenCtx<'b> as BackendTypes>::DebugInfoLocation;
    type DebugInfoVariable = <CodeGenCtx<'b> as BackendTypes>::DebugInfoVariable;
}

impl<'b> Backend<'b> for Builder<'b> {}

impl<'b> std::ops::Deref for Builder<'b> {
    type Target = CodeGenCtx<'b>;

    fn deref(&self) -> &Self::Target {
        self.ctx
    }
}

impl<'b> HasCtxMethods<'b> for Builder<'b> {
    fn settings(&self) -> &CompilerSettings {
        self.ctx.settings()
    }

    fn ir_ctx(&self) -> &IrCtx {
        self.ctx.ir_ctx()
    }

    fn layouts(&self) -> &LayoutCtx {
        self.ctx.layouts()
    }

    fn layout_computer(&self) -> LayoutComputer<'_> {
        LayoutComputer::new(self.layouts(), self.ir_ctx())
    }
}

impl HasTargetSpec for Builder<'_> {
    fn target_spec(&self) -> &Target {
        todo!()
    }
}

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
pub enum MetadataType {
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
