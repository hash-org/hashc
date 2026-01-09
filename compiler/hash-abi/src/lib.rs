//! This module defines types and logic that deal with ABIs (Application Binary
//! Interfaces). This is needed in order to communicate with the outside world
//! and to be able to call functions from other languages, but to also provide
//! information to code generation backends about how values are represented.

use hash_ir::ty::{InstanceId, ReprTyId};
use hash_repr::{LayoutId, TyInfo};
use hash_storage::{new_store_key, store::statics::StoreId};
use hash_target::{
    Target,
    abi::{Abi, AbiRepresentation, Scalar},
    size::Size,
};
use hash_utils::bitflags;

/// Defines the available calling conventions that can be
/// used when invoking functions with the ABI.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CallingConvention {
    /// The C calling convention.
    ///
    /// Equivalent to the `ccc` calling convention in LLVM.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#calling-conventions> (ccc)
    C = 0,

    /// Cold calling convention for functions that are unlikely to be called.
    ///
    /// Equivalent to the `coldcc` calling convention in LLVM.
    ///
    /// Ref: <https://llvm.org/docs/LangRef.html#calling-conventions> (coldcc)
    Cold = 9,
}

impl CallingConvention {
    /// Create a new [CallingConvention] from the provided [Abi] whilst
    /// also making any adjustments according to the current compilation
    /// [Target].
    pub fn make_from_abi_and_target(abi: Abi, target: &Target) -> Self {
        match target.adjust_abi(abi) {
            Abi::C | Abi::Hash => CallingConvention::C,
            Abi::Cold => CallingConvention::Cold,
        }
    }
}

new_store_key!(pub FnAbiId, derives = Debug);

/// Defines ABI specific information about a function.
///
/// @@TODO: Do we need to record information about variadics here (when we add
/// them)?
#[derive(Debug, Clone)]
pub struct FnAbi {
    /// The ID of the function ABI if any.
    pub ty: ReprTyId,

    /// All the types of the arguments in order, and how they should
    /// be passed to the function (as per convention).
    pub args: Box<[ArgAbi]>,

    /// The return type of the function, and how it should be returned
    /// (as per convention).
    pub ret_abi: ArgAbi,

    /// The calling convention that should be used when invoking the function.
    pub calling_convention: CallingConvention,
}

/// Defines ABI specific information about an argument. [ArgAbi] is also
/// used to denote the return type of the function it has similar conventions
/// to function arguments.
#[derive(Debug, Clone, Copy)]
pub struct ArgAbi {
    /// The type of the argument.
    pub info: TyInfo,

    /// The passing mode of the argument.
    pub mode: PassMode,
}

impl ArgAbi {
    /// Create a new [ArgAbi] with the provided [TyInfo].
    pub fn new(info: TyInfo, attributes_from_scalar: impl Fn(Scalar) -> ArgAttributes) -> Self {
        let mode = info.layout.map(|layout| match layout.abi {
            AbiRepresentation::Uninhabited => PassMode::Ignore,
            AbiRepresentation::Scalar(scalar) => PassMode::Direct(attributes_from_scalar(scalar)),
            AbiRepresentation::Pair(scalar_a, scalar_b) => {
                PassMode::Pair(attributes_from_scalar(scalar_a), attributes_from_scalar(scalar_b))
            }
            AbiRepresentation::Vector { .. } => PassMode::Direct(ArgAttributes::new()),
            AbiRepresentation::Aggregate => PassMode::Direct(ArgAttributes::new()),
        });

        Self { info, mode }
    }

    /// Create a new [`PassMode::Indirect`] based on the provided [Layout].
    fn indirect_pass_mode(layout: LayoutId) -> PassMode {
        let mut attributes = ArgAttributes::new();

        attributes
            .set(ArgAttributeFlag::NON_NULL)
            .set(ArgAttributeFlag::NO_ALIAS)
            .set(ArgAttributeFlag::NO_CAPTURE)
            .set(ArgAttributeFlag::NO_UNDEF);

        attributes.pointee_size = layout.size();

        PassMode::Indirect { attributes, on_stack: false }
    }

    /// Make the argument be passed indirectly.
    pub fn make_indirect(&mut self) {
        // Firstly, verify that that we aren't making an ignored argument indirect.
        match self.mode {
            PassMode::Direct(_) | PassMode::Pair(_, _) => {}
            PassMode::Indirect { on_stack: false, .. } => return,
            kind => panic!("tried to make this argument with mode {kind:?} indirectly"),
        }

        self.mode = Self::indirect_pass_mode(self.info.layout);
    }

    /// Make the argument be passed on the stack.
    pub fn make_indirect_by_stack(&mut self) {
        self.make_indirect();

        match self.mode {
            PassMode::Indirect { ref mut on_stack, .. } => {
                *on_stack = true;
            }
            _ => unreachable!(),
        }
    }

    /// Check if the [PassMode] of the [ArgAbi] is "indirect".
    pub fn is_indirect(&self) -> bool {
        matches!(self.mode, PassMode::Indirect { .. })
    }

    /// Check if the [PassMode] of the [ArgAbi] is "ignored".
    pub fn is_ignored(&self) -> bool {
        matches!(self.mode, PassMode::Ignore)
    }
}

bitflags::bitflags! {
    /// Defines the relevant attributes to ABI arguments.
    #[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
    pub struct ArgAttributeFlag: u16 {
        /// This specifies that this pointer argument does not alias
        /// any other arguments or the return value.
        const NO_ALIAS = 1 << 1;

        /// This specifies that this pointer argument is not captured
        /// by the callee function.
        const NO_CAPTURE = 1 << 2;

        /// This specifies that the pointer argument does not contain
        /// any undefined values or is un-initialised.
        ///
        /// In the following "llvm" example, this denotes that `foo` takes
        /// a pointer argument `x` that does not contain any undefined values.
        /// ```llvm
        /// define i32 @foo(i32* noundef %x) {
        /// ...
        /// }
        /// ```
        const NO_UNDEF = 1 << 3;
        /// This denotes that the pointer argument is not-null.

        const NON_NULL = 1 << 4;

        /// The argument is a read-only value.
        const READ_ONLY = 1 << 5;

        /// Apply a hint to the code generation that this particular
        /// argument should be passed in a register.
        const IN_REG = 1 << 6;
    }
}

/// Defines how an argument should be extended to a certain size.
///
/// This is used when a particular ABI requires small integer sizes to
/// be extended to a full or a partial register size. Additionally, the
/// ABI defines whether the value should be sign-extended or zero-extended.
///
/// If this is not required, this should be set to [`ArgExtension::NoExtend`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ArgExtension {
    /// The argument should be zero-extended.
    ZeroExtend,

    /// The argument should be sign-extended.
    SignExtend,

    /// The argument does not need to be extended.
    #[default]
    NoExtend,
}

/// [ArgAttributes] provides all of the attributes that a
/// particular argument has, as in additional information that
/// can be used by the compiler to generate better code, or
/// if it is targetting a specific ABI which requires certain
/// operations to be performed on the argument in order to
/// properly pass it to the function.
#[derive(Debug, Clone, Copy, Default)]
pub struct ArgAttributes {
    /// Additional information about the argument in the form
    /// of bit flags. The [ArgAttributeFlag] resemble a similar
    /// naming convention to LLVM's function parameter attributes
    /// but they are intended to be used regardless of which
    /// backend is being targeted.
    pub flags: ArgAttributeFlag,

    /// Depending on the ABI, the argument may need to be zero/sign-extended
    /// to a certain size.
    pub extension: ArgExtension,

    /// Denotes the size of the pointee if this is a argument passed by
    /// a pointer. If it is not a pointer argument, then the size is
    /// recorded as [`Size::ZERO`].
    pub pointee_size: Size,
}

impl ArgAttributes {
    /// Create a new [ArgAttributes].
    pub fn new() -> Self {
        Self {
            flags: ArgAttributeFlag::default(),
            extension: ArgExtension::NoExtend,
            pointee_size: Size::ZERO,
        }
    }

    /// Apply a [ArgAttributeFlag] to the [ArgAttributes].
    pub fn set(&mut self, attribute: ArgAttributeFlag) -> &mut Self {
        self.flags |= attribute;
        self
    }

    /// Check if a particular [ArgAttributeFlag] exists on a
    /// [ArgAttributes].
    pub fn contains(&self, attribute: ArgAttributeFlag) -> bool {
        self.flags.contains(attribute)
    }

    /// Apply an argument extension to the [ArgAttributes].
    pub fn extend_with(&mut self, extension: ArgExtension) {
        debug_assert!(
            self.extension == ArgExtension::NoExtend || self.extension == extension,
            "extension already set"
        );
        self.extension = extension;
    }
}

/// Defines how an argument should be passed to a function.
#[derive(Debug, Clone, Copy)]
pub enum PassMode {
    /// Ignore the argument, this is used for arguments that are not
    /// inhabited (as in cannot be constructed) or ZSTs.
    Ignore,

    /// Pass the argument directly.
    ///
    /// The argument has a layout ABI of [`AbiRepresentation::Scalar`] or
    /// [`AbiRepresentation::Vector`], and potentially
    /// [`AbiRepresentation::Aggregate`] if the ABI allows for "small"
    /// structures to be passed as just integers.
    Direct(ArgAttributes),

    /// Pass a pair's elements directly in two arguments.
    ///
    /// The argument has a layout abi of `ScalarPair`.
    Pair(ArgAttributes, ArgAttributes),

    /// Pass the argument indirectly via a pointer. This corresponds to
    /// passing arguments "by value". The "by value" semantics implies that
    /// a copy of the argument is made between the caller and callee. This
    /// is used to pass structs and arrays as arguments.
    ///
    /// N.B. This is not a valid attribute on a return type.
    Indirect {
        /// Attributes about the argument.
        attributes: ArgAttributes,

        /// Whether or not this is being passed on the
        /// stack.
        on_stack: bool,
    },
}

impl PassMode {
    /// Check if the [PassMode] specifies that the argument is passed
    /// indirectly.
    pub fn is_indirect(&self) -> bool {
        matches!(self, Self::Indirect { .. })
    }
}
