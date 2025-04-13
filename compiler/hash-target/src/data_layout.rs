//! Contains common interfaces for layouts on various targets, and
//! as well an interface to access information about a specific
//! layout. Furthermore, this module contains logic about parsing
//! layout from a "layout specification" string, more information
//! about this can be found (https://llvm.org/docs/LangRef.html#data-layout)[here].

use std::num::ParseIntError;

use crate::{
    abi::{AddressSpace, Integer},
    alignment::{Alignment, Alignments},
    size::Size,
};

/// Interface to access information about the target layout.
pub trait HasDataLayout {
    fn data_layout(&self) -> &TargetDataLayout;
}

impl HasDataLayout for TargetDataLayout {
    #[inline]
    fn data_layout(&self) -> &TargetDataLayout {
        self
    }
}

/// This enum defines the Endianness of a target, which is used
/// when reading/writing scalar values to memory. More information
/// about Endianness can be found (https://en.wikipedia.org/wiki/Endianness)[here].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endian {
    /// Values use the little endian format.
    Little,

    /// Values use the big endian format.
    Big,
}

impl Endian {
    /// Convert the [Endian] to a static string.
    pub fn as_str(&self) -> &'static str {
        match self {
            Endian::Little => "little",
            Endian::Big => "big",
        }
    }
}

/// Defines all of the specifics of how primitive types are
/// lay'd out for a specific target. The layout of a target
/// is specified as a "layout specification" string, more information
/// about this can be found (https://llvm.org/docs/LangRef.html#data-layout)[here].
#[derive(Debug, Clone)]
pub struct TargetDataLayout {
    /// The kind of Endianness that the target uses.
    pub endian: Endian,

    /// Alignment of bit values on the target.
    pub i1_align: Alignments,

    /// The alignment of byte values on the target.
    pub i8_align: Alignments,

    /// The alignment of 16-bit values on the target.
    pub i16_align: Alignments,

    /// The alignment of 32-bit values on the target.
    pub i32_align: Alignments,

    /// The alignment of 64-bit values on the target.
    pub i64_align: Alignments,

    /// The alignment of 128-bit values on the target.
    pub i128_align: Alignments,

    /// The [Size] of a pointer on the target.
    pub pointer_size: Size,

    /// The alignment of pointers on the target.
    pub pointer_align: Alignments,

    /// Alignment of `f32` values on the target.
    pub f32_align: Alignments,

    /// Alignment of `f64` values on the target.
    pub f64_align: Alignments,

    /// Alignment specifics of aggregate types on the target.
    pub aggregate_align: Alignments,

    /// Alignment of vector types on the target. Each element
    /// corresponds a pair of the "vector" size, and its alignment.
    pub vector_align: Vec<(Size, Alignments)>,

    /// The address space of the program counter register.
    pub instruction_address_space: AddressSpace,

    /// Minimum size of C-Style enums on the target.
    ///
    /// N.B. This is not specified by the LLVM specification, but
    /// is required for representing these types when dealing with
    /// FFI.
    pub c_style_enum_min_size: Integer,
}

impl TargetDataLayout {
    /// Get an equivalent [Integer] representation for a pointer
    /// on the current target.
    pub fn ptr_sized_integer(&self) -> Integer {
        match self.pointer_size.bits() {
            16 => Integer::I16,
            32 => Integer::I32,
            64 => Integer::I64,
            size => unreachable!("unknown pointer size of `{size}`"),
        }
    }

    /// Returns the exclusive upper bound on an object size. This is the maximum
    /// size of an object that can be allocated on the target.
    ///
    /// The upper bound on 64-bit currently needs to be lower because LLVM uses
    /// a 64-bit integer to represent object size in bits. It would need to
    /// be 1 << 61 to account for this, but is currently conservatively
    /// bounded to 1 << 47 as that is enough to cover the current usable
    /// address space on 64-bit ARMv8 and x86_64.
    pub fn obj_size_bound(&self) -> u64 {
        match self.pointer_size.bits() {
            16 => 1 << 15,
            32 => 1 << 31,
            64 => 1 << 47,
            _ => unreachable!(),
        }
    }
}

impl Default for TargetDataLayout {
    /// Create a default value for [`TargetDataLayout`] based on the
    /// LLVM specification for the default data layout
    /// (https://llvm.org/docs/LangRef.html#data-layout)(here).
    ///
    /// N.B. `c_style_enum_min_size` is set to `I32`, which is not
    /// based on the specification because it does not specify a
    /// default value for this field.
    fn default() -> Self {
        let make_align = |bits| Alignment::from_bits(bits).unwrap();

        Self {
            endian: Endian::Little,
            i1_align: Alignments::new(make_align(8)),
            i8_align: Alignments::new(make_align(8)),
            i16_align: Alignments::new(make_align(16)),
            i32_align: Alignments::new(make_align(32)),
            i64_align: Alignments { abi: make_align(32), preferred: make_align(64) },
            i128_align: Alignments { abi: make_align(32), preferred: make_align(64) },
            pointer_size: Size::from_bits(64),
            pointer_align: Alignments::new(make_align(64)),
            f32_align: Alignments::new(make_align(32)),
            f64_align: Alignments::new(make_align(64)),
            aggregate_align: Alignments { abi: make_align(0), preferred: make_align(64) },
            instruction_address_space: AddressSpace::DATA,
            vector_align: vec![
                (Size::from_bits(64), Alignments::new(make_align(64))),
                (Size::from_bits(128), Alignments::new(make_align(128))),
            ],
            c_style_enum_min_size: Integer::I32,
        }
    }
}

pub enum TargetDataLayoutParseError<'a> {
    /// The specified data layout string was invalid, and could
    /// not be parsed into separate components.
    Malformed { dl: &'a str },

    /// The specified address space is invalid.
    InvalidAddressSpace { addr_space: &'a str, err: ParseIntError },

    /// The string specified an invalid alignment.
    InvalidAlignment { cause: &'a str },

    /// Some unexpected bits were found in the string.
    InvalidBits { kind: &'a str, bit: &'a str, cause: &'a str, err: ParseIntError },

    /// The string is missing an alignment after a type specifier.
    MissingAlignment { cause: &'a str },

    /// Inconsistent target architecture.
    InconsistentTargetArchitecture { dl: &'a str, target: &'a str },

    /// When the data layout string specifies an inconsistent pointer size
    /// with the target.
    InconsistentTargetPointerWidth {
        /// The size specified on the string.
        size: u64,
        /// The expected pointer size on the target.
        target: u64,
    },

    /// When a data layout incorrectly specifies the size of C-style enums.
    InvalidEnumSize { err: String },
}

impl TargetDataLayout {
    /// Parse a [`TargetDataLayout`] from a "layout specification" string.
    ///
    /// The data layout string is specified in the LLVM documentation
    /// [here](https://llvm.org/docs/LangRef.html#data-layout).
    pub fn parse_from_llvm_data_layout_string(
        input: &str,
    ) -> Result<Self, TargetDataLayoutParseError<'_>> {
        let mut data_layout = Self::default();
        let mut i128_align_src = 64;

        // If the data-layout string is empty, then we return an error
        // specifying that the layout string was malformed.
        if input.is_empty() {
            return Err(TargetDataLayoutParseError::Malformed { dl: input });
        }

        // Each item is separated by a dash
        for component in input.split('-') {
            let parts = component.split(':').collect::<Vec<_>>();

            match &*parts {
                ["e"] => data_layout.endian = Endian::Little,
                ["E"] => data_layout.endian = Endian::Big,

                // Specifies the address space that corresponds to program memory
                [p] if p.starts_with('P') => {
                    let addr_space = p[1..].parse::<u32>().map(AddressSpace).map_err(|err| {
                        TargetDataLayoutParseError::InvalidAddressSpace { addr_space: p, err }
                    })?;

                    data_layout.instruction_address_space = addr_space;
                }
                // this specifies the aggregate alignment
                ["a", values @ ..] => {
                    data_layout.aggregate_align = Self::parse_alignment_specification(values, "a")?;
                }
                ["f32", values @ ..] => {
                    data_layout.f32_align = Self::parse_alignment_specification(values, "f32")?;
                }
                ["f64", values @ ..] => {
                    data_layout.f64_align = Self::parse_alignment_specification(values, "f64")?;
                }
                [p @ ("p" | "p0"), s, values @ ..] => {
                    data_layout.pointer_align = Self::parse_alignment_specification(values, p)?;
                    data_layout.pointer_size =
                        Size::from_bits(s.parse::<u64>().map_err(|err| {
                            TargetDataLayoutParseError::InvalidBits {
                                kind: "size",
                                bit: s,
                                cause: p,
                                err,
                            }
                        })?);
                }

                // Integer alignments
                [s, values @ ..] if s.starts_with('i') => {
                    let bits = s[1..].parse::<u64>().map_err(|err| {
                        TargetDataLayoutParseError::InvalidBits {
                            kind: "size",
                            bit: s,
                            cause: s,
                            err,
                        }
                    })?;

                    // Parse the alignment and assign it to the correct integer
                    // type.
                    let alignments = Self::parse_alignment_specification(values, s)?;

                    match bits {
                        1 => data_layout.i1_align = alignments,
                        8 => data_layout.i8_align = alignments,
                        16 => data_layout.i16_align = alignments,
                        32 => data_layout.i32_align = alignments,
                        64 => data_layout.i64_align = alignments,
                        _ => {}
                    }

                    // From LLVM spec:
                    //
                    // 2. If no match is found, and the type sought is an
                    // integer type, then the smallest integer type that is
                    // larger than the bitwidth of the sought type is used. If
                    // none of the specifications are larger than the bitwidth
                    // then the largest integer type is used. For example, given
                    // the default specifications above, the i7 type will use
                    // the alignment of i8 (next largest) while both i65 and
                    // i256 will use the alignment of i64 (largest specified).

                    if bits >= i128_align_src && bits <= 128 {
                        data_layout.i128_align = alignments;
                        i128_align_src = bits;
                    }
                }

                // Everything else is ignored since it is not relevant to
                // the layout of data.
                _ => {}
            }
        }

        Ok(data_layout)
    }

    /// Parse a specified [Alignments] from the target data layout string. This
    /// will parse the expected "abi" alignment, and an optional "preferred"
    /// alignment value if it is specified.
    fn parse_alignment_specification<'a>(
        items: &[&'a str],
        cause: &'a str,
    ) -> Result<Alignments, TargetDataLayoutParseError<'a>> {
        if items.is_empty() {
            return Err(TargetDataLayoutParseError::MissingAlignment { cause });
        }

        let alignment_from_bits = |bits| {
            Alignment::from_bits(bits)
                .map_err(|_| TargetDataLayoutParseError::InvalidAlignment { cause })
        };

        // Read a `u64` from the component, or otherwise create an error with
        // additional metadata about why parsing failed.
        let parse_bits = |bits: &'a str, kind: &'a str, cause: &'a str| {
            bits.parse::<u64>().map_err(|err| TargetDataLayoutParseError::InvalidBits {
                kind,
                bit: bits,
                cause,
                err,
            })
        };

        let abi = alignment_from_bits(parse_bits(items[0], "alignment", cause)?)?;
        let preferred = items
            .get(1)
            .map_or(Ok(abi), |item| alignment_from_bits(parse_bits(item, "alignment", cause)?))?;

        Ok(Alignments { abi, preferred })
    }
}
