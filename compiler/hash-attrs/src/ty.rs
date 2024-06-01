//! Implementation for the registering procedural macro which can parse
//! attribute definitions into something that the compiler can understand and
//! later use to programatically check attribute annotations.

use hash_ast_utils::attr::AttrTarget;
use hash_repr::ty::{ReprTyId, COMMON_REPR_TYS};
use hash_source::{identifier::Identifier, Size};
use hash_storage::store::statics::StoreId;
use hash_tir::tir::{
    DataDefCtors, DataTy, NumericCtorBits, NumericCtorInfo, ParamIndex, ParamsId,
    PrimitiveCtorInfo, Ty, TyId,
};
use hash_utils::{
    fxhash::FxHashMap,
    index_vec::{define_index_type, IndexVec},
};

use crate::builtin::ATTR_MAP;

define_index_type! {
    /// This is the unique identifier for an AST node. This is used to
    /// map spans to nodes, and vice versa. [AstNodeId]s are unique and
    /// they are always increasing as a new nodes are created.
    pub struct AttrId = u32;
    MAX_INDEX = i32::MAX as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

impl AttrId {
    /// Get the name of the attribute.
    pub fn name(&self) -> Identifier {
        ATTR_MAP.map[*self].name
    }
}

/// A table that stores the definitions for all of the builtin compiler
/// attributes that a program may use. The table stores information about what
/// the type of the attributes parameters are, and what kind of subject the
/// attribute is allowed to be applied onto.
#[derive(Debug, Default)]
pub struct AttrTyMap {
    /// A storage of all of the attributes that the compiler knows and
    /// supports.
    pub(crate) map: IndexVec<AttrId, AttrTy>,

    /// A mapping between the name of an attribute and its [AttrId].
    pub(crate) name_map: FxHashMap<Identifier, AttrId>,
}

impl AttrTyMap {
    /// Create a new [AttrTyMap].
    pub fn new() -> Self {
        Self { map: IndexVec::new(), name_map: FxHashMap::default() }
    }

    /// Get the [AttrTy] for the given [AttrId].
    pub fn get(&self, id: AttrId) -> &AttrTy {
        &self.map[id]
    }

    /// Get the [AttrId] by the name of the attribute.
    pub fn get_id_by_name(&self, name: Identifier) -> Option<AttrId> {
        self.name_map.get(&name).copied()
    }

    /// Get the [AttrTy] by the name of the attribute.
    pub fn get_by_name(&self, name: Identifier) -> Option<&AttrTy> {
        self.name_map.get(&name).map(|id| &self.map[*id])
    }
}

/// An [AttrTy] stores the expected "type" of the parameter arguments, so that
/// the compiler can check that the arguments are correct.
#[derive(Debug)]
pub struct AttrTy {
    /// The name of the attribute.
    pub name: Identifier,

    /// The type of the parameters that the attribute expects. We use
    /// [ParamsId] in order so that we can use the defined logic in
    /// [hash_tir::utils::params] to check that the arguments to an
    /// attribute are correct. This is possible because the same rules
    /// to attribute parameters and arguments apply as they do to other
    /// parameters and arguments.
    pub params: ParamsId,

    /// The expected kind of subject that the attribute is allowed to be
    /// applied onto.
    pub subject: AttrTarget,
}

impl AttrTy {
    /// Create a new [AttrTy] with the given name, parameters and subject.
    pub fn new(name: impl Into<Identifier>, params: ParamsId, subject: AttrTarget) -> Self {
        Self { name: name.into(), params, subject }
    }

    /// Get the type of a parameter at a given [ParamIndex].
    ///
    /// If the parameter doesn't exist, then `None` is returned.
    pub fn ty_of_param(&self, index: ParamIndex) -> Option<TyId> {
        self.params.at_index(index).map(|param| param.borrow().ty)
    }
}

fn repr_ty_from_primitive_ctor(ctor: PrimitiveCtorInfo) -> Option<ReprTyId> {
    Some(match ctor {
        PrimitiveCtorInfo::Numeric(NumericCtorInfo { bits, flags }) => {
            if flags.is_float() {
                match bits {
                    NumericCtorBits::Bounded(32) => COMMON_REPR_TYS.f32,
                    NumericCtorBits::Bounded(64) => COMMON_REPR_TYS.f64,

                    // Other bits widths are not supported.
                    _ => unreachable!(),
                }
            } else {
                match bits {
                    NumericCtorBits::Bounded(bits) => {
                        let size = Size::from_bits(bits);

                        if flags.is_signed() {
                            match size.bytes() {
                                // If this is a platform type, return `isize`
                                _ if flags.is_platform() => COMMON_REPR_TYS.isize,
                                1 => COMMON_REPR_TYS.i8,
                                2 => COMMON_REPR_TYS.i16,
                                4 => COMMON_REPR_TYS.i32,
                                8 => COMMON_REPR_TYS.i64,
                                16 => COMMON_REPR_TYS.i128,
                                _ => unreachable!(), /* Other bits widths are not
                                                      * supported. */
                            }
                        } else {
                            match size.bytes() {
                                // If this is a platform type, return `usize`
                                _ if flags.is_platform() => COMMON_REPR_TYS.usize,
                                1 => COMMON_REPR_TYS.u8,
                                2 => COMMON_REPR_TYS.u16,
                                4 => COMMON_REPR_TYS.u32,
                                8 => COMMON_REPR_TYS.u64,
                                16 => COMMON_REPR_TYS.u128,
                                _ => unreachable!(), /* Other bits widths are not
                                                      * supported. */
                            }
                        }
                    }
                    NumericCtorBits::Unbounded => {
                        if flags.is_signed() {
                            COMMON_REPR_TYS.ibig
                        } else {
                            COMMON_REPR_TYS.ubig
                        }
                    }
                }
            }
        }

        // @@Temporary: `str` implies that it is a `&str`
        PrimitiveCtorInfo::Str => COMMON_REPR_TYS.str,
        PrimitiveCtorInfo::Char => COMMON_REPR_TYS.char,
        PrimitiveCtorInfo::Array(..) => return None,
    })
}

/// This is a utility that assumes a [ReprTy] can be derived from the
/// given [TyId] that is primitive. The assumption is that this type is
/// a primitive (non-array).
///
/// @@Hack: This is primarily being used for attribute type lowerings. Ideally,
/// we should be able ti use the standard type lowering infrastructure in order
/// to fully support all types in attributes in the future. For now, since
/// attributes can only be literals, therefore we can rely on this method to
/// lower the supported subset of types.
pub fn repr_ty_from_primitive_ty(ty: TyId) -> Option<ReprTyId> {
    if let Ty::DataTy(DataTy { data_def, .. }) = ty.value().data {
        if let DataDefCtors::Primitive(ctor) = data_def.value().ctors {
            return repr_ty_from_primitive_ctor(ctor);
        }
    }

    None
}
