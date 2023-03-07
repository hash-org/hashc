//! Contains all of the logic that is used by the lowering process
//! to convert types and [Ty]s into [IrTy]s.

use hash_intrinsics::{
    primitives::{AccessToPrimitives, DefinedPrimitives},
    utils::PrimitiveUtils,
};
use hash_ir::{
    ty::{
        self, AdtData, AdtField, AdtFlags, AdtId, AdtVariant, AdtVariants, IrTy, IrTyId,
        Mutability, RepresentationFlags,
    },
    IrCtx,
};
use hash_reporting::macros::panic_on_span;
use hash_source::{
    constant::{FloatTy, SIntTy, UIntTy},
    identifier::IDENTS,
};
use hash_target::size::Size;
use hash_tir::{
    data::{
        ArrayCtorInfo, DataDefCtors, DataTy, NumericCtorBits, NumericCtorInfo, PrimitiveCtorInfo,
    },
    environment::env::{AccessToEnv, Env},
    fns::FnTy,
    refs::RefTy,
    tuples::TupleTy,
    tys::{Ty, TyId},
    utils::{common::CommonUtils, AccessToUtils},
};
use hash_utils::{
    index_vec::index_vec,
    store::{PartialCloneStore, SequenceStore, SequenceStoreKey, Store},
};

/// A context that is used to lower types and terms into [IrTy]s.
pub(crate) struct TyLoweringCtx<'ir> {
    /// A reference to the store of all of the IR types.
    pub lcx: &'ir IrCtx,

    /// The type storage from the semantic analysis stage.
    pub tcx: &'ir Env<'ir>,

    /// The primitive storage from the semantic analysis stage.
    pub primitives: &'ir DefinedPrimitives,
}

impl<'ir> AccessToEnv for TyLoweringCtx<'ir> {
    fn env(&self) -> &Env {
        self.tcx
    }
}

impl AccessToPrimitives for TyLoweringCtx<'_> {
    fn primitives(&self) -> &DefinedPrimitives {
        self.primitives
    }
}

impl<'ir> TyLoweringCtx<'ir> {
    /// Create a new [TyLoweringCtx] from the given [IrCtx] and [GlobalStorage].
    pub fn new(lcx: &'ir IrCtx, tcx: &'ir Env<'ir>, primitives: &'ir DefinedPrimitives) -> Self {
        Self { lcx, tcx, primitives }
    }

    /// Get the [IrTyId] from a given [TyId]. This function will internally
    /// cache results of lowering a [TyId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(crate) fn ty_id_from_tir_ty(&self, id: TyId) -> IrTyId {
        // Check if the term is present within the cache, and if so, return the
        // cached value.
        if let Some(ty) = self.lcx.semantic_cache().borrow().get(&id.into()) {
            return *ty;
        }

        // @@Hack: avoid re-creating "commonly" used types in order
        // to allow for type_id equality to work
        let create_new_ty = |ty: IrTy| match ty {
            IrTy::Char => self.lcx.tys().common_tys.char,
            IrTy::Bool => self.lcx.tys().common_tys.bool,
            IrTy::UInt(UIntTy::U8) => self.lcx.tys().common_tys.u8,
            IrTy::UInt(UIntTy::U16) => self.lcx.tys().common_tys.u16,
            IrTy::UInt(UIntTy::U32) => self.lcx.tys().common_tys.u32,
            IrTy::UInt(UIntTy::U64) => self.lcx.tys().common_tys.u64,
            IrTy::UInt(UIntTy::U128) => self.lcx.tys().common_tys.u128,
            IrTy::UInt(UIntTy::USize) => self.lcx.tys().common_tys.usize,
            IrTy::Int(SIntTy::I8) => self.lcx.tys().common_tys.i8,
            IrTy::Int(SIntTy::I16) => self.lcx.tys().common_tys.i16,
            IrTy::Int(SIntTy::I32) => self.lcx.tys().common_tys.i32,
            IrTy::Int(SIntTy::I64) => self.lcx.tys().common_tys.i64,
            IrTy::Int(SIntTy::I128) => self.lcx.tys().common_tys.i128,
            IrTy::Int(SIntTy::ISize) => self.lcx.tys().common_tys.isize,
            IrTy::Float(FloatTy::F32) => self.lcx.tys().common_tys.f32,
            IrTy::Float(FloatTy::F64) => self.lcx.tys().common_tys.f64,
            _ => self.lcx.tys().create(ty),
        };

        // Lower the type into ir type.
        self.map_ty(id, |ty| {
            if let Ty::Data(data_ty) = ty {
                let data_ty = *data_ty;

                if let Some(ty) = self.lcx.semantic_cache().borrow().get(&data_ty.into()) {
                    return *ty;
                }

                // Convert the data-type into an ir type, cache it and return it
                let ty = create_new_ty(self.ty_from_tir_data(data_ty));

                // Add entries for both the data type and the type id.
                let mut cache = self.lcx.semantic_cache().borrow_mut();
                cache.insert(data_ty.into(), ty);
                cache.insert(id.into(), ty);

                ty
            } else {
                // Add an entry into the cache for this term
                let ty = create_new_ty(self.ty_from_tir_ty(id, ty));
                self.lcx.semantic_cache().borrow_mut().insert(id.into(), ty);
                ty
            }
        })
    }

    /// Get an [IrTy] from the given [Ty].
    pub(crate) fn ty_from_tir_ty_id(&self, id: TyId) -> IrTy {
        self.map_ty(id, |ty| self.ty_from_tir_ty(id, ty))
    }

    /// Get the [IrTy] from the given [Ty].
    pub(crate) fn ty_from_tir_ty(&self, id: TyId, ty: &Ty) -> IrTy {
        match ty {
            Ty::Tuple(TupleTy { data }) => {
                let mut flags = AdtFlags::empty();
                flags |= AdtFlags::TUPLE;

                // Convert the single variant into the tuple variant.
                let variant = self.stores().params().map_fast(*data, |entries| {
                    let fields = entries.iter().map(|field| self.ty_id_from_tir_ty(field.ty));

                    AdtVariant {
                        name: "0".into(),
                        fields: fields
                            .enumerate()
                            .map(|(index, ty)| AdtField { name: index.into(), ty })
                            .collect(),
                    }
                });

                let adt = AdtData::new_with_flags("tuple".into(), index_vec![variant], flags);
                let id = self.lcx.adts().create(adt);
                IrTy::Adt(id)
            }
            Ty::Fn(FnTy { params, return_ty, .. }) => {
                let params = self.stores().params().map_fast(*params, |params| {
                    self.lcx.tls().create_from_iter(
                        params.iter().map(|param| self.ty_id_from_tir_ty(param.ty)),
                    )
                });

                let return_ty = self.ty_id_from_tir_ty(*return_ty);
                IrTy::Fn { params, return_ty }
            }
            Ty::Ref(RefTy { kind, mutable, ty }) => {
                let ty = self.ty_id_from_tir_ty(*ty);
                let mutability = if *mutable { Mutability::Mutable } else { Mutability::Immutable };
                let ref_kind = match kind {
                    hash_tir::refs::RefKind::Rc => ty::RefKind::Rc,
                    hash_tir::refs::RefKind::Raw => ty::RefKind::Raw,
                    hash_tir::refs::RefKind::Local => ty::RefKind::Normal,
                };

                IrTy::Ref(ty, mutability, ref_kind)
            }
            Ty::Data(data_ty) => self.ty_from_tir_data(*data_ty),
            Ty::Eval(_) | Ty::Universe(_) => IrTy::Adt(AdtId::UNIT),

            Ty::Var(sym) => {
                let value = self.context_utils().get_binding_value(*sym);
                self.ty_from_tir_ty_id(self.use_term_as_ty(value))
            }
            ty @ Ty::Hole(_) => {
                let message = format!(
                    "all types should be monomorphised before lowering, type: `{}`",
                    self.env().with(ty)
                );

                if let Some(location) = self.get_location(id) {
                    panic_on_span!(location, self.source_map(), format!("{message}"))
                } else {
                    panic!("{message}")
                }
            }
        }
    }

    /// Convert the [DataTy] into an [`IrTy::Adt`]. The [DataTy] specifies a
    /// data definition and a collection of arguments to the data
    /// definition. The arguments correspond to generic parameters that the
    /// definition has.
    pub(crate) fn ty_id_from_tir_data(&self, data_ty: DataTy) -> IrTyId {
        // Check if the data type has already been converted into
        // an ir type.
        let key = data_ty.into();
        if let Some(ty) = self.lcx.semantic_cache().borrow().get(&key) {
            return *ty;
        }

        let ty = self.ty_from_tir_data(data_ty);
        let id = self.lcx.tys().create(ty);

        // Add an entry into the cache for this term
        self.lcx.semantic_cache().borrow_mut().insert(key, id);
        id
    }

    fn create_data_def(&self, DataTy { data_def, .. }: DataTy) -> IrTy {
        let data_ty = self.get_data_def(data_def);

        match data_ty.ctors {
            DataDefCtors::Defined(ctor_defs) => {
                // If data_def has more than one constructor, then it is assumed that this
                // is a enum.
                let mut flags = AdtFlags::empty();

                match ctor_defs.len() {
                    0 => return IrTy::Never, // This must be the never type.
                    1 => flags |= AdtFlags::STRUCT,
                    _ => flags |= AdtFlags::ENUM,
                }

                // Lower each variant as a constructor.
                let variants = self.stores().ctor_defs().map_fast(ctor_defs, |defs| {
                    defs.iter()
                        .map(|ctor| {
                            let name = self.get_symbol(ctor.name).name.unwrap_or(IDENTS.underscore);

                            self.stores().params().map_fast(ctor.params, |fields| {
                                let fields = fields
                                    .iter()
                                    .map(|field| {
                                        let ty = self.ty_id_from_tir_ty(field.ty);
                                        let name = self
                                            .get_symbol(field.name)
                                            .name
                                            .unwrap_or(IDENTS.underscore);

                                        AdtField { name, ty }
                                    })
                                    .collect::<Vec<_>>();

                                AdtVariant { name, fields }
                            })
                        })
                        .collect::<AdtVariants>()
                });

                // Get the name of the data type, if no name exists we default to
                // using `_`.
                let name = self.get_symbol(data_ty.name).name.unwrap_or(IDENTS.underscore);
                let mut adt = AdtData::new_with_flags(name, variants, flags);

                // Deal with any specific attributes that were set on the type, i.e.
                // `#repr_c`.
                if let Some(directives) = self.stores().directives().get(data_def.into()) {
                    if directives.contains(IDENTS.repr_c) {
                        adt.metadata.add_flags(RepresentationFlags::C_LIKE);
                    }
                }

                let id = self.lcx.adts().create(adt);
                IrTy::Adt(id)
            }

            // Primitive are numerics, strings, arrays, etc.
            DataDefCtors::Primitive(primitive) => {
                match primitive {
                    PrimitiveCtorInfo::Numeric(NumericCtorInfo { bits, is_signed, is_float }) => {
                        if is_float {
                            match bits {
                                NumericCtorBits::Bounded(32) => IrTy::Float(FloatTy::F32),
                                NumericCtorBits::Bounded(64) => IrTy::Float(FloatTy::F64),

                                // Other bits widths are not supported.
                                _ => unreachable!(),
                            }
                        } else {
                            match bits {
                                NumericCtorBits::Bounded(bits) => {
                                    let size = Size::from_bits(bits);

                                    if is_signed {
                                        IrTy::Int(SIntTy::from_size(size))
                                    } else {
                                        IrTy::UInt(UIntTy::from_size(size))
                                    }
                                }
                                // We don't implement bigints yet
                                _ => unimplemented!(),
                            }
                        }
                    }

                    // @@Verify: does `str` now imply that it is a `&str`, or should we create a
                    // `&str` type here.
                    PrimitiveCtorInfo::Str => IrTy::Str,
                    PrimitiveCtorInfo::Char => IrTy::Char,
                    PrimitiveCtorInfo::Array(ArrayCtorInfo { element_ty, length }) => {
                        match length.and_then(|l| self.try_use_term_as_integer_lit(l)) {
                            Some(length) => {
                                IrTy::Array { ty: self.ty_id_from_tir_ty(element_ty), length }
                            }
                            None => IrTy::Slice(self.ty_id_from_tir_ty(element_ty)),
                        }
                    }
                }
            }
        }
    }

    /// Convert the [DataDefType] into an [`IrTy::Adt`].
    fn ty_from_tir_data(&self, ty: DataTy) -> IrTy {
        // If the data type is a primitive boolean, then return the boolean type.
        if ty.data_def == self.primitives().bool() {
            return IrTy::Bool;
        }

        // Apply the arguments as the scope of the data type.
        let kind = ty.data_def.into();
        let data_params = self.stores().data_def().map_fast(ty.data_def, |data| data.params);

        self.context().enter_scope(kind, || {
            self.context_utils().add_arg_bindings(data_params, ty.args);
            self.create_data_def(ty)
        })
    }
}
