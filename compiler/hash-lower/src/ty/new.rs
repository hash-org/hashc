//! Contains all of the logic that is used by the lowering process
//! to convert types and [Ty]s into [IrTy]s.
#![allow(dead_code)] // @@Temporary.

use hash_ir::{
    ty::{
        self, AdtData, AdtField, AdtFlags, AdtId, AdtVariant, AdtVariants, IrTy, IrTyId, Mutability,
    },
    IrCtx,
};
use hash_source::{
    constant::{FloatTy, SIntTy, UIntTy},
    identifier::IDENTS,
};
use hash_target::size::Size;
use hash_tir::new::{
    data::{
        ArrayCtorInfo, DataDefCtors, DataTy, NumericCtorBits, NumericCtorInfo, PrimitiveCtorInfo,
    },
    environment::env::{AccessToEnv, Env},
    fns::FnTy,
    refs::RefTy,
    tuples::TupleTy,
    tys::{Ty, TyId},
    utils::common::CommonUtils,
};
use hash_utils::{
    index_vec::index_vec,
    store::{SequenceStore, SequenceStoreKey, Store},
};

/// A context that is used to lower types and terms into [IrTy]s.
pub(crate) struct TyLoweringCtx<'ir> {
    /// A reference to the store of all of the IR types.
    pub lcx: &'ir IrCtx,

    /// The type storage from the semantic analysis stage.
    pub tcx: Env<'ir>,
}

impl<'ir> AccessToEnv for TyLoweringCtx<'ir> {
    fn env(&self) -> &Env {
        &self.tcx
    }
}

impl<'ir> TyLoweringCtx<'ir> {
    /// Create a new [TyLoweringCtx] from the given [IrCtx] and [GlobalStorage].
    pub fn new(lcx: &'ir IrCtx, tcx: Env<'ir>) -> Self {
        Self { lcx, tcx }
    }

    /// Get the [IrTyId] from a given [TyId]. This function will internally
    /// cache results of lowering a [TyId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(crate) fn ty_id_from_tir_ty(&self, term: TyId) -> IrTyId {
        // Check if the term is present within the cache, and if so, return the
        // cached value.
        if let Some(ty) = self.lcx.semantic_cache().borrow().get(&term.into()) {
            return *ty;
        }

        // Lower the type into ir type.
        let ty = self.map_ty(term, |ty| self.ty_from_tir_ty(ty));

        // @@Hack: avoid re-creating "commonly" used types in order
        // to allow for type_id equality to work
        let id = match ty {
            IrTy::Char => self.lcx.tys().common_tys.char,
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

        // Add an entry into the cache for this term
        self.lcx.semantic_cache().borrow_mut().insert(term.into(), id);
        id
    }

    /// Get the [IrTy] from the given [TyId].
    fn ty_from_tir_ty(&self, ty: &Ty) -> IrTy {
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
                    hash_tir::new::refs::RefKind::Rc => ty::RefKind::Rc,
                    hash_tir::new::refs::RefKind::Raw => ty::RefKind::Raw,
                    hash_tir::new::refs::RefKind::Local => ty::RefKind::Normal,
                };

                IrTy::Ref(ty, mutability, ref_kind)
            }
            Ty::Data(data_ty) => self.ty_from_tir_data(*data_ty),
            Ty::Eval(_) | Ty::Universe(_) => IrTy::Adt(AdtId::UNIT),
            Ty::Hole(_) | Ty::Var(_) => panic!("all types should be monomorphised before lowering"),
        }
    }

    /// Convert the [DataDefType] into an [`IrTy::Adt`].
    pub(crate) fn ty_id_from_tir_data(&self, data @ DataTy { data_def, args }: DataTy) -> IrTyId {
        // Check if the data type has already been converted into
        // an [IrTyId].
        if let Some(ty) = self.lcx.semantic_cache().borrow().get(&data.into()) {
            return *ty;
        }

        let ty = self.ty_from_tir_data(DataTy { data_def, args });
        let id = self.lcx.tys().create(ty);

        // Add an entry into the cache for this term
        self.lcx.semantic_cache().borrow_mut().insert(data.into(), id);
        id
    }

    /// Convert the [DataDefType] into an [`IrTy::Adt`].
    fn ty_from_tir_data(&self, DataTy { data_def, args: _ }: DataTy) -> IrTy {
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

                // @@Todo: Deal with performing generics on the types here...

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
                let adt = AdtData::new_with_flags(name, variants, flags);

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
                        IrTy::Array { ty: self.ty_id_from_tir_ty(element_ty), length }
                    }
                }
            }
        }
    }
}