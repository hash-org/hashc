//! Contains all of the logic that is used by the lowering process
//! to convert types and [Ty]s into [IrTy]s.
#![allow(dead_code, unused)] // @@Temporary

use hash_ir::{
    ty::{
        self, AdtData, AdtField, AdtFlags, AdtId, AdtVariant, AdtVariants, Instance, IrTy, IrTyId,
        Mutability,
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
        ArrayCtorInfo, DataDefCtors, DataDefId, DataTy, NumericCtorBits, NumericCtorInfo,
        PrimitiveCtorInfo,
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
}

impl<'ir> AccessToEnv for TyLoweringCtx<'ir> {
    fn env(&self) -> &Env {
        todo!()
    }
}

impl<'ir> TyLoweringCtx<'ir> {
    /// Create a new [TyLoweringCtx] from the given [IrCtx] and [GlobalStorage].
    pub fn new(lcx: &'ir IrCtx) -> Self {
        Self { lcx }
    }

    /// Get the [IrTyId] from a given [TyId]. This function will internally
    /// cache results of lowering a [TyId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(crate) fn ty_id_from_tir_ty(&self, term: TyId) -> IrTyId {
        todo!()
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

                // @@Todo: functions should have a name if possible, otherwise they default
                // to an underscore.
                let name = IDENTS.underscore;
                let source = None;

                let instance = Instance::new(name, source, params, return_ty);
                let id = self.lcx.instances().create(instance);

                IrTy::Fn { instance: id, params, return_ty }
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
    pub(crate) fn ty_id_from_tir_data(&self, data: DataDefId) -> IrTyId {
        todo!()
    }

    /// Convert the [DataDefType] into an [`IrTy::Adt`].
    fn ty_from_tir_data(&self, DataTy { data_def, args: _ }: DataTy) -> IrTy {
        let data_ty = self.get_data_def(data_def);

        match data_ty.ctors {
            DataDefCtors::Defined(ctor_defs) => {
                // If data_def has more than one constructor, then it is assumed that this
                // is a enum.
                let mut flags = AdtFlags::empty();

                if ctor_defs.len() > 1 {
                    flags |= AdtFlags::ENUM;
                } else if ctor_defs.len() == 1 {
                    flags |= AdtFlags::STRUCT;
                } else {
                    // This must be the never type.
                    return IrTy::Never;
                }

                // @@Todo: Deal with performing generics on the types here...

                // Lower each variant as a constructor.
                let variants = self.stores().ctor_defs().map_fast(ctor_defs, |defs| {
                    defs.into_iter()
                        .map(|ctor| {
                            self.stores().params().map_fast(ctor.params, |fields| {
                                let fields = fields
                                    .iter()
                                    .map(|field| {
                                        let ty = self.ty_id_from_tir_ty(field.ty);

                                        // @@Todo: convert symbol into an ident.
                                        let name = IDENTS.underscore;
                                        // @@Todo: do we need to store default parameter information
                                        // here?
                                        AdtField { name, ty }
                                    })
                                    .collect::<Vec<_>>();

                                // @@Todo: convert symbol into an ident.
                                let name = IDENTS.underscore;
                                AdtVariant { name, fields }
                            })
                        })
                        .collect::<AdtVariants>()
                });

                // @@Todo: conver `data_ty.name` from a `Symbol` into an ident.
                let name = IDENTS.underscore;
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
