//! Contains all of the logic that is used by the lowering process
//! to convert types and [Ty]s into [IrTy]s.

use hash_intrinsics::{primitives::AccessToPrimitives, utils::PrimitiveUtils};
use hash_ir::{
    intrinsics::Intrinsic,
    lang_items::LangItem,
    ty::{
        self, AdtData, AdtField, AdtFlags, AdtId, AdtVariant, AdtVariants, Instance, IrTy, IrTyId,
        Mutability, RepresentationFlags,
    },
};
use hash_reporting::macros::panic_on_span;
use hash_source::{
    attributes::Attribute,
    constant::{FloatTy, SIntTy, UIntTy},
    identifier::IDENTS,
};
use hash_target::size::Size;
use hash_tir::{
    data::{
        ArrayCtorInfo, DataDefCtors, DataTy, NumericCtorBits, NumericCtorInfo, PrimitiveCtorInfo,
    },
    environment::env::AccessToEnv,
    fns::{FnDef, FnDefId, FnTy},
    refs::RefTy,
    tuples::TupleTy,
    tys::{Ty, TyId},
    utils::{common::CommonUtils, AccessToUtils},
};
use hash_utils::{
    index_vec::index_vec,
    log::info,
    store::{CloneStore, PartialCloneStore, PartialStore, SequenceStore, SequenceStoreKey, Store},
};

use crate::ctx::BuilderCtx;

impl<'ir> BuilderCtx<'ir> {
    /// Get the [IrTyId] from a given [TyId]. This function will internally
    /// cache results of lowering a [TyId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(crate) fn ty_id_from_tir_ty(&self, id: TyId) -> IrTyId {
        // Check if the term is present within the cache, and if so, return the
        // cached value.
        if let Some(ty) = self.lcx.ty_cache().borrow().get(&id.into()) {
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
            IrTy::Str => self.lcx.tys().common_tys.str,
            _ => self.lcx.tys().create(ty),
        };

        // Lower the type into ir type.
        self.map_ty(id, |ty| {
            if let Ty::Data(data_ty) = ty {
                let data_ty = *data_ty;

                if let Some(ty) = self.lcx.ty_cache().borrow().get(&data_ty.into()) {
                    return *ty;
                }

                // Convert the data-type into an ir type, cache it and return it
                let ty = create_new_ty(self.ty_from_tir_data(data_ty));

                // Add entries for both the data type and the type id.
                let mut cache = self.lcx.ty_cache().borrow_mut();
                cache.insert(data_ty.into(), ty);
                cache.insert(id.into(), ty);

                ty
            } else {
                // Add an entry into the cache for this term
                let ty = create_new_ty(self.ty_from_tir_ty(id, ty));
                self.lcx.ty_cache().borrow_mut().insert(id.into(), ty);
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
                // @@Temporary
                if self.context().try_get_binding(*sym).is_some() {
                    let term = self.context_utils().get_binding_value(*sym);
                    self.ty_from_tir_ty_id(self.use_term_as_ty(term))
                } else {
                    info!("couldn't resolve type variable `{}`", self.env().with(*sym));

                    // We just return the unit type for now.
                    IrTy::Adt(AdtId::UNIT)
                }
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

    /// Create a new [IrTyId] from the given function definition whilst
    /// caching the result in the
    pub(crate) fn ty_id_from_tir_fn_def(&self, def: FnDefId) -> IrTyId {
        // Check if we have already lowered this function definition, and
        // if so we can just return the cached value.
        if let Some(ty) = self.lcx.ty_cache().borrow().get(&def.into()) {
            return *ty;
        }

        let instance = self.create_instance_from_fn_def(def);

        let is_lang = instance.attributes.contains("lang".into());
        let name = instance.name();

        // Check if the instance has the `lang` attribute, specifying that it is
        // the lang-item attribute.
        let instance = self.lcx.instances().create(instance);
        let ty = self.lcx.tys().create(IrTy::FnDef { instance });

        if is_lang {
            let item = LangItem::from_str_name(name.into());
            self.lcx.lang_items_mut().set(item, instance, ty);
        }

        // Specify here that the function might be an intrinsic function
        if self.stores().fn_def().map_fast(def, |def| def.is_intrinsic()) {
            let item = Intrinsic::from_str_name(name.into()).expect("unknown intrinsic function");
            self.lcx.intrinsics_mut().set(item, instance, ty);
        }

        // Save in the cache that the definition has been lowered.
        self.lcx.ty_cache().borrow_mut().insert(def.into(), ty);
        ty
    }

    /// Create a [Instance] from a [FnDefId]. This represents the function
    /// instance including the name, types (monormorphised), and attributes
    /// that are associated with the function definition.
    fn create_instance_from_fn_def(&self, fn_def: FnDefId) -> Instance {
        let FnDef { name, ty, .. } = self.env().stores().fn_def().get(fn_def);

        let name = self.env().symbol_name(name);

        // Check whether this is an intrinsic item, since we need to handle
        // them differently

        let source = self.get_location(fn_def).map(|location| location.id);
        let FnTy { params, return_ty, .. } = ty;

        // Lower the parameters and the return type
        let param_tys = self.stores().params().get_vec(params);

        let params = self
            .lcx
            .tls()
            .create_from_iter(param_tys.iter().map(|param| self.ty_id_from_tir_ty(param.ty)));
        let ret_ty = self.ty_id_from_tir_ty(return_ty);

        let mut instance = Instance::new(name, source, params, ret_ty);

        // Lookup any applied directives on the fn_def and add them to the
        // instance
        self.env().stores().directives().map_fast(fn_def.into(), |maybe_directives| {
            if let Some(directives) = maybe_directives {
                for directive in directives.iter() {
                    instance.attributes.add(Attribute::word(directive));
                }
            }
        });

        if Intrinsic::from_str_name(name.into()).is_some() {
            instance.is_intrinsic = true;
        }

        instance
    }

    /// Convert the [DataTy] into an [`IrTy::Adt`]. The [DataTy] specifies a
    /// data definition and a collection of arguments to the data
    /// definition. The arguments correspond to generic parameters that the
    /// definition has.
    pub(crate) fn ty_id_from_tir_data(&self, data_ty: DataTy) -> IrTyId {
        // Check if the data type has already been converted into
        // an ir type.
        let key = data_ty.into();
        if let Some(ty) = self.lcx.ty_cache().borrow().get(&key) {
            return *ty;
        }

        let ty = self.ty_from_tir_data(data_ty);
        let id = self.lcx.tys().create(ty);

        // Add an entry into the cache for this term
        self.lcx.ty_cache().borrow_mut().insert(key, id);
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

                    // @@Temporary: `str` implies that it is a `&str`
                    PrimitiveCtorInfo::Str => IrTy::Ref(
                        self.lcx.tys().common_tys.byte_slice,
                        Mutability::Immutable,
                        ty::RefKind::Normal,
                    ),
                    PrimitiveCtorInfo::Char => IrTy::Char,
                    PrimitiveCtorInfo::Array(ArrayCtorInfo { element_ty, length }) => {
                        match length.and_then(|l| self.try_use_term_as_integer_lit(l)) {
                            Some(length) => {
                                IrTy::Array { ty: self.ty_id_from_tir_ty(element_ty), length }
                            }
                            // @@Temporary: `[]` implies that it is a `&[]`, and there is no
                            // information about mutability and reference kind, so for now we
                            // assume that it is immutable and a normal reference kind.
                            None => {
                                let slice = IrTy::Slice(self.ty_id_from_tir_ty(element_ty));
                                let id = self.lcx.tys().create(slice);

                                IrTy::Ref(id, Mutability::Immutable, ty::RefKind::Normal)
                            }
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
