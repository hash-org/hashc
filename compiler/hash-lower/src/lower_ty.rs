//! Contains all of the logic that is used by the lowering process
//! to convert types and [Ty]s into [IrTy]s.

use hash_intrinsics::{primitives::primitives, utils::PrimitiveUtils};
use hash_ir::{
    intrinsics::Intrinsic,
    lang_items::LangItem,
    ty::{
        self, Adt, AdtField, AdtFlags, AdtId, AdtVariant, AdtVariants, Instance, IrTy, IrTyId,
        IrTyListId, Mutability, COMMON_IR_TYS,
    },
    TyCacheEntry,
};
use hash_reporting::macros::panic_on_span;
use hash_storage::store::{
    statics::{SingleStoreValue, StoreId},
    SequenceStoreKey,
};
use hash_target::size::Size;
use hash_tir::{
    data::{
        ArrayCtorInfo, CtorDefsId, DataDef, DataDefCtors, DataTy, NumericCtorBits, NumericCtorInfo,
        PrimitiveCtorInfo,
    },
    environment::env::AccessToEnv,
    fns::{FnDef, FnDefId, FnTy},
    refs::RefTy,
    tuples::TupleTy,
    tys::{Ty, TyId},
    utils::common::get_location,
};
use hash_utils::{index_vec::index_vec, itertools::Itertools};

use crate::ctx::BuilderCtx;

impl<'ir> BuilderCtx<'ir> {
    /// Perform a type lowering operation whilst also caching the result of the
    /// lowering operation. This is used to avoid duplicated work when lowering
    /// types.
    fn with_cache<T>(&self, item: T, f: impl FnOnce() -> (IrTyId, bool)) -> IrTyId
    where
        T: Copy + Into<TyCacheEntry>,
    {
        // Check if the term is present within the cache, and if so, return the
        // cached value.
        if let Some(ty) = self.lcx.ty_cache().borrow().get(&item.into()) {
            return *ty;
        }

        // Create the new type
        let (ty, add_to_cache) = f();

        // If the function returned true, then this means that it has dealt with
        // adding the item into the cache, and we can skip it here. This is to allow
        // for recursive type definitions to be lowered.
        if add_to_cache {
            self.lcx.ty_cache().borrow_mut().insert(item.into(), ty);
        }

        ty
    }

    /// Get the [IrTyId] from a given [TyId]. This function will internally
    /// cache results of lowering a [TyId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(crate) fn ty_id_from_tir_ty(&self, id: TyId) -> IrTyId {
        self.with_cache(id, || {
            let ty = id.borrow();
            // We compute the "uncached" type, and then it will be added to the
            // cache if it is not already present. For data types, since they can
            // be defined in a recursive way, the `ty_from_tir_data` will deal with
            // its own caching, but we still want to add an entry here for `TyId` since
            // we want to avoid computing the `ty_from_tir_data` as well.
            let result = match &*ty {
                Ty::Data(data_ty) => self.ty_from_tir_data(*data_ty),

                // Hot path for unit types.
                Ty::Tuple(tuple) if tuple.data.is_empty() => COMMON_IR_TYS.unit,
                _ => self.uncached_ty_from_tir_ty(id, &ty),
            };

            (result, false)
        })
    }

    /// Get the [IrTy] from the given [Ty].
    fn uncached_ty_from_tir_ty(&self, id: TyId, ty: &Ty) -> IrTyId {
        let ty = match *ty {
            Ty::Tuple(TupleTy { data }) => {
                // Optimise, if this is a UNIT, then we can just return a unit type.
                if data.is_empty() {
                    return COMMON_IR_TYS.unit;
                }

                let mut flags = AdtFlags::empty();
                flags |= AdtFlags::TUPLE;

                // Convert the single variant into the tuple variant.
                let fields = data
                    .borrow()
                    .iter()
                    .map(|field| self.ty_id_from_tir_ty(field.ty))
                    .enumerate()
                    .map(|(index, ty)| AdtField { name: index.into(), ty })
                    .collect();
                let variant = AdtVariant { name: "0".into(), fields };

                let adt = Adt::new_with_flags("tuple".into(), index_vec![variant], flags);
                IrTy::Adt(Adt::create(adt))
            }
            Ty::Fn(FnTy { params, return_ty, .. }) => {
                let params = IrTyListId::seq(
                    params.borrow().iter().map(|param| self.ty_id_from_tir_ty(param.ty)),
                );
                let return_ty = self.ty_id_from_tir_ty(return_ty);
                IrTy::Fn { params, return_ty }
            }
            Ty::Ref(RefTy { kind, mutable, ty }) => {
                let ty = self.ty_id_from_tir_ty(ty);
                let mutability = if mutable { Mutability::Mutable } else { Mutability::Immutable };
                let ref_kind = match kind {
                    hash_tir::refs::RefKind::Rc => ty::RefKind::Rc,
                    hash_tir::refs::RefKind::Raw => ty::RefKind::Raw,
                    hash_tir::refs::RefKind::Local => ty::RefKind::Normal,
                };

                IrTy::Ref(ty, mutability, ref_kind)
            }
            Ty::Data(data_ty) => return self.ty_from_tir_data(data_ty),
            Ty::Eval(_) | Ty::Universe(_) => IrTy::Adt(AdtId::UNIT),

            // This is a type variable that should be found in the scope. It is
            // resolved and substituted in the `Ty::Var` case below.
            Ty::Var(sym) => {
                // @@Temporary
                if self.context().try_get_decl(sym).is_some() {
                    let term = self.context().get_binding_value(sym);
                    let ty = term.as_ty().value();
                    return self.uncached_ty_from_tir_ty(id, &ty);
                } else {
                    return COMMON_IR_TYS.unit; // We just return the unit type
                                               // for now.
                }
            }
            ty @ Ty::Hole(_) => {
                let message =
                    format!("all types should be monomorphised before lowering, type: `{}`", ty);

                if let Some(location) = get_location(id) {
                    panic_on_span!(location, self.source_map(), format!("{message}"))
                } else {
                    panic!("{message}")
                }
            }
        };

        IrTy::create(ty)
    }

    /// Create a new [IrTyId] from the given function definition whilst
    /// caching the result in the
    pub(crate) fn ty_id_from_tir_fn_def(&self, def: FnDefId) -> IrTyId {
        self.with_cache(def, || {
            let instance = self.create_instance_from_fn_def(def);

            let is_lang = instance.attributes.contains("lang".into());
            let name = instance.name();

            // Check if the instance has the `lang` attribute, specifying that it is
            // the lang-item attribute.
            let instance = Instance::create(instance);
            let ty = IrTy::create(IrTy::FnDef { instance });

            if is_lang {
                let item = LangItem::from_str_name(name.into());
                self.lcx.lang_items_mut().set(item, instance, ty);
            }

            // Specify here that the function might be an intrinsic function
            if def.borrow().is_intrinsic() {
                let item =
                    Intrinsic::from_str_name(name.into()).expect("unknown intrinsic function");
                self.lcx.intrinsics_mut().set(item, instance, ty);
            }

            (ty, true)
        })
    }

    /// Create a [Instance] from a [FnDefId]. This represents the function
    // / instance including the name, types (monomorphised), and attributes
    /// that are associated with the function definition.
    fn create_instance_from_fn_def(&self, fn_def: FnDefId) -> Instance {
        let FnDef { name, ty, .. } = fn_def.value();

        // Check whether this is an intrinsic item, since we need to handle
        // them differently

        let source = get_location(fn_def).map(|location| location.id);
        let FnTy { params, return_ty, .. } = ty;

        let params =
            IrTyListId::seq(params.borrow().iter().map(|param| self.ty_id_from_tir_ty(param.ty)));
        let ret_ty = self.ty_id_from_tir_ty(return_ty);

        let ident = name.ident();
        let mut instance = Instance::new(ident, source, params, ret_ty);

        // Lookup any applied directives on the fn_def and add them to the
        // instance

        // @@ReAddDirectives: we should access the new attributes stuff later...
        // tir_stores().directives().map_fast(fn_def.into(), |maybe_directives| {
        //     if let Some(directives) = maybe_directives {
        //         for directive in directives.iter() {
        //             instance.attributes.add(Attribute::word(directive));
        //         }
        //     }
        // });

        if Intrinsic::from_str_name(ident.into()).is_some() {
            instance.is_intrinsic = true;
        }

        instance
    }

    /// Convert the [DataTy] into an [`IrTy::Adt`]. The [DataTy] specifies a
    /// data definition and a collection of arguments to the data
    /// definition. The arguments correspond to generic parameters that the
    /// definition has.
    pub(crate) fn ty_from_tir_data(&self, data_ty: DataTy) -> IrTyId {
        self.with_cache(data_ty, || self.uncached_ty_from_tir_data(data_ty))
    }

    /// Function to convert a data definition into a [`IrTy::Adt`].
    ///
    /// This function that will create a [IrTy] and save it into the
    /// `reserved_ty` slot.
    fn adt_ty_from_data(&self, ty: DataTy, def: &DataDef, ctor_defs: CtorDefsId) -> (IrTyId, bool) {
        // If data_def has more than one constructor, then it is assumed that this
        // is a enum.
        let mut flags = AdtFlags::empty();

        match ctor_defs.len() {
            // This must be the never type.
            0 => {
                return (COMMON_IR_TYS.never, false);
            }
            1 => flags |= AdtFlags::STRUCT,
            _ => flags |= AdtFlags::ENUM,
        }

        // Reserve a type slot for the data type, and add it to the cache
        // so that if any inner types are recursive, they can refer to
        // this type, and it will be updated once the type is fully defined.
        // Apply the arguments as the scope of the data type.
        let reserved_ty = IrTy::create(IrTy::Never);
        self.lcx.ty_cache().borrow_mut().insert(ty.into(), reserved_ty);

        // We want to add the arguments to the ADT, so that we can print them
        // out when the type is being displayed.
        let subs = if ty.args.len() > 0 {
            // For each argument, we lookup the value of the argument, lower it as a
            // type and create a TyList for the subs.
            Some(IrTyListId::seq(ty.args.borrow().iter().map(|arg| {
                let ty = arg.value.as_ty();
                self.ty_id_from_tir_ty(ty)
            })))
        } else {
            None
        };

        // Lower each variant as a constructor.
        let variants = ctor_defs
            .borrow()
            .iter()
            .map(|ctor| {
                let fields = ctor
                    .params
                    .borrow()
                    .iter()
                    .enumerate()
                    .map(|(index, field)| AdtField {
                        name: field.name.borrow().name.unwrap_or(index.into()),
                        ty: self.ty_id_from_tir_ty(field.ty),
                    })
                    .collect_vec();

                AdtVariant { name: ctor.name.ident(), fields }
            })
            .collect::<AdtVariants>();

        // Get the name of the data type, if no name exists we default to
        // using `_`.
        let mut adt = Adt::new_with_flags(def.name.ident(), variants, flags);
        adt.substitutions = subs;

        // Deal with any specific attributes that were set on the type, i.e.
        // `#repr_c`.
        //
        // @@ReAddDirectives: check whether this has `repr(c)` on it.
        //
        // if let Some(directives) = tir_stores().directives().get(def.id.into()) {
        //     if directives.contains(IDENTS.repr_c) {
        //         adt.metadata.add_flags(RepresentationFlags::C_LIKE);
        //     }
        // }

        // Update the type in the slot that was reserved for it.
        reserved_ty.modify(|ty| *ty = IrTy::Adt(Adt::create(adt)));

        // We created our own cache entry, so we don't need to update the
        // cache.
        (reserved_ty, true)
    }

    /// Function that converts a [DataTy] into the corresponding [IrTyId].
    fn uncached_ty_from_tir_data(&self, ty: DataTy) -> (IrTyId, bool) {
        let data_def = ty.data_def.value();

        match data_def.ctors {
            DataDefCtors::Defined(ctor_defs) => {
                // Booleans are defined as a data type with two constructors,
                // check here if we are dealing with a boolean.
                if primitives().bool() == ty.data_def {
                    return (COMMON_IR_TYS.bool, true);
                }

                self.context().enter_scope(ty.data_def.into(), || {
                    self.context().add_arg_bindings(data_def.params, ty.args);
                    self.adt_ty_from_data(ty, &data_def, ctor_defs)
                })
            }

            // Primitive are numerics, strings, arrays, etc.
            DataDefCtors::Primitive(primitive) => {
                let ty = match primitive {
                    PrimitiveCtorInfo::Numeric(NumericCtorInfo { bits, is_signed, is_float }) => {
                        if is_float {
                            match bits {
                                NumericCtorBits::Bounded(32) => COMMON_IR_TYS.f32,
                                NumericCtorBits::Bounded(64) => COMMON_IR_TYS.f64,

                                // Other bits widths are not supported.
                                _ => unreachable!(),
                            }
                        } else {
                            match bits {
                                NumericCtorBits::Bounded(bits) => {
                                    let size = Size::from_bits(bits);

                                    if is_signed {
                                        match size.bytes() {
                                            1 => COMMON_IR_TYS.i8,
                                            2 => COMMON_IR_TYS.i16,
                                            4 => COMMON_IR_TYS.i32,
                                            8 => COMMON_IR_TYS.i64,
                                            16 => COMMON_IR_TYS.i128,
                                            _ => unreachable!(), /* Other bits widths are not
                                                                  * supported. */
                                        }
                                    } else {
                                        match size.bytes() {
                                            1 => COMMON_IR_TYS.u8,
                                            2 => COMMON_IR_TYS.u16,
                                            4 => COMMON_IR_TYS.u32,
                                            8 => COMMON_IR_TYS.u64,
                                            16 => COMMON_IR_TYS.u128,
                                            _ => unreachable!(), /* Other bits widths are not
                                                                  * supported. */
                                        }
                                    }
                                }
                                _ => unimplemented!(), // We don't implement big-ints yet
                            }
                        }
                    }

                    // @@Temporary: `str` implies that it is a `&str`
                    PrimitiveCtorInfo::Str => COMMON_IR_TYS.str,
                    PrimitiveCtorInfo::Char => COMMON_IR_TYS.char,
                    PrimitiveCtorInfo::Array(ArrayCtorInfo { element_ty, length }) => {
                        // Apply the arguments as the scope of the data type.
                        self.context().enter_scope(ty.data_def.into(), || {
                            self.context().add_arg_bindings(data_def.params, ty.args);

                            let ty = match length.and_then(|l| self.try_use_term_as_integer_lit(l))
                            {
                                Some(length) => {
                                    IrTy::Array { ty: self.ty_id_from_tir_ty(element_ty), length }
                                }
                                // @@Temporary: `[]` implies that it is a `&[]`, and there is no
                                // information about mutability and reference kind, so for now we
                                // assume that it is immutable and a normal reference kind.
                                None => {
                                    let slice = IrTy::Slice(self.ty_id_from_tir_ty(element_ty));
                                    IrTy::Ref(
                                        IrTy::create(slice),
                                        Mutability::Immutable,
                                        ty::RefKind::Normal,
                                    )
                                }
                            };

                            IrTy::create(ty)
                        })
                    }
                };

                // Since we don't do anything with the cache, we can specify that
                // the result of the operation should be cached.
                (ty, true)
            }
        }
    }
}
