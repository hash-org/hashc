//! Contains all of the logic that is used by the lowering process
//! to convert types and [Ty]s into [IrTy]s.

use hash_ast::ast::AstNodeId;
use hash_attrs::builtin::attrs;
use hash_ir::{
    intrinsics::Intrinsic,
    lang_items::LangItem,
    ty::{
        self, Adt, AdtField, AdtFlags, AdtId, AdtVariant, AdtVariants, Instance, IrTy, IrTyId,
        IrTyListId, Mutability, VariantDiscriminant, COMMON_IR_TYS,
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
    context::HasContext,
    intrinsics::{
        definitions::{bool_def, Intrinsic as TirIntrinsic},
        make::IsIntrinsic,
        utils::try_use_term_as_integer_lit,
    },
    tir::{
        ArrayCtorInfo, CtorDefsId, DataDef, DataDefCtors, DataTy, FnDef, FnDefId, FnTy,
        HasAstNodeId, NodesId, NumericCtorBits, NumericCtorInfo, PrimitiveCtorInfo, RefTy, TupleTy,
        Ty, TyId,
    },
};
use hash_utils::{index_vec::index_vec, itertools::Itertools};

use crate::ctx::BuilderCtx;

/// A flag specifying whether a type lowering from TIR types to IR types
/// should be cached or not.
#[derive(PartialEq, Eq)]
enum ShouldCache {
    Yes,
    No,
}

impl<'ir> BuilderCtx<'ir> {
    /// Perform a type lowering operation whilst also caching the result of the
    /// lowering operation. This is used to avoid duplicated work when lowering
    /// types.
    fn with_cache<T>(&self, item: T, f: impl FnOnce() -> (IrTyId, ShouldCache)) -> IrTyId
    where
        T: Copy + Into<TyCacheEntry>,
    {
        // Check if the term is present within the cache, and if so, return the
        // cached value.
        if let Some(ty) = self.lcx.ty_cache().borrow().get(&item.into()) {
            return *ty;
        }

        // Create the new type
        let (ty, should_cache) = f();

        // If the function returned true, then this means that it has dealt with
        // adding the item into the cache, and we can skip it here. This is to allow
        // for recursive type definitions to be lowered.
        if should_cache == ShouldCache::Yes {
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
            let result = match &(*ty).data {
                Ty::DataTy(data_ty) => self.ty_from_tir_data(*data_ty),

                // Hot path for unit types.
                Ty::TupleTy(tuple) if tuple.data.is_empty() => COMMON_IR_TYS.unit,
                _ => self.uncached_ty_from_tir_ty(id, &ty),
            };

            (result, ShouldCache::No)
        })
    }

    /// Get the [IrTy] from the given [Ty].
    fn uncached_ty_from_tir_ty(&self, id: TyId, ty: &Ty) -> IrTyId {
        let ty = match *ty {
            Ty::TupleTy(TupleTy { data }) => {
                // Optimise, if this is a UNIT, then we can just return a unit type.
                if data.is_empty() {
                    return COMMON_IR_TYS.unit;
                }

                let mut flags = AdtFlags::empty();
                flags |= AdtFlags::TUPLE;

                // Convert the single variant into the tuple variant.
                let fields = data
                    .elements()
                    .borrow()
                    .iter()
                    .map(|field| self.ty_id_from_tir_ty(field.ty))
                    .enumerate()
                    .map(|(index, ty)| AdtField { name: index.into(), ty })
                    .collect();
                let variant = AdtVariant::singleton("0".into(), fields);

                let adt = Adt::new_with_flags("tuple".into(), index_vec![variant], flags);
                IrTy::Adt(Adt::create(adt))
            }
            Ty::FnTy(FnTy { params, return_ty, .. }) => {
                let params = IrTyListId::seq(
                    params.elements().borrow().iter().map(|param| self.ty_id_from_tir_ty(param.ty)),
                );
                let return_ty = self.ty_id_from_tir_ty(return_ty);
                IrTy::Fn { params, return_ty }
            }
            Ty::RefTy(RefTy { kind, mutable, ty }) => {
                let ty = self.ty_id_from_tir_ty(ty);
                let mutability = if mutable { Mutability::Mutable } else { Mutability::Immutable };
                let ref_kind = match kind {
                    hash_tir::tir::RefKind::Rc => ty::RefKind::Rc,
                    hash_tir::tir::RefKind::Raw => ty::RefKind::Raw,
                    hash_tir::tir::RefKind::Local => ty::RefKind::Normal,
                };

                IrTy::Ref(ty, mutability, ref_kind)
            }
            Ty::DataTy(data_ty) => return self.ty_from_tir_data(data_ty),

            // This is a type variable that should be found in the scope. It is
            // resolved and substituted in the `Ty::Var` case below.
            Ty::Var(var) => {
                // @@Temporary
                if self.context().try_get_decl(var.symbol).is_some() {
                    let term = self.context().get_binding_value(var.symbol);
                    let ty = term.value();
                    return self.uncached_ty_from_tir_ty(id, &ty);
                } else {
                    return COMMON_IR_TYS.unit; // We just return the unit type
                                               // for now.
                }
            }
            ty @ Ty::Hole(_) => {
                let message =
                    format!("all types should be monomorphised before lowering, type: `{}`", ty);

                if let Some(location) = id.span() {
                    panic_on_span!(location, format!("{message}"))
                } else {
                    panic!("{message}")
                }
            }

            _ => IrTy::Adt(AdtId::UNIT),
        };

        IrTy::create(ty)
    }

    /// Create a new [IrTyId] from the given intrinsic whilst
    /// caching the result.
    pub(crate) fn ty_id_from_tir_intrinsic(
        &self,
        intrinsic: TirIntrinsic,
        originating_node: AstNodeId,
    ) -> IrTyId {
        self.with_cache(intrinsic, || {
            let instance = self.create_instance_from_intrinsic(intrinsic, originating_node);

            let is_lang = instance.has_attr(attrs::LANG);
            let name = instance.name();

            // Check if the instance has the `lang` attribute, specifying that it is
            // the lang-item attribute.
            let instance = Instance::create(instance);
            let ty = IrTy::create(IrTy::FnDef { instance });

            if is_lang {
                let item = LangItem::from_str_name(name.into());
                self.lcx.lang_items_mut().set(item, instance, ty);
            }

            // The function is an intrinsic function
            let item = Intrinsic::from_str_name(name.into()).expect("unknown intrinsic function");
            self.lcx.intrinsics_mut().set(item, instance, ty);

            (ty, ShouldCache::Yes)
        })
    }

    /// Create a new [IrTyId] from the given function definition whilst
    /// caching the result.
    pub(crate) fn ty_id_from_tir_fn_def(&self, def: FnDefId) -> IrTyId {
        self.with_cache(def, || {
            let instance = self.create_instance_from_fn_def(def);

            let is_lang = instance.has_attr(attrs::LANG);
            let name = instance.name();

            // Check if the instance has the `lang` attribute, specifying that it is
            // the lang-item attribute.
            let instance = Instance::create(instance);
            let ty = IrTy::create(IrTy::FnDef { instance });

            if is_lang {
                let item = LangItem::from_str_name(name.into());
                self.lcx.lang_items_mut().set(item, instance, ty);
            }

            (ty, ShouldCache::Yes)
        })
    }

    /// Create a [Instance] from a [TirIntrinsic].
    ///
    /// Only some of the [TirIntrinsic]s have equivalents in the IR [Intrinsic]
    /// enum.
    fn create_instance_from_intrinsic(
        &self,
        intrinsic: TirIntrinsic,
        originating_node: AstNodeId,
    ) -> Instance {
        let FnTy { params, return_ty, .. } = intrinsic.ty();

        let params = IrTyListId::seq(
            params.elements().borrow().iter().map(|param| self.ty_id_from_tir_ty(param.ty)),
        );
        let ret_ty = self.ty_id_from_tir_ty(return_ty);

        let ident = intrinsic.name();
        let mut instance = Instance::new(ident, None, params, ret_ty, originating_node);

        if Intrinsic::from_str_name(ident.into()).is_some() {
            instance.is_intrinsic = true;
        }

        instance
    }

    /// Create a [Instance] from a [FnDefId]. This represents the function
    // / instance including the name, types (monomorphised), and attributes
    /// that are associated with the function definition.
    fn create_instance_from_fn_def(&self, fn_def: FnDefId) -> Instance {
        let FnDef { name, ty, .. } = *fn_def.value();

        // Get the AstNodeId of the function definition, this is used to
        // link this instance to any attributes that might be applied
        // to the function definition.
        let attr_id = fn_def.node_id_ensured();

        let source = fn_def.span().map(|location| location.id);
        let FnTy { params, return_ty, .. } = ty;

        let params = IrTyListId::seq(
            params.elements().borrow().iter().map(|param| self.ty_id_from_tir_ty(param.ty)),
        );
        let ret_ty = self.ty_id_from_tir_ty(return_ty);
        let ident = name.ident();

        Instance::new(ident, source, params, ret_ty, attr_id)
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
    fn adt_ty_from_data(
        &self,
        ty: DataTy,
        def: &DataDef,
        ctor_defs: CtorDefsId,
    ) -> (IrTyId, ShouldCache) {
        // If data_def has more than one constructor, then it is assumed that this
        // is a enum.
        let mut flags = AdtFlags::empty();

        match ctor_defs.len() {
            // This must be the never type.
            0 => {
                return (COMMON_IR_TYS.never, ShouldCache::No);
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
            Some(IrTyListId::seq(
                ty.args.elements().borrow().iter().map(|arg| self.ty_id_from_tir_ty(arg.value)),
            ))
        } else {
            None
        };

        // Lower each variant as a constructor.
        let variants = ctor_defs
            .elements()
            .borrow()
            .iter()
            .enumerate()
            .map(|(index, ctor)| {
                let fields = ctor
                    .params
                    .elements()
                    .borrow()
                    .iter()
                    .enumerate()
                    .map(|(index, field)| AdtField {
                        name: field.name.borrow().name.unwrap_or(index.into()),
                        ty: self.ty_id_from_tir_ty(field.ty),
                    })
                    .collect_vec();

                // @@Hack: for now we just use the discriminant as the index of the 
                // variant, this is not correct, but it will do for now.
                let discriminant = if let Some(discriminant_term) = ctor.discriminant &&
                                      let Some(value) = try_use_term_as_integer_lit(self, discriminant_term) {
                    VariantDiscriminant(value)
                } else {
                    VariantDiscriminant(index as u128)
                };

                AdtVariant {
                    name: ctor.name.ident(),
                    fields,
                    discriminant,
                }
            })
            .collect::<AdtVariants>();

        // Get the name of the data type, if no name exists we default to
        // using `_`.
        let mut adt = Adt::new_with_flags(def.name.ident(), variants, flags);
        adt.substitutions = subs;

        // Deal with any specific attributes that were set on the type, i.e.
        // `#repr`.
        if let Some(origin) = ty.data_def.node_id() {
            adt.apply_origin(origin)
        }

        // Update the type in the slot that was reserved for it.
        reserved_ty.modify(|ty| *ty = IrTy::Adt(Adt::create(adt)));

        // We created our own cache entry, so we don't need to update the
        // cache.
        (reserved_ty, ShouldCache::Yes)
    }

    /// Function that converts a [DataTy] into the corresponding [IrTyId].
    fn uncached_ty_from_tir_data(&self, ty: DataTy) -> (IrTyId, ShouldCache) {
        let data_def = ty.data_def.value();

        match data_def.ctors {
            DataDefCtors::Defined(ctor_defs) => {
                // Booleans are defined as a data type with two constructors,
                // check here if we are dealing with a boolean.
                if bool_def() == ty.data_def {
                    return (COMMON_IR_TYS.bool, ShouldCache::Yes);
                }

                self.context().enter_scope(ty.data_def.into(), || {
                    self.context().add_arg_bindings(data_def.params, ty.args);
                    self.adt_ty_from_data(ty, &data_def, ctor_defs)
                })
            }

            // Primitive are numerics, strings, arrays, etc.
            DataDefCtors::Primitive(primitive) => {
                let ty = match primitive {
                    PrimitiveCtorInfo::Numeric(NumericCtorInfo { bits, flags }) => {
                        if flags.is_float() {
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

                                    if flags.is_signed() {
                                        match size.bytes() {
                                            // If this is a platform type, return `isize`
                                            _ if flags.is_platform() => COMMON_IR_TYS.isize,
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
                                            // If this is a platform type, return `usize`
                                            _ if flags.is_platform() => COMMON_IR_TYS.usize,
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
                                NumericCtorBits::Unbounded => {
                                    if flags.is_signed() {
                                        COMMON_IR_TYS.ibig
                                    } else {
                                        COMMON_IR_TYS.ubig
                                    }
                                }
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

                            let ty = match length.and_then(|l| try_use_term_as_integer_lit(self, l))
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
                (ty, ShouldCache::Yes)
            }
        }
    }
}
