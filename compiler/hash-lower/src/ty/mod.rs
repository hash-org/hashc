//! Contains all of the logic that is used by the lowering process
//! to convert types and terms into [IrTy]s.

use hash_ir::{
    ty::{AdtData, AdtField, AdtFlags, AdtVariant, Instance, IrTy, IrTyId},
    IrCtx,
};
use hash_source::{
    constant::{FloatTy, SIntTy, UIntTy, CONSTANT_MAP},
    identifier::IDENTS,
};
use hash_tir::{
    fmt::{PrepareForFormatting, TcFormatOpts},
    location::LocationTarget,
    nominals::{EnumDef, EnumVariantValue, NominalDef, NominalDefId, StructFields},
    storage::GlobalStorage,
    terms::{
        ConstructedTerm, FnLit, FnTy, Level0Term, Level1Term, LitTerm, Term, TermId, TupleLit,
        TupleTy,
    },
};
use hash_utils::{
    index_vec::index_vec,
    store::{CloneStore, SequenceStore, Store},
};

/// A context that is used to lower types and terms into [IrTy]s.
pub(crate) struct TyLoweringCtx<'ir> {
    /// A reference to the store of all of the IR types.
    pub lcx: &'ir IrCtx,

    /// A reference to the type storage context.
    pub tcx: &'ir GlobalStorage,
}

impl<'ir> TyLoweringCtx<'ir> {
    /// Create a new [TyLoweringCtx] from the given [IrCtx] and [GlobalStorage].
    pub fn new(lcx: &'ir IrCtx, tcx: &'ir GlobalStorage) -> Self {
        Self { lcx, tcx }
    }

    /// Get the [IrTyId] from a given [TermId]. This function will internally
    /// cache results of lowering a [TermId] into an [IrTyId] to avoid
    /// duplicate work.
    pub(crate) fn ty_id_from_term(&self, term: TermId) -> IrTyId {
        // Check if the term is present within the cache, and if so, return the
        // cached value.
        if let Some(ty) = self.lcx.ty_cache().get(&term.into()) {
            return *ty;
        }

        let ir_ty = self.ty_from_term(term);

        // @@Hack: avoid re-creating "commonly" used types in order
        // to allow for type_id equality to work
        let id = match ir_ty {
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
            _ => self.lcx.tys().create(ir_ty),
        };

        // Add an entry into the cache for this term
        self.lcx.add_ty_cache_entry(term, id);
        id
    }

    /// Get the [IrTyId] from a given [NominalDefId].
    pub(crate) fn ty_id_from_nominal(&self, nominal: NominalDefId) -> IrTyId {
        // Attempt to get the type from the cache
        if let Some(ty) = self.lcx.ty_cache().get(&nominal.into()) {
            return *ty;
        }

        // Create the type, intern it, and a cache entry for it
        let ty = self.ty_from_nominal(nominal);
        let id = self.lcx.tys().create(ty);
        self.lcx.add_nominal_ty_cache_entry(nominal, id);

        id
    }

    /// Get the [IrTy] from a given [TermId].
    pub(super) fn ty_from_term(&self, term_id: TermId) -> IrTy {
        let term = self.tcx.term_store.get(term_id);

        match term {
            // @@Temporary: we shouldn't need to deal with `Level0` terms...
            Term::Level0(lvl_0_term) => match lvl_0_term {
                Level0Term::FnLit(FnLit { fn_ty, .. }) => self.ty_from_term(fn_ty),
                Level0Term::Rt(term) => self.ty_from_term(term),
                Level0Term::Tuple(TupleLit { members }) => {
                    let fields = self
                        .tcx
                        .args_store
                        .get_owned_param_list(members)
                        .positional()
                        .iter()
                        .enumerate()
                        .map(|(index, param)| AdtField {
                            name: index.into(),
                            ty: self.ty_id_from_term(param.value),
                        })
                        .collect();

                    let variants = index_vec![AdtVariant { name: 0usize.into(), fields }];
                    let adt = AdtData::new_with_flags("tuple".into(), variants, AdtFlags::TUPLE);
                    let adt_id = self.lcx.adts().create(adt);
                    IrTy::Adt(adt_id)
                }
                Level0Term::Lit(lit_term) => match lit_term {
                    LitTerm::Str(_) => IrTy::Str,
                    LitTerm::Int { value } => {
                        CONSTANT_MAP.map_int_constant(value, |val| val.ty).into()
                    }
                    LitTerm::Char(_) => IrTy::Char,
                },
                Level0Term::EnumVariant(EnumVariantValue { def_id, .. }) => {
                    self.ty_from_nominal(def_id)
                }
                Level0Term::Constructed(ConstructedTerm { subject, .. }) => {
                    self.ty_from_term(subject)
                }
                Level0Term::Unit(_) | Level0Term::FnCall(_) => {
                    panic!("unexpected level 0 term: {lvl_0_term:?}")
                }
            },

            Term::Level1(lvl_1_term) => match lvl_1_term {
                Level1Term::NominalDef(def_id) => self.ty_from_nominal(def_id),
                Level1Term::Tuple(TupleTy { members }) => {
                    let fields = self
                        .tcx
                        .params_store
                        .get_owned_param_list(members)
                        .into_positional()
                        .into_iter()
                        .enumerate()
                        .map(|(index, param)| AdtField {
                            name: index.into(),
                            ty: self.ty_id_from_term(param.ty),
                        })
                        .collect();

                    let variants = index_vec![AdtVariant { name: 0usize.into(), fields }];
                    let adt = AdtData::new_with_flags("tuple".into(), variants, AdtFlags::TUPLE);
                    let adt_id = self.lcx.adts().create(adt);
                    IrTy::Adt(adt_id)
                }
                Level1Term::Fn(FnTy { name, params, return_ty }) => {
                    let return_ty = self.ty_id_from_term(return_ty);
                    let params = self
                        .tcx
                        .params_store
                        .get_owned_param_list(params)
                        .into_positional()
                        .into_iter()
                        .map(|param| self.ty_id_from_term(param.ty));

                    let params = self.lcx.tls().create_from_iter(params);

                    // We lookup the source of the function by looking at the associated
                    // location of the term and then taking the source-id from it.
                    let source = self.tcx.location_store.get_source(LocationTarget::from(term_id));

                    // @@Temporary: `Instance` is not being properly initialised. This is until the
                    // new typechecking introduces `FnDefId`s.
                    let instance = self.lcx.instances().create(Instance::new(
                        name.unwrap_or(IDENTS.underscore),
                        source,
                        params,
                        return_ty,
                    ));

                    IrTy::Fn { params, return_ty, instance }
                }
                Level1Term::ModDef(_) => unreachable!(),
            },
            Term::ScopeVar(scope_var) => {
                // read the scope that the member belongs to and extract the scope member
                // data, and then lower the underlying type.
                let scope_member = self.tcx.scope_store.map_fast(scope_var.scope, |scope| {
                    scope.members.get(scope_var.index).cloned().unwrap()
                });

                self.ty_from_term(scope_member.ty())
            }
            Term::BoundVar(_) => {
                // @@Verify: this should never occur, since that `BoundVar(..)` should only
                // be present on value types, and not types. However, it is not entirely clear
                // if this case does occur, so we should verify this.
                unreachable!()
            }
            Term::Union(union_term) => {
                let union = self.tcx.term_list_store.get_vec(union_term);

                // This means that this is the `never` type
                if union.is_empty() {
                    return IrTy::Never;
                }

                // If there is only one variant, then we can just return that variant.
                if union.len() == 1 {
                    return self.ty_from_term(union[0]);
                }

                let variants = union
                    .into_iter()
                    .enumerate()
                    .map(|(index, param)| AdtVariant {
                        name: index.into(),
                        fields: vec![AdtField {
                            name: 0usize.into(),
                            ty: self.ty_id_from_term(param),
                        }],
                    })
                    .collect();

                // @@Future: figure out what name to use when printing the name of the union.
                let adt = AdtData::new_with_flags("union{...}".into(), variants, AdtFlags::UNION);
                let adt_id = self.lcx.adts().create(adt);

                IrTy::Adt(adt_id)
            }

            // @@FixMe: we assume that a merge term is going to be either a
            // list or some other collection type.
            Term::TyFnCall(_) | Term::Merge(_) => {
                IrTy::Slice(self.lcx.tys().create(IrTy::Int(SIntTy::I32)))
            }
            Term::Var(_)
            | Term::Access(_)
            | Term::TyFn(_)
            | Term::TyFnTy(_)
            | Term::SetBound(_)
            | Term::Level3(_)
            | Term::Level2(_)
            | Term::TyOf(_)
            | Term::Unresolved(_)
            | Term::Root => panic!(
                "unexpected term: `{}`, expanded: `{:?}`",
                term_id.for_formatting_with_opts(self.tcx, TcFormatOpts { expand: true }),
                term
            ),
        }
    }

    /// Convert a [NominalDef] into the equivalent [IrTy].
    pub(super) fn ty_from_nominal(&self, def_id: NominalDefId) -> IrTy {
        self.tcx.nominal_def_store.map_fast(def_id, |def| {
            match def {
                NominalDef::Struct(struct_def) => {
                    // @@Hack: for now, we basically just check if the name
                    // of the struct is a `primitive` type, and if so then
                    // we convert to using the primitive variant, otherwise we
                    // then just convert the struct into the IR representation.

                    if struct_def.name.is_none() {
                        // @@Future: Nameless structs will be removed from the type
                        // structure           so we don't
                        // have to deal with them here.
                        unreachable!()
                    }

                    match struct_def.name.unwrap() {
                        id if id == IDENTS.i8 => IrTy::Int(SIntTy::I8),
                        id if id == IDENTS.i16 => IrTy::Int(SIntTy::I16),
                        id if id == IDENTS.i32 => IrTy::Int(SIntTy::I32),
                        id if id == IDENTS.i64 => IrTy::Int(SIntTy::I64),
                        id if id == IDENTS.i128 => IrTy::Int(SIntTy::I128),
                        id if id == IDENTS.isize => IrTy::Int(SIntTy::ISize),
                        id if id == IDENTS.u8 => IrTy::UInt(UIntTy::U8),
                        id if id == IDENTS.u16 => IrTy::UInt(UIntTy::U16),
                        id if id == IDENTS.u32 => IrTy::UInt(UIntTy::U32),
                        id if id == IDENTS.u64 => IrTy::UInt(UIntTy::U64),
                        id if id == IDENTS.u128 => IrTy::UInt(UIntTy::U128),
                        id if id == IDENTS.usize => IrTy::UInt(UIntTy::USize),
                        id if id == IDENTS.f32 => IrTy::Float(FloatTy::F32),
                        id if id == IDENTS.f64 => IrTy::Float(FloatTy::F64),
                        id if id == IDENTS.char => IrTy::Char,
                        id if id == IDENTS.str => IrTy::Str,
                        id if id == IDENTS.never => IrTy::Never,
                        name => {
                            // if the fields of the struct are not opaque, then we
                            // can create an ADT from it, otherwise this case should
                            // not occur, and we have encountered an unhandled
                            // primitive.
                            if let StructFields::Explicit(params) = struct_def.fields {
                                let fields = self.tcx.params_store.map_as_param_list_fast(
                                    params,
                                    |params| {
                                        params
                                            .positional()
                                            .iter()
                                            .enumerate()
                                            .map(|(index, param)| AdtField {
                                                name: param.name.unwrap_or_else(|| index.into()),
                                                ty: self.ty_id_from_term(param.ty),
                                            })
                                            .collect()
                                    },
                                );

                                let variants = index_vec![AdtVariant { name, fields }];

                                let adt = AdtData::new_with_flags(name, variants, AdtFlags::STRUCT);
                                let adt_id = self.lcx.adts().create(adt);

                                IrTy::Adt(adt_id)
                            } else {
                                // If we get here, this means that we haven't accounted
                                // for
                                // a particular primitive
                                // type occurring.
                                panic!("unhandled primitive type: {name}");
                            }
                        }
                    }
                }
                NominalDef::Unit(_) => unimplemented!(),
                NominalDef::Enum(EnumDef { name, variants }) => match name.unwrap() {
                    id if id == IDENTS.bool => IrTy::Bool,
                    name => {
                        let variants = variants
                            .iter()
                            .map(|(variant_name, variant)| {
                                let fields = match variant.fields {
                                    Some(fields) => self.tcx.params_store.map_as_param_list_fast(
                                        fields,
                                        |params| {
                                            params
                                                .positional()
                                                .iter()
                                                .enumerate()
                                                .map(|(index, param)| AdtField {
                                                    name: param
                                                        .name
                                                        .unwrap_or_else(|| index.into()),
                                                    ty: self.ty_id_from_term(param.ty),
                                                })
                                                .collect()
                                        },
                                    ),
                                    None => vec![],
                                };

                                AdtVariant { name: *variant_name, fields }
                            })
                            .collect();

                        let adt = AdtData::new_with_flags(name, variants, AdtFlags::ENUM);
                        let adt_id = self.lcx.adts().create(adt);

                        IrTy::Adt(adt_id)
                    }
                },
            }
        })
    }
}
