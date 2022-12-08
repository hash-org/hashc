//! Logic for converting `hash-types` types into `hash-ir` types. This is done
//! in order to simplify the lowering process when it needs to deal with types
//! of items. The full [Term] structure which is defined in the `hash-types` is
//! not required for the IR generation stage, and often has un-needed terms for
//! the lowering process. This is why this builder is used to `lower` the [Term]
//! types into the [IrTy] which is then used for the lowering process.

use hash_ir::{
    ir::Const,
    ty::{AdtData, AdtField, AdtFlags, AdtVariant, IrTy, IrTyId},
};
use hash_source::{
    constant::{FloatTy, SIntTy, UIntTy, CONSTANT_MAP},
    identifier::IDENTS,
};
use hash_types::{
    nominals::{EnumDef, EnumVariantValue, NominalDef, NominalDefId, StructFields},
    storage::GlobalStorage,
    terms::{FnLit, FnTy, Level0Term, Level1Term, LitTerm, Term, TermId, TupleLit, TupleTy},
};
use hash_utils::store::{CloneStore, SequenceStore, Store};
use index_vec::index_vec;

use super::Builder;

/// Get the [FnTy] from a given [TermId].
pub(super) fn get_fn_ty_from_term(term_id: TermId, tcx: &GlobalStorage) -> FnTy {
    tcx.term_store.map_fast(term_id, |term| match term {
        Term::Level0(Level0Term::FnLit(FnLit { fn_ty, .. })) => get_fn_ty_from_term(*fn_ty, tcx),
        Term::Level1(Level1Term::Fn(fn_ty)) => *fn_ty,
        _ => unreachable!(),
    })
}

/// Assuming that the provided [TermId] is a literal term, we essentially
/// convert the term into a [Const] and return the value of the constant
/// as a [u128]. This literal term must be an integral type.
pub(crate) fn evaluate_int_lit_term(term: TermId, tcx: &GlobalStorage) -> (Const, u128) {
    tcx.term_store.map_fast(term, |term| match term {
        Term::Level0(Level0Term::Lit(LitTerm::Int { value })) => CONSTANT_MAP
            .map_int_constant(*value, |val| {
                (Const::Int(*value), u128::from_be_bytes(val.get_bytes()))
            }),
        Term::Level0(Level0Term::Lit(LitTerm::Char(char))) => {
            (Const::Char(*char), u128::from(*char))
        }
        _ => unreachable!(),
    })
}

/// Convert a [LitTerm] into a [Const] value.
pub(super) fn constify_lit_term(term: TermId, tcx: &GlobalStorage) -> Const {
    tcx.term_store.map_fast(term, |term| match term {
        Term::Level0(Level0Term::Lit(LitTerm::Int { value })) => Const::Int(*value),
        Term::Level0(Level0Term::Lit(LitTerm::Char(char))) => Const::Char(*char),
        Term::Level0(Level0Term::Lit(LitTerm::Str(str))) => Const::Str(*str),
        _ => unreachable!(),
    })
}

impl<'tcx> Builder<'tcx> {
    /// Get the [IrTy] from a given [TermId].
    pub(super) fn lower_term(&self, term: TermId) -> IrTy {
        let term = self.tcx.term_store.get(term);

        match term {
            // @@Temporary: we shouldn't need to deal with `Level0` terms...
            Term::Level0(lvl_0_term) => match lvl_0_term {
                Level0Term::FnLit(FnLit { fn_ty, .. }) => self.lower_term(fn_ty),
                Level0Term::Rt(term) => self.lower_term(term),
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
                            ty: self.convert_term_into_ir_ty(param.value),
                        })
                        .collect();

                    let variants = index_vec![AdtVariant { name: 0usize.into(), fields }];
                    let adt = AdtData::new_with_flags("tuple".into(), variants, AdtFlags::TUPLE);
                    let adt_id = self.storage.adt_store().create(adt);
                    IrTy::Adt(adt_id)
                }
                Level0Term::Lit(lit_term) => match lit_term {
                    LitTerm::Str(_) => IrTy::Str,
                    LitTerm::Int { value } => {
                        CONSTANT_MAP.map_int_constant(value, |val| val.ty).into()
                    }
                    LitTerm::Char(_) => IrTy::Char,
                },
                Level0Term::EnumVariant(EnumVariantValue { enum_def_id, .. }) => {
                    self.lower_nominal_def(enum_def_id)
                }
                Level0Term::Unit(_) | Level0Term::FnCall(_) | Level0Term::Constructed(_) => {
                    panic!("unexpected level 0 term: {lvl_0_term:?}")
                }
            },

            Term::Level1(lvl_1_term) => match lvl_1_term {
                Level1Term::NominalDef(def_id) => self.lower_nominal_def(def_id),
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
                            ty: self.convert_term_into_ir_ty(param.ty),
                        })
                        .collect();

                    let variants = index_vec![AdtVariant { name: 0usize.into(), fields }];
                    let adt = AdtData::new_with_flags("tuple".into(), variants, AdtFlags::TUPLE);
                    let adt_id = self.storage.adt_store().create(adt);
                    IrTy::Adt(adt_id)
                }
                Level1Term::Fn(FnTy { name, params, return_ty }) => {
                    let return_ty = self.convert_term_into_ir_ty(return_ty);
                    let params = self
                        .tcx
                        .params_store
                        .get_owned_param_list(params)
                        .into_positional()
                        .into_iter()
                        .map(|param| self.convert_term_into_ir_ty(param.ty));

                    let params = self.storage.ty_list_store().create_from_iter(params);
                    IrTy::Fn { name, params, return_ty }
                }
                Level1Term::ModDef(_) => unreachable!(),
            },
            Term::ScopeVar(scope_var) => {
                // read the scope that the member belongs to and extract the scope member
                // data, and then lower the underlying type.
                let scope_member = self.tcx.scope_store.map_fast(scope_var.scope, |scope| {
                    scope.members.get(scope_var.index).cloned().unwrap()
                });

                self.lower_term(scope_member.ty())
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
                    return self.lower_term(union[0]);
                }

                let variants = union
                    .into_iter()
                    .enumerate()
                    .map(|(index, param)| AdtVariant {
                        name: index.into(),
                        fields: vec![AdtField {
                            name: 0usize.into(),
                            ty: self.convert_term_into_ir_ty(param),
                        }],
                    })
                    .collect();

                // @@Future: figure out what name to use when printing the name of the union.
                let adt = AdtData::new_with_flags("union{...}".into(), variants, AdtFlags::UNION);
                let adt_id = self.storage.adt_store().create(adt);

                IrTy::Adt(adt_id)
            }
            Term::Var(_)
            | Term::Access(_)
            | Term::Merge(_)
            | Term::TyFn(_)
            | Term::TyFnTy(_)
            | Term::TyFnCall(_)
            | Term::SetBound(_)
            | Term::Level3(_)
            | Term::Level2(_)
            | Term::TyOf(_)
            | Term::Unresolved(_)
            | Term::Root => panic!("unexpected term: {term:?}"),
        }
    }

    fn lower_nominal_def(&self, def_id: NominalDefId) -> IrTy {
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
                                                ty: self.convert_term_into_ir_ty(param.ty),
                                            })
                                            .collect()
                                    },
                                );

                                let variants = index_vec![AdtVariant { name, fields }];

                                let adt = AdtData::new_with_flags(name, variants, AdtFlags::STRUCT);
                                let adt_id = self.storage.adt_store().create(adt);

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
                                                    ty: self.convert_term_into_ir_ty(param.ty),
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
                        let adt_id = self.storage.adt_store().create(adt);

                        IrTy::Adt(adt_id)
                    }
                },
            }
        })
    }

    /// This function will attempt to lower a provided [TermId] into a specified
    /// variant of a [AdtData]. This function assumed that the specified term is
    /// a [Term::Level0] enum variant which belongs to the specified adt,
    /// otherwise the function will panic.
    pub(crate) fn lower_enum_variant_ty(&self, adt: &AdtData, term: TermId) -> usize {
        self.tcx.term_store.map_fast(term, |term| match term {
            Term::Level0(level0_term) => match level0_term {
                Level0Term::EnumVariant(EnumVariantValue { variant_name, .. }) => {
                    adt.variant_idx(variant_name).unwrap()
                }
                term => panic!("expected enum variant, but got: {term:?}"),
            },
            term => panic!("expected enum variant, but got: {term:?}"),
        })
    }

    /// Get the [IrTyId] from a given [TermId]. This function will internally
    /// cache results of lowering a [TermId] into an [IrTyId] to avoid
    /// duplicate work. =
    pub(crate) fn convert_term_into_ir_ty(&self, term: TermId) -> IrTyId {
        // Check if the term is present within the cache, and if so, return the
        // cached value.
        if let Some(ty) = self.storage.ty_cache().get(&term) {
            return *ty;
        }

        let ir_ty = self.lower_term(term);
        let ir_ty_id = self.storage.ty_store().create(ir_ty);

        // Add an entry into the cache for this term
        self.storage.add_ty_cache_entry(term, ir_ty_id);
        ir_ty_id
    }
}
