//! Lowering utilities from a [Pat] into a [DeconstructedPat] and
//! vice versa.
use std::{iter::once, mem::size_of};

use hash_ast::ast::{ParamOrigin, RangeEnd};
use hash_source::constant::{IntConstant, IntConstantValue, CONSTANT_MAP};
use hash_tir::{
    mods::ModDef,
    nominals::{EnumVariantValue, NominalDef, StructFields},
    params::ParamsId,
    pats::{
        AccessPat, ArrayPat, ConstPat, ConstructorPat, IfPat, ModPat, Pat, PatArg, PatArgsId,
        PatId, RangePat, SpreadPat,
    },
    terms::{Level0Term, Level1Term, LitTerm, Term, TermId, TupleTy},
};
use hash_utils::{
    itertools::Itertools,
    store::{SequenceStore, Store},
};
use if_chain::if_chain;
use smallvec::SmallVec;

use super::{
    constant::Constant,
    construct::DeconstructedCtor,
    deconstruct::DeconstructedPat,
    fields::Fields,
    list::{Array, ArrayKind},
    range::IntRange,
    AccessToUsefulnessOps,
};
use crate::{
    diagnostics::macros::tc_panic,
    ops::AccessToOps,
    storage::{exhaustiveness::DeconstructedPatId, AccessToStorage, StorageRef},
};

/// Representation of a field within a collection of patterns.
#[derive(Debug, Clone)]
pub struct FieldPat {
    /// Relative to the associated definition
    pub(crate) index: usize,
    /// Pattern associated with this field
    pub(crate) pat: PatId,
}

pub struct LowerPatOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for LowerPatOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> LowerPatOps<'tc> {
    /// Create a new [LowerPatOps].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Convert a [Pat] into a [DeconstructedPat].
    pub(crate) fn deconstruct_pat(&self, ty: TermId, pat_id: PatId) -> DeconstructedPat {
        let reader = self.reader();
        let pat = reader.get_pat(pat_id);

        let (ctor, fields) = match pat {
            Pat::Wild | Pat::Binding(_) | Pat::Spread(_) => (DeconstructedCtor::Wildcard, vec![]),

            // For all members in the scope, fill it in as a wildcard, and then provide
            // deconstructed patterns for the actual members that are specified in the
            // pattern...
            //
            // @@Speed: Could we just care about the specified fields and assume that the
            // rest are wildcards, since this seems to be redundant, might need to introduce
            // some kind of special fields that doesn't care about all of the filled in fields...
            Pat::Mod(ModPat { members }) => {
                let specified_members = reader.get_pat_args_owned(members);

                let (scope_id, mut scope_members) = match reader.get_term(ty) {
                    Term::Level1(Level1Term::ModDef(id)) => {
                        let ModDef { members, .. } = reader.get_mod_def(id);
                        self.scope_store().map_fast(members, |scope| {
                            // We should be in a constant scope
                            assert!(scope.kind.is_constant());
                            (
                                members,
                                scope
                                    .members
                                    .iter()
                                    .map(|member| self.deconstruct_pat_ops().wildcard(member.ty()))
                                    .collect_vec(),
                            )
                        })
                    }
                    _ => tc_panic!(
                        ty,
                        self,
                        "expected a module definition when deconstructing pattern!"
                    ),
                };

                // Iterate over the specified members and set the `actual` pattern here
                for member in specified_members.positional() {
                    let index = self
                        .scope_store()
                        .map_fast(scope_id, |scope| scope.get(member.name.unwrap()).unwrap().1);

                    scope_members[index] =
                        self.deconstruct_pat(scope_members[index].ty, member.pat);
                }

                (DeconstructedCtor::Single, scope_members)
            }

            // A `access` is either going to be
            Pat::Access(AccessPat { subject, .. }) => {
                let pat_ty = self.typer().get_term_of_pat(pat_id).unwrap();

                match self.maybe_construct_variant(pat_ty) {
                    Some(variant) => (variant, vec![]),
                    None => return self.deconstruct_pat(ty, subject),
                }
            }
            // This is essentially a simplification to some unit nominal definition like
            // for example `None`..., here we need to be able to get the `type` of the
            // actual pattern in order to figure out which
            Pat::Const(ConstPat { term }) => match self.maybe_construct_variant(term) {
                Some(variant) => (variant, vec![]),
                None => (DeconstructedCtor::Wildcard, vec![]),
            },
            Pat::Range(range) => {
                let range = self.lower_pat_range(ty, range);
                (DeconstructedCtor::IntRange(range), vec![])
            }
            Pat::Lit(term) => match reader.get_term(term) {
                Term::Level0(Level0Term::Lit(lit)) => match lit {
                    LitTerm::Str(value) => (DeconstructedCtor::Str(value), vec![]),
                    LitTerm::Int { value } => {
                        let ptr_width = self.global_storage().pointer_width;
                        let value = Constant::from_int(value, term, ptr_width);
                        let range = self.int_range_ops().range_from_constant(value);
                        (DeconstructedCtor::IntRange(range), vec![])
                    }
                    LitTerm::Char(value) => {
                        let value = Constant::from_char(value, term);
                        let range = self.int_range_ops().range_from_constant(value);
                        (DeconstructedCtor::IntRange(range), vec![])
                    }
                },
                _ => tc_panic!(term, self, "Not a constant!"),
            },
            Pat::Tuple(args) => {
                // We need to read the tuple type from the ctx type and then create
                // wildcard fields for all of the inner types
                match reader.get_term(ty) {
                    Term::Level1(Level1Term::Tuple(TupleTy { members })) => {
                        let fields = self.pat_lowerer().deconstruct_pat_fields(args, members);
                        let members = reader.get_params_owned(members);

                        // Create wild-cards for all of the tuple inner members
                        let mut wilds: SmallVec<[_; 2]> = members
                            .positional()
                            .iter()
                            .map(|member| self.deconstruct_pat_ops().wildcard(member.ty))
                            .collect();

                        // For each provided field, we want to recurse and lower the pattern further
                        for field in fields {
                            wilds[field.index] =
                                self.deconstruct_pat(wilds[field.index].ty, field.pat);
                        }

                        (DeconstructedCtor::Single, wilds.to_vec())
                    }
                    _ => tc_panic!(
                        ty,
                        self,
                        "Unexpected ty `{}` when deconstructing pattern {:?}",
                        self.for_fmt(ty),
                        pat
                    ),
                }
            }
            Pat::Constructor(ConstructorPat { args, .. }) => {
                reader.term_store().map_fast(ty, |term| {
                    match term {
                        Term::Level1(Level1Term::NominalDef(nominal_def)) => {
                            let lower_constructor_args = |params: ParamsId| {
                                // Lower the fields by resolving what positions the
                                // actual fields are with the reference of the
                                // constructor's type...
                                let fields =
                                    self.pat_lowerer().deconstruct_pat_fields(args, params);

                                let args = reader.get_params_owned(params);
                                let tys = args.positional().iter().map(|param| param.ty);

                                let mut wilds: SmallVec<[_; 2]> =
                                    tys.map(|ty| self.deconstruct_pat_ops().wildcard(ty)).collect();

                                // For each provided field, we want to recurse and lower
                                // the pattern further
                                for field in fields {
                                    wilds[field.index] =
                                        self.deconstruct_pat(wilds[field.index].ty, field.pat);
                                }

                                wilds.to_vec()
                            };

                            reader.nominal_def_store().map_fast(*nominal_def, |def| {
                                match def {
                                    NominalDef::Struct(struct_def) => match struct_def.fields {
                                        StructFields::Explicit(members) => (
                                            DeconstructedCtor::Single,
                                            lower_constructor_args(members),
                                        ),
                                        StructFields::Opaque => {
                                            panic!("got unexpected opaque struct-def here")
                                        }
                                    },
                                    NominalDef::Unit(_) => (DeconstructedCtor::Single, vec![]),
                                    NominalDef::Enum(_) => {
                                        // @@Todo: We need to deduce the variant index from the type
                                        // of the pattern?
                                        todo!()
                                    }
                                }
                            })
                        }
                        _ => tc_panic!(
                            ty,
                            self,
                            "unexpected ty `{}` when deconstructing pattern {:?}",
                            self.for_fmt(ty),
                            pat
                        ),
                    }
                })
            }
            Pat::Array(ArrayPat { element_pats: inner, .. }) => {
                let mut prefix = vec![];
                let mut suffix = vec![];
                let mut spread = false;

                let pats = reader.get_pat_args_owned(inner);
                let inner_ty = self.oracle().term_as_list_ty(ty).unwrap();

                // We don't care about the `name` of the arg because the list
                // never has the `name` assigned to anything...
                for PatArg { pat: id, .. } in pats.positional() {
                    let pat = reader.get_pat(*id);

                    if matches!(pat, Pat::Spread(_)) {
                        if spread {
                            tc_panic!(
                                id,
                                self,
                                "found multiple spread patterns within list pattern"
                            );
                        }

                        spread = true;
                    } else {
                        match spread {
                            true => suffix.push(self.deconstruct_pat(inner_ty, *id)),
                            false => prefix.push(self.deconstruct_pat(inner_ty, *id)),
                        }
                    }
                }

                // If we saw a `...` then we can't be sure of the list length and
                // so it is now considered to be variable length
                let kind = if spread {
                    ArrayKind::Var(prefix.len(), suffix.len())
                } else {
                    ArrayKind::Fixed(prefix.len() + suffix.len())
                };

                let ctor = DeconstructedCtor::Array(Array::new(kind));
                let fields = prefix.into_iter().chain(suffix).collect_vec();

                (ctor, fields)
            }
            Pat::Or(_) => {
                // here, we need to expand the or pattern, so that all of the
                // children patterns of the `or` become fields of the
                // deconstructed  pat.
                let pats = self.pat_lowerer().flatten_or_pat(pat_id);

                // @@Correctness: does it make sense to pass in this `ctx` since the
                // type is the type of the `or` pattern and not each pat itself, but also
                // it should be that the union-ty is simplified into a single term?
                let fields = pats.iter().map(|pat| self.deconstruct_pat(ty, *pat)).collect_vec();

                (DeconstructedCtor::Or, fields)
            }
            Pat::If(IfPat { pat, .. }) => {
                let pat = self.deconstruct_pat(ty, pat);
                pat.has_guard.set(true);

                return pat;
            }
        };

        let ctor = self.constructor_store().create(ctor);

        // Now we need to put them in the store...
        let fields = Fields::from_iter(
            fields.into_iter().map(|field| self.deconstructed_pat_store().create(field)),
        );

        DeconstructedPat::new(ctor, fields, ty, Some(pat_id))
    }

    // Convert a [DeconstructedPat] into a [Pat].
    pub(crate) fn construct_pat(&self, pat: DeconstructedPatId) -> PatId {
        let reader = self.reader();
        let deconstructed_store = reader.deconstructed_pat_store();
        let ctor_store = reader.constructor_store();

        deconstructed_store.map_fast(pat, |deconstructed| {
            let DeconstructedPat {ty, fields, ..} = deconstructed;

            // Short-circuit, if the pattern already has an associated `PatId`...
            if deconstructed.id.is_some() {
                return deconstructed.id.unwrap();
            }

            ctor_store.map_fast(deconstructed.ctor, |ctor| {
                let pat = match ctor {
                    DeconstructedCtor::Single | DeconstructedCtor::Variant(_) => {
                        match reader.get_term(*ty) {
                            Term::Level1(Level1Term::Tuple(_)) => {
                                let children =
                                    fields
                                    .iter_patterns()
                                    .map(|p| PatArg {
                                        name: None,
                                        pat: self.construct_pat(p)
                                    })
                                    .collect_vec();
                                let args = self.builder().create_pat_args(children, ParamOrigin::Tuple);
                                Pat::Tuple(args)
                            }
                            Term::Level1(Level1Term::NominalDef(def_id)) => {
                                reader.nominal_def_store().map_fast(def_id, |def| {
                                    match def {
                                        NominalDef::Struct(struct_def) => {
                                            let params = match struct_def.fields {
                                                StructFields::Explicit(fields) => fields,
                                                StructFields::Opaque => unreachable!(),
                                            };
                                            let args = self.construct_pat_args(fields, params);
                                            Pat::Constructor(ConstructorPat { subject: *ty, args })
                                        },
                                        NominalDef::Unit(_) => {
                                            Pat::Const(ConstPat { term: self.builder().create_unit_term(def_id) })
                                        }
                                        NominalDef::Enum(enum_def) => {
                                            let variant_idx = match ctor {
                                                DeconstructedCtor::Variant(idx) => *idx,
                                                _ => 0,
                                            };

                                            let variant = enum_def.get_variant_by_idx(variant_idx).unwrap();

                                            // If the variant has no fields, then we can just return a `ConstPat` with the
                                            // variant's name, and the definition id of the enum.
                                            match variant.fields {
                                                Some(params) => {
                                                    let args = self.construct_pat_args(fields, params);
                                                    Pat::Constructor(ConstructorPat { subject: *ty, args })
                                                }
                                                None => Pat::Const(ConstPat { term: self.builder().create_enum_variant_value_term(variant.name, def_id)})
                                            }
                                        },
                                    }
                                })
                            }
                            _ => tc_panic!(
                                ty,
                                self,
                                "Unexpected ty `{}` when converting to pattern",
                                self.for_fmt(*ty),
                            ),
                        }
                    }
                    DeconstructedCtor::IntRange(range) => self.construct_pat_from_range(*ty, *range),
                    DeconstructedCtor::Str(_) => Pat::Lit(*ty),
                    DeconstructedCtor::Array(Array { kind }) => {
                        let mut children = fields.iter_patterns().map(|p| PatArg { pat: self.construct_pat(p), name: None });

                        match kind {
                            ArrayKind::Fixed(_) => {
                                let inner_term = self.oracle().term_as_list_ty(*ty).unwrap();

                                let inner = self.builder().create_pat_args(children, ParamOrigin::ArrayPat);
                                Pat::Array(ArrayPat { list_element_ty: inner_term, element_pats: inner })
                            }
                            #[allow(clippy::needless_collect)]
                            ArrayKind::Var(prefix, _) => {
                                // build the prefix and suffix components
                                let prefix: Vec<_> = children.by_ref().take(*prefix).collect();
                                let suffix: Vec<_> = children.collect();

                                // Create the `spread` dummy pattern
                                let dummy = Pat::Spread(SpreadPat { name: None });
                                let spread = PatArg { pat: self.pat_store().create(dummy), name: None };

                                // Now create an inner collection of patterns with the inserted
                                // spread pattern
                                let inner = prefix.into_iter().chain(once(spread)).chain(suffix);
                                let term = self.oracle().term_as_list_ty(*ty).unwrap();

                                let elements = self.builder().create_pat_args(inner, ParamOrigin::ArrayPat);
                                Pat::Array(ArrayPat { list_element_ty: term, element_pats: elements })
                            }
                        }
                    }
                    DeconstructedCtor::Wildcard | DeconstructedCtor::NonExhaustive => Pat::Wild,
                    DeconstructedCtor::Or => {
                        panic!("cannot convert an `or` deconstructed pat back into pat")
                    }
                    DeconstructedCtor::Missing => panic!(
                        "trying to convert a `Missing` constructor into a `Pat`; this is probably a bug, `Missing` should have been processed in `apply_ctors`"
                    ),
                };
                // Now put the pat on the store and return it
                self.pat_store().create(pat)
            })
        })
    }

    /// Create a [DeconstructedCtor] from a provided [TermId] that is an
    /// underlying enum variant. If the term is not a variant, then we don't
    /// attempt to create a variant.
    fn maybe_construct_variant(&self, term: TermId) -> Option<DeconstructedCtor> {
        self.reader().term_store().map_fast(term, |term| {
            match term {
                Term::Level0(Level0Term::EnumVariant(EnumVariantValue { def_id, name })) => {
                    self.reader().nominal_def_store().map_fast(*def_id, |def| {
                        let NominalDef::Enum(enum_def) = def else {
                            unreachable!()
                        };

                        let variant_idx = enum_def.get_variant_idx(name).unwrap();

                        // We don't care about the fields here, since a `Pat::Const` will
                        // not have any fields on it ever.
                        Some(DeconstructedCtor::Variant(variant_idx))
                    })
                }
                _ => None,
            }
        })
    }

    /// Construct pattern arguments from provided [ParamsId].
    fn construct_pat_args(&self, fields: &Fields, params: ParamsId) -> PatArgsId {
        let reader = self.reader();

        // Construct the inner arguments to the constructor by iterating over the
        // pattern fields within the pattern. If possible, lookup the name of the
        // field by using the nominal definition attached to the pattern.
        let children = reader.params_store().map_fast(params, |tys| {
            fields
                .iter_patterns()
                .enumerate()
                .filter(|(_, p)| !reader.get_deconstructed_pat_ctor(*p).is_wildcard())
                .map(|(index, p)| PatArg {
                    name: tys.get(index).and_then(|param| param.name),
                    pat: self.construct_pat(p),
                })
                .collect_vec()
        });

        // We collapse all fields that are specified as `wildcards` within
        // these construct patterns in order to represent them visually in a clearer
        // way. If a construct has 20 fields that 18 are specified as wildcards, and the
        // rest have user specified patterns, then we only want to print those and the
        // rest is denoted as `...`.
        if fields.len() != children.len() {
            let dummy = Pat::Spread(SpreadPat { name: None });
            let arg = PatArg { pat: self.pat_store().create(dummy), name: None };

            self.builder()
                .create_pat_args(children.into_iter().chain(once(arg)), ParamOrigin::ConstructorPat)
        } else {
            self.builder().create_pat_args(children, ParamOrigin::ConstructorPat)
        }
    }

    /// Lower a [RangePat] into [IntRange]. This function expects that
    /// the [RangePat] was already validated, and so this function will
    /// read `lo`, and `hi` terms, convert them into bytes and put them
    /// into the [IntRange]
    pub fn lower_pat_range(&self, ty: TermId, range: RangePat) -> IntRange {
        let RangePat { lo, hi, end } = range;

        let term_to_u128 = |term| {
            // The only types we support we support within ranges is currently a
            // `char` and `int` types
            match self.reader().get_term(term) {
                Term::Level0(Level0Term::Lit(LitTerm::Char(ch))) => {
                    Constant::from_char(ch, term).data()
                }
                Term::Level0(Level0Term::Lit(LitTerm::Int { value })) => {
                    let ptr_width = self.global_storage().pointer_width;

                    Constant::from_int(value, term, ptr_width).data()
                }
                _ => tc_panic!(term, self, "term does not support lowering into range"),
            }
        };

        let lo = term_to_u128(lo);
        let hi = term_to_u128(hi);
        self.int_range_ops().make_range(ty, lo, hi, &end)
    }

    /// Convert [IntRange] into a [Pat] by judging the given
    /// type that is stored within the parent [DeconstructedPat].
    pub fn construct_pat_from_range(&self, ty: TermId, range: IntRange) -> Pat {
        if range.is_singleton() {
            Pat::Lit(ty)
        } else {
            Pat::Range(self.construct_range_pat(range, ty))
        }
    }

    /// Function to specifically create a [RangePat] from two specified
    /// boundaries and the type that represents the boundaries. This
    /// function does not consider if the range boundaries are the same
    /// which should yield a [Pat::Lit] instead of a [Pat::Range], if this
    /// is the desired behaviour, then you should use
    /// [`Self::construct_pat_from_range`].
    pub(crate) fn construct_range_pat(&self, range: IntRange, ty: TermId) -> RangePat {
        let (lo, hi) = range.boundaries();
        let bias = range.bias;
        let (lo, hi) = (lo ^ bias, hi ^ bias);

        let (lo, hi) = if let Some(kind) = self.oracle().term_as_int_ty(ty) {
            let ptr_width = self.global_storage().pointer_width;
            let size = kind.size(ptr_width).unwrap().bytes() as usize;

            // Trim the values within the stored range and then create
            // literal terms with those values...
            let lo_val = CONSTANT_MAP.create_int_constant(IntConstant::new(
                IntConstantValue::from_le_bytes(&lo.to_le_bytes()[0..size]),
                kind,
                None,
            ));
            let hi_val = CONSTANT_MAP.create_int_constant(IntConstant::new(
                IntConstantValue::from_le_bytes(&hi.to_le_bytes()[0..size]),
                kind,
                None,
            ));

            let lo = self.builder().create_lit_term(LitTerm::Int { value: lo_val });
            let hi = self.builder().create_lit_term(LitTerm::Int { value: hi_val });

            (lo, hi)
        } else if self.oracle().term_is_char_ty(ty) {
            let size = size_of::<char>();

            // This must be a `char` literal
            let (lo_val, hi_val) = unsafe {
                let lo_val = char::from_u32_unchecked(u32::from_le_bytes(
                    lo.to_le_bytes()[0..size].try_into().unwrap(),
                ));
                let hi_val = char::from_u32_unchecked(u32::from_le_bytes(
                    hi.to_le_bytes()[0..size].try_into().unwrap(),
                ));

                (lo_val, hi_val)
            };

            let lo = self.builder().create_lit_term(LitTerm::Char(lo_val));
            let hi = self.builder().create_lit_term(LitTerm::Char(hi_val));

            (lo, hi)
        } else {
            unreachable!()
        };

        RangePat { lo, hi, end: RangeEnd::Included }
    }

    /// Expand an `or` pattern into a passed [Vec], whilst also
    /// applying the same operation on children patterns.
    fn expand(&self, id: PatId, vec: &mut Vec<PatId>) {
        let reader = self.reader();
        let pat = reader.get_pat(id);

        if let Pat::Or(pats) = pat {
            for inner_pat in pats {
                self.expand(inner_pat, vec);
            }
        } else {
            vec.push(id)
        }
    }

    /// Internal use for expanding an [Pat::Or] into children
    /// patterns. This will also expand any children that are `or`
    /// patterns.
    pub fn flatten_or_pat(&self, pat: PatId) -> Vec<PatId> {
        let mut pats = Vec::new();
        self.expand(pat, &mut pats);

        pats
    }

    /// Function to lower a collection of pattern fields. This is used for
    /// tuple and constructor patterns. This function takes account of whether
    /// fields are named or not, and properly computes the `index` of each
    /// field based on the definition position and whether or not it is a
    /// named argument.
    pub fn deconstruct_pat_fields(&self, fields: PatArgsId, ty: ParamsId) -> Vec<FieldPat> {
        let reader = self.reader();
        let args = reader.get_pat_args_owned(fields);
        let ty_def = reader.get_params_owned(ty);

        let pats = args
            .positional()
            .iter()
            .enumerate()
            // This tries to resolve the `index` of the argument that is being passed
            // within the tuple field. If the tuple has named arguments, then we have
            // to use the parameter list in order to resolve the index. By now it should be
            // verified that no un-named arguments appear after named arguments as this
            // creates an ambiguous ordering of arguments.
            .map(|(index, arg)| -> FieldPat {
                let field = if_chain! {
                    if let Some(name) = arg.name;
                    if let Some((arg_index, _)) = ty_def.get_by_name(name);
                    then {
                        arg_index
                    } else {
                        index
                    }
                };

                FieldPat { index: field, pat: arg.pat }
            })
            .collect_vec();

        pats
    }
}
