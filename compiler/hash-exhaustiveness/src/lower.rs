//! Lowering utilities from a [Pat] into a [DeconstructedPat] and
//! vice versa.
use std::mem::size_of;

use hash_ast::ast::RangeEnd;
use hash_intrinsics::utils::{LitTy, PrimitiveUtils};
use hash_source::{
    constant::{u128_to_int_const, CONSTANT_MAP},
    identifier::IDENTS,
};
use hash_tir::{
    args::{PatArgData, PatArgsId, PatOrCapture},
    arrays::ArrayPat,
    control::{IfPat, OrPat},
    data::{ArrayCtorInfo, CtorDefId, CtorPat, DataTy},
    environment::{env::AccessToEnv, stores::StoreId},
    lits::{CharLit, IntLit, LitPat, StrLit},
    params::ParamsId,
    pats::{Pat, PatId, RangePat, Spread},
    scopes::BindingPat,
    tuples::{TuplePat, TupleTy},
    ty_as_variant,
    tys::{Ty, TyId},
    utils::{common::CommonUtils, AccessToUtils},
};
use hash_utils::{
    itertools::Itertools,
    smallvec::SmallVec,
    store::{SequenceStoreKey, Store, TrivialSequenceStoreKey},
};

use super::{
    constant::Constant,
    construct::DeconstructedCtor,
    deconstruct::DeconstructedPat,
    fields::Fields,
    list::{Array, ArrayKind},
    range::IntRange,
};
use crate::{storage::DeconstructedPatId, usefulness::MatchArm, ExhaustivenessChecker};

/// Expand an `or` pattern into a passed [Vec], whilst also
/// applying the same operation on children patterns.
fn expand_or_pat(id: PatId, vec: &mut Vec<PatId>) {
    if let Pat::Or(OrPat { alternatives }) = id.value() {
        for alternative in alternatives.iter() {
            expand_or_pat(alternative.assert_pat(), vec);
        }
    } else {
        vec.push(id)
    }
}

/// Internal use for expanding an [Pat::Or] into children
/// patterns. This will also expand any children that are `or`
/// patterns.
fn flatten_or_pat(pat: PatId) -> Vec<PatId> {
    let mut pats = Vec::new();
    expand_or_pat(pat, &mut pats);

    pats
}

/// Representation of a field within a collection of patterns.
#[derive(Debug, Clone)]
pub struct FieldPat {
    /// Relative to the associated definition
    pub(crate) index: usize,

    /// Pattern associated with this field
    pub(crate) pat: PatId,
}

impl<'tc> ExhaustivenessChecker<'tc> {
    /// Performs a lowering operation on all of the specified branches.
    ///
    /// This takes in the `term` which is the type of the subject.
    pub(crate) fn lower_pats_to_arms(&self, pats: &[PatId], ty: TyId) -> Vec<MatchArm> {
        pats.iter()
            .map(|id| {
                let destructed_pat = self.deconstruct_pat(ty, *id);
                let pat = self.deconstructed_pat_store().create(destructed_pat);

                MatchArm {
                    deconstructed_pat: pat,
                    has_guard: matches!(id.value(), Pat::If(_)),
                    id: *id,
                }
            })
            .collect_vec()
    }

    /// Convert a [Pat] into a [DeconstructedPat].
    pub(crate) fn deconstruct_pat(&self, ty_id: TyId, pat_id: PatId) -> DeconstructedPat {
        let (ctor, fields) = match pat_id.value() {
            Pat::Binding(_) => (DeconstructedCtor::Wildcard, vec![]),
            Pat::Range(range) => {
                let range = self.lower_pat_range(ty_id, range);
                (DeconstructedCtor::IntRange(range), vec![])
            }
            Pat::Lit(lit_pat) => match lit_pat {
                LitPat::Str(lit) => (DeconstructedCtor::Str(lit.interned_value()), vec![]),
                LitPat::Int(lit) => {
                    let value = Constant::from_int(lit.interned_value(), ty_id);
                    let range = self.make_range_from_constant(value);
                    (DeconstructedCtor::IntRange(range), vec![])
                }
                LitPat::Char(lit) => {
                    let value = Constant::from_char(lit.value(), ty_id);
                    let range = self.make_range_from_constant(value);
                    (DeconstructedCtor::IntRange(range), vec![])
                }
            },
            Pat::Tuple(TuplePat { data, .. }) => {
                // We need to read the tuple type from the ctx type and then create
                // wildcard fields for all of the inner types
                let tuple_ty = ty_as_variant!(ty, ty_id.value(), Tuple);
                let fields = self.deconstruct_pat_fields(data, tuple_ty.data);

                // Create wild-cards for all of the tuple inner members
                let mut wilds: SmallVec<[_; 2]> = tuple_ty
                    .data
                    .borrow()
                    .iter()
                    .map(|param| self.wildcard_from_ty(param.ty))
                    .collect();

                // For each provided field, we want to recurse and lower the pattern further
                for field in fields {
                    wilds[field.index] = self.deconstruct_pat(wilds[field.index].ty, field.pat);
                }

                (DeconstructedCtor::Single, wilds.to_vec())
            }
            Pat::Ctor(CtorPat { ctor, ctor_pat_args: args, .. }) => {
                let params = ctor.borrow().params;

                // Lower the fields by resolving what positions the
                // actual fields are with the reference of the
                // constructor's type...
                let fields = self.deconstruct_pat_fields(args, params);

                // Create wild-cards for all of the tuple inner members
                let mut wilds: SmallVec<[_; 2]> =
                    params.borrow().iter().map(|param| self.wildcard_from_ty(param.ty)).collect();

                // For each provided field, we want to recurse and lower
                // the pattern further
                for field in fields {
                    wilds[field.index] = self.deconstruct_pat(wilds[field.index].ty, field.pat);
                }

                let CtorDefId(ctor_defs, index) = ctor;
                let ctor = if index != 0 || ctor_defs.len() > 1 {
                    DeconstructedCtor::Variant(ctor.1)
                } else {
                    DeconstructedCtor::Single
                };

                (ctor, wilds.to_vec())
            }
            Pat::Array(ArrayPat { pats, spread }) => {
                let mut prefix = vec![];
                let mut suffix = vec![];

                let Some(ArrayCtorInfo { element_ty, .. }) = self.try_use_ty_as_array_ty(ty_id)
                else {
                    panic!("Expected array type")
                };

                let spread_index =
                    if let Some(Spread { index, .. }) = spread { index as isize } else { -1 };

                for (index, pat) in pats.borrow().iter().enumerate() {
                    let deconstructed_pat = self.deconstruct_pat(element_ty, pat.assert_pat());

                    // If the index is `-1`, this will always push to the prefix which
                    // is what should happen if no spread pattern is present.
                    if (index as isize) > spread_index {
                        prefix.push(deconstructed_pat);
                    } else {
                        suffix.push(deconstructed_pat);
                    }
                }

                // If we saw a `...` then we can't be sure of the list length and
                // so it is now considered to be variable length
                let kind = if spread.is_some() {
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
                let pats = flatten_or_pat(pat_id);

                // @@Correctness: does it make sense to pass in this `ctx` since the
                // type is the type of the `or` pattern and not each pat itself, but also
                // it should be that the union-ty is simplified into a single term?
                let fields = pats.iter().map(|pat| self.deconstruct_pat(ty_id, *pat)).collect_vec();

                (DeconstructedCtor::Or, fields)
            }
            Pat::If(IfPat { pat, .. }) => {
                let pat = self.deconstruct_pat(ty_id, pat);
                pat.has_guard.set(true);

                return pat;
            }
        };

        let ctor = self.ctor_store().create(ctor);

        // Now we need to put them in the store...
        DeconstructedPat::new(
            ctor,
            Fields::from_iter(
                fields.into_iter().map(|field| self.deconstructed_pat_store().create(field)),
            ),
            ty_id,
            Some(pat_id),
        )
    }

    // Convert a [DeconstructedPat] into a [Pat].
    pub(crate) fn construct_pat(&self, pat: DeconstructedPatId) -> PatId {
        let deconstructed_store = self.deconstructed_pat_store();
        let ctor_store = self.ctor_store();

        deconstructed_store.map_fast(pat, |deconstructed| {
            let DeconstructedPat {ty, fields, ..} = deconstructed;

            // Short-circuit, if the pattern already has an associated `PatId`...
            if deconstructed.id.is_some() {
                return deconstructed.id.unwrap();
            }

            ctor_store.map_fast(deconstructed.ctor, |ctor| {
                let pat = match ctor {
                    DeconstructedCtor::Single | DeconstructedCtor::Variant(_) => {
                        match ty.value() {
                            Ty::Data(DataTy { data_def, args }) => {
                                let ctor_def_id = data_def.borrow().ctors.assert_defined();

                                // We need to reconstruct the ctor-def-id...
                                let variant_idx = match ctor {
                                    DeconstructedCtor::Single => 0,
                                    DeconstructedCtor::Variant(idx) => *idx,
                                    _ => unreachable!()
                                };
                                let ctor = CtorDefId(ctor_def_id, variant_idx);
                                let (pats, spread) = self.construct_pat_args(fields, ctor.borrow().params);

                                Pat::Ctor(CtorPat { ctor, ctor_pat_args: pats, ctor_pat_args_spread: spread, data_args: args })
                            }
                            Ty::Tuple(TupleTy { data }) => {
                                let (pats, spread) = self.construct_pat_args(fields, data);
                                Pat::Tuple(TuplePat { data: pats, data_spread: spread })
                            }
                            _ => unreachable!()
                        }
                    }
                    DeconstructedCtor::IntRange(range) => self.construct_pat_from_range(*ty, *range),
                    DeconstructedCtor::Str(str) => Pat::Lit(LitPat::Str(StrLit::from(*str))),
                    DeconstructedCtor::Array(Array { kind }) => {
                        let children = fields.iter_patterns().map(|p| self.construct_pat(p).into());
                        let pats = self.new_pat_list(children);

                        match kind {
                            ArrayKind::Fixed(_) => {
                                Pat::Array(ArrayPat { pats, spread: None })
                            }
                            ArrayKind::Var(prefix, _) => {
                                Pat::Array(ArrayPat { pats, spread: Some(Spread { name: self.new_symbol(IDENTS.underscore), index: *prefix }) })
                            }
                        }
                    }
                    DeconstructedCtor::Wildcard | DeconstructedCtor::NonExhaustive => Pat::Binding(BindingPat { name: self.new_symbol(IDENTS.underscore), is_mutable: false }),
                    DeconstructedCtor::Or => {
                        panic!("cannot convert an `or` deconstructed pat back into pat")
                    }
                    DeconstructedCtor::Missing => panic!(
                        "trying to convert a `Missing` constructor into a `Pat`; this is probably a bug, `Missing` should have been processed in `apply_ctors`"
                    ),
                };

                // Now put the pat on the store and return it
                self.new_pat(pat)
            })
        })
    }

    /// Construct pattern arguments from provided [ParamsId].
    fn construct_pat_args(&self, fields: &Fields, params: ParamsId) -> (PatArgsId, Option<Spread>) {
        // Construct the inner arguments to the constructor by iterating over the
        // pattern fields within the pattern. If possible, lookup the name of the
        // field by using the nominal definition attached to the pattern.
        let fields = fields
            .iter_patterns()
            .enumerate()
            .filter(|(_, p)| !self.get_deconstructed_pat_ctor(*p).is_wildcard())
            .map(|(index, p)| PatArgData {
                target: self.get_param_index((params, index).into()),
                pat: self.construct_pat(p).into(),
            })
            .collect_vec();

        let field_count = fields.len();
        let args = self.param_utils().create_pat_args(fields.into_iter());

        // @@Todo: we need to add a spread pattern if the number of added fields
        // mismatches the total number of params in order to signify that some
        // number of fields were omitted for display purposes.
        if field_count != params.len() {
            (args, Some(Spread { name: self.new_fresh_symbol(), index: field_count }))
        } else {
            (args, None)
        }
    }

    /// Lower a [RangePat] into [IntRange]. This function expects that
    /// the [RangePat] was already validated, and so this function will
    /// read `lo`, and `hi` terms, convert them into bytes and put them
    /// into the [IntRange]
    pub fn lower_pat_range(&self, ty: TyId, range: RangePat) -> IntRange {
        let RangePat { lo, hi, end } = range;

        let term_to_u128 = |lit| {
            // The only types we support we support within ranges is currently a
            // `char` and `int` types
            match lit {
                LitPat::Char(char) => Constant::from_char(char.value(), ty).data(),
                LitPat::Int(int) => Constant::from_int(int.interned_value(), ty).data(),
                _ => unreachable!(),
            }
        };

        let lo = term_to_u128(lo);
        let hi = term_to_u128(hi);
        self.make_int_range(ty, lo, hi, &end)
    }

    /// Convert [IntRange] into a [Pat] by judging the given
    /// type that is stored within the parent [DeconstructedPat].
    pub fn construct_pat_from_range(&self, ty: TyId, range: IntRange) -> Pat {
        if range.is_singleton() {
            // `ubig` and `ibig` won't appear here since the range will never become
            // a singleton, and in fact the range will never be constructed from a
            // `ubig` or `ibig` type.
            match self.try_use_ty_as_lit_ty(ty).unwrap() {
                LitTy::I8
                | LitTy::U8
                | LitTy::I16
                | LitTy::U16
                | LitTy::I32
                | LitTy::U32
                | LitTy::I64
                | LitTy::U64
                | LitTy::I128
                | LitTy::U128 => {
                    let (lo, _) = range.boundaries();
                    let bias = range.bias;
                    let lo = lo ^ bias;

                    Pat::Lit(LitPat::Int(IntLit::from_value(CONSTANT_MAP.create_int(lo.into()))))
                }
                LitTy::Char => {
                    let (lo, _) = range.boundaries();
                    let literal = unsafe { char::from_u32_unchecked(lo as u32) };

                    Pat::Lit(LitPat::Char(CharLit::from_literal(literal)))
                }
                _ => unreachable!(),
            }
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
    pub(crate) fn construct_range_pat(&self, range: IntRange, ty: TyId) -> RangePat {
        let (lo, hi) = range.boundaries();
        let bias = range.bias;
        let (lo, hi) = (lo ^ bias, hi ^ bias);

        let (lo, hi) = match self.try_use_ty_as_lit_ty(ty).unwrap() {
            LitTy::I8
            | LitTy::U8
            | LitTy::I16
            | LitTy::U16
            | LitTy::I32
            | LitTy::U32
            | LitTy::I64
            | LitTy::U64
            | LitTy::U128
            | LitTy::I128
            | LitTy::IBig
            | LitTy::UBig => {
                let kind = self.try_use_ty_as_int_ty(ty).unwrap();
                let ptr_width = self.target().ptr_size();

                let lo_val = u128_to_int_const(lo, kind, ptr_width);
                let hi_val = u128_to_int_const(hi, kind, ptr_width);
                let lo = LitPat::Int(IntLit::from_value(lo_val));
                let hi = LitPat::Int(IntLit::from_value(hi_val));

                (lo, hi)
            }
            LitTy::Char => {
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

                let lo = LitPat::Char(CharLit::from_literal(lo_val));
                let hi = LitPat::Char(CharLit::from_literal(hi_val));

                (lo, hi)
            }
            _ => unreachable!(),
        };

        RangePat { lo, hi, end: RangeEnd::Included }
    }

    /// Function to lower a collection of pattern fields. This is used for
    /// tuple and constructor patterns. This function takes account of whether
    /// fields are named or not, and properly computes the `index` of each
    /// field based on the definition position and whether or not it is a
    /// named argument.
    pub fn deconstruct_pat_fields(&self, fields: PatArgsId, params_id: ParamsId) -> Vec<FieldPat> {
        fields
            .borrow()
            .iter()
            .enumerate()
            .filter(|(_, arg)| matches!(arg.pat, PatOrCapture::Pat(_)))
            // This tries to resolve the `index` of the argument that is being passed
            // within the tuple field. If the tuple has named arguments, then we have
            // to use the parameter list in order to resolve the index. By now it should be
            // verified that no un-named arguments appear after named arguments as this
            // creates an ambiguous ordering of arguments.
            .map(|(index, arg)| -> FieldPat {
                let field = if let Some(arg_index) =
                    self.try_get_actual_param_index(params_id, arg.target)
                {
                    arg_index
                } else {
                    index
                };

                FieldPat { index: field, pat: arg.pat.assert_pat() }
            })
            .collect_vec()
    }
}
