//! Lowering utilities from a [Pat] into a [DeconstructedPat] and
//! vice versa.
use std::mem::size_of;

use hash_ast::ast::RangeEnd;
use hash_layout::{
    constant::Const,
    ty::{ReprTy, ReprTyId, COMMON_REPR_TYS},
};
use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_tir::{
    intrinsics::utils::{
        numeric_max_val_of_lit, numeric_min_val_of_lit, try_use_ty_as_array_ty,
        try_use_ty_as_lit_ty, LitTy,
    },
    term_as_variant,
    tir::*,
};
use hash_utils::{itertools::Itertools, smallvec::SmallVec};

use super::{
    construct::DeconstructedCtor,
    deconstruct::DeconstructedPat,
    fields::Fields,
    list::{Array, ArrayKind},
    range::IntRange,
};
use crate::{
    storage::DeconstructedPatId, usefulness::MatchArm, ExhaustivenessChecker, ExhaustivenessEnv,
};

/// Expand an `or` pattern into a passed [Vec], whilst also
/// applying the same operation on children patterns.
fn expand_or_pat(id: PatId, vec: &mut Vec<PatId>) {
    if let Pat::Or(OrPat { alternatives }) = *id.value() {
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

impl<E: ExhaustivenessEnv> ExhaustivenessChecker<'_, E> {
    /// Performs a lowering operation on all of the specified branches.
    ///
    /// This takes in the `term` which is the type of the subject.
    pub(crate) fn lower_pats_to_arms(&mut self, pats: &[PatId], ty: TyId) -> Vec<MatchArm> {
        pats.iter()
            .map(|id| {
                let destructed_pat = self.deconstruct_pat(ty, *id);
                let pat = self.make_pat(destructed_pat);

                MatchArm {
                    deconstructed_pat: pat,
                    has_guard: matches!(*id.value(), Pat::If(_)),
                    id: *id,
                }
            })
            .collect_vec()
    }

    /// Convert a [Pat] into a [DeconstructedPat].
    pub(crate) fn deconstruct_pat(&mut self, ty_id: TyId, pat_id: PatId) -> DeconstructedPat {
        let (ctor, fields) = match *pat_id.value() {
            Pat::Binding(_) => (DeconstructedCtor::Wildcard, vec![]),
            Pat::Range(range) => {
                let range = self.lower_pat_range(ty_id, range);
                (DeconstructedCtor::IntRange(range), vec![])
            }
            Pat::Lit(LitPat(lit)) => match *lit.value() {
                Lit::Const(constant) => match constant.ty().value() {
                    ty if ty.is_switchable() => {
                        let range = self.make_range_from_constant(constant);
                        (DeconstructedCtor::IntRange(range), vec![])
                    }
                    _ if constant.ty() == COMMON_REPR_TYS.str => {
                        (DeconstructedCtor::Str(constant.as_alloc()), vec![])
                    }
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            },
            Pat::Tuple(TuplePat { data, .. }) => {
                // We need to read the tuple type from the ctx type and then create
                // wildcard fields for all of the inner types
                let tuple_ty = term_as_variant!(ty, ty_id.value(), TupleTy);
                let fields = self.deconstruct_pat_fields(data, tuple_ty.data);

                // Create wild-cards for all of the tuple inner members
                let mut wilds: SmallVec<[_; 2]> = tuple_ty
                    .data
                    .elements()
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
                let mut wilds: SmallVec<[_; 2]> = params
                    .elements()
                    .borrow()
                    .iter()
                    .map(|param| self.wildcard_from_ty(param.ty))
                    .collect();

                // For each provided field, we want to recurse and lower
                // the pattern further
                for field in fields {
                    wilds[field.index] = self.deconstruct_pat(wilds[field.index].ty, field.pat);
                }

                let CtorDefId(ctor_defs, index) = ctor;
                let ctor = if index != 0 || ctor_defs.len() > 1 {
                    DeconstructedCtor::Variant(ctor.1 as usize)
                } else {
                    DeconstructedCtor::Single
                };

                (ctor, wilds.to_vec())
            }
            Pat::Array(ArrayPat { pats, spread }) => {
                let mut prefix = vec![];
                let mut suffix = vec![];

                let Some(ArrayCtorInfo { element_ty, .. }) = try_use_ty_as_array_ty(ty_id) else {
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

        let ctor = self.make_ctor(ctor);

        // Now we need to put them in the store...
        DeconstructedPat::new(
            ctor,
            Fields::from_iter(fields.into_iter().map(|field| self.make_pat(field))),
            ty_id,
            Some(pat_id),
        )
    }

    // Convert a [DeconstructedPat] into a [Pat].
    pub(crate) fn construct_pat(&self, pat: DeconstructedPatId) -> PatId {
        let DeconstructedPat { ty, fields, ctor, .. } = self.get_pat(pat);

        let ctor = self.get_ctor(*ctor);
        let pat = match ctor {
                    DeconstructedCtor::Single | DeconstructedCtor::Variant(_) => {
                        match *ty.value() {
                            Ty::DataTy(DataTy { data_def, args }) => {
                                let ctor_def_id = data_def.borrow().ctors.assert_defined();

                                // We need to reconstruct the ctor-def-id...
                                let variant_idx = match ctor {
                                    DeconstructedCtor::Single => 0,
                                    DeconstructedCtor::Variant(idx) => *idx,
                                    _ => unreachable!()
                                };
                                let ctor = CtorDefId::new(ctor_def_id.elements(), variant_idx);
                                let (pats, spread) = self.construct_pat_args(fields, ctor.borrow().params);

                                Pat::Ctor(CtorPat { ctor, ctor_pat_args: pats, ctor_pat_args_spread: spread, data_args: args })
                            }
                            Ty::TupleTy(TupleTy { data }) => {
                                let (pats, spread) = self.construct_pat_args(fields, data);
                                Pat::Tuple(TuplePat { data: pats, data_spread: spread })
                            }
                            _ => unreachable!()
                        }
                    }
                    DeconstructedCtor::IntRange(range) => self.construct_pat_from_range(*ty, *range),
                    DeconstructedCtor::Str(str) => Pat::Lit(LitPat(Node::create_gen(Lit::Const(Const::alloc(*str, COMMON_REPR_TYS.str))))),
                    DeconstructedCtor::Array(Array { kind }) => {
                        let children = fields.iter_patterns().map(|p| PatOrCapture::Pat(self.construct_pat(p))).collect_vec();
                        let pats = Node::create_at(PatOrCapture::seq(children), NodeOrigin::Generated);

                        match kind {
                            ArrayKind::Fixed(_) => {
                                Pat::Array(ArrayPat { pats, spread: None })
                            }
                            ArrayKind::Var(prefix, _) => {
                                Pat::Array(ArrayPat { pats, spread: Some(Spread { name: SymbolId::fresh_underscore(NodeOrigin::Generated), index: *prefix }) })
                            }
                        }
                    }
                    DeconstructedCtor::Wildcard | DeconstructedCtor::NonExhaustive => Pat::Binding(BindingPat { name: SymbolId::fresh_underscore(NodeOrigin::Generated), is_mutable: false }),
                    DeconstructedCtor::Or => {
                        panic!("cannot convert an `or` deconstructed pat back into pat")
                    }
                    DeconstructedCtor::Missing => panic!(
                        "trying to convert a `Missing` constructor into a `Pat`; this is probably a bug, `Missing` should have been processed in `apply_ctors`"
                    ),
                };

        // Now put the pat on the store and return it
        Node::create_at(pat, NodeOrigin::Generated)
    }

    /// Construct pattern arguments from provided [ParamsId].
    fn construct_pat_args(&self, fields: &Fields, params: ParamsId) -> (PatArgsId, Option<Spread>) {
        // Construct the inner arguments to the constructor by iterating over the
        // pattern fields within the pattern. If possible, lookup the name of the
        // field by using the nominal definition attached to the pattern.
        let fields = fields
            .iter_patterns()
            .enumerate()
            .filter(|(_, p)| !self.get_pat_ctor(*p).is_wildcard())
            .map(|(index, p)| {
                Node::at(
                    PatArg {
                        target: ParamId::new(params.elements(), index).as_param_index(),
                        pat: self.construct_pat(p).into(),
                    },
                    NodeOrigin::Generated,
                )
            })
            .collect_vec();

        let field_count = fields.len();
        let args = Node::create_at(Node::<PatArg>::seq(fields), NodeOrigin::Generated);

        if field_count != params.len() {
            (
                args,
                Some(Spread { name: SymbolId::fresh(NodeOrigin::Generated), index: field_count }),
            )
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

        let lit_to_u128 = |lit, at_end| {
            // The only types we support we support within ranges is currently a
            // `char` and `int` types
            match lit {
                Some(LitPat(pat)) => match *pat.value() {
                    Lit::Const(constant) => {
                        let scalar = constant.as_scalar();
                        scalar.to_bits(scalar.size()).unwrap()
                    }
                    _ => unreachable!(),
                },
                None if at_end => numeric_max_val_of_lit(self.target(), ty).unwrap(),
                None => numeric_min_val_of_lit(self.target(), ty).unwrap(),
            }
        };

        let lo = lit_to_u128(lo, false);
        let hi = lit_to_u128(hi, true);

        let ty = self.ty_lower().repr_ty_from_tir_ty(ty);
        self.make_int_range(ty, lo, hi, &end)
    }

    /// Convert [IntRange] into a [Pat] by judging the given
    /// type that is stored within the parent [DeconstructedPat].
    pub fn construct_pat_from_range(&self, ty: TyId, range: IntRange) -> Pat {
        if range.is_singleton() {
            // `ubig` and `ibig` won't appear here since the range will never become
            // a singleton, and in fact the range will never be constructed from a
            // `ubig` or `ibig` type.
            match try_use_ty_as_lit_ty(self.target(), ty).unwrap() {
                int_ty if int_ty.is_int() => {
                    let (lo, _) = range.boundaries();
                    let ty = self.ty_lower().repr_ty_from_tir_ty(ty);
                    let bias = self.signed_bias(ty);
                    let lo = lo ^ bias;

                    let val = Const::from_scalar_like(lo, ty, self.target());
                    Pat::Lit(LitPat(Node::create_gen(Lit::Const(val))))
                }
                LitTy::Char => {
                    let (lo, _) = range.boundaries();
                    let val = unsafe { char::from_u32_unchecked(lo as u32) };
                    Pat::Lit(LitPat(Node::create_gen(Lit::Const(Const::char(val)))))
                }
                _ => unreachable!(),
            }
        } else {
            let ty = self.ty_lower().repr_ty_from_tir_ty(ty);
            Pat::Range(self.construct_range_pat(range, ty))
        }
    }

    /// Function to specifically create a [RangePat] from two specified
    /// boundaries and the type that represents the boundaries. This
    /// function does not consider if the range boundaries are the same
    /// which should yield a [Pat::Lit] instead of a [Pat::Range], if this
    /// is the desired behaviour, then you should use
    /// [`Self::construct_pat_from_range`].
    pub(crate) fn construct_range_pat(&self, range: IntRange, ty_id: ReprTyId) -> RangePat {
        let (lo, hi) = range.boundaries();
        let bias = self.signed_bias(ty_id);
        let (lo, hi) = (lo ^ bias, hi ^ bias);

        let (lo, hi) = match ty_id.value() {
            ty if ty.is_integral() => {
                let lo_val = Const::from_scalar_like(lo, ty_id, self.env.target());
                let hi_val = Const::from_scalar_like(hi, ty_id, self.env.target());
                let lo = LitPat(Node::create_gen(Lit::Const(lo_val)));
                let hi = LitPat(Node::create_gen(Lit::Const(hi_val)));

                (lo, hi)
            }
            ReprTy::Char => {
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

                let lo = LitPat(Node::create_gen(Lit::Const(lo_val.into())));
                let hi = LitPat(Node::create_gen(Lit::Const(hi_val.into())));

                (lo, hi)
            }
            _ => unreachable!(),
        };

        RangePat { lo: Some(lo), hi: Some(hi), end: RangeEnd::Included }
    }

    /// Function to lower a collection of pattern fields. This is used for
    /// tuple and constructor patterns. This function takes account of whether
    /// fields are named or not, and properly computes the `index` of each
    /// field based on the definition position and whether or not it is a
    /// named argument.
    fn deconstruct_pat_fields(&self, fields: PatArgsId, params_id: ParamsId) -> Vec<FieldPat> {
        fields
            .elements()
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
                let field = if let Some(arg_index) = params_id.at_param_index(arg.target) {
                    arg_index
                } else {
                    index
                };

                FieldPat { index: field, pat: arg.pat.assert_pat() }
            })
            .collect_vec()
    }
}
