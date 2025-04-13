//! Utilities that are used by the discovery pass.

use hash_ast::ast;
use hash_attrs::{
    attr::{ReprAttr, attr_store},
    builtin::attrs,
};
use hash_const_eval::Const;
use hash_repr::ty::ToReprTy;
use hash_target::{
    abi::Integer,
    discriminant::{Discriminant, DiscriminantKind},
    primitives::IntTy,
    size::Size,
};
use hash_tir::{
    intrinsics::utils::create_term_from_const,
    tir::{HasAstNodeId, Node, NodeOrigin, TermId},
};
use hash_utils::num_bigint::BigInt;

use super::DiscoveryPass;
use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult},
    env::SemanticEnv,
};

impl<E: SemanticEnv> DiscoveryPass<'_, E> {
    /// Compute the type of the discriminant from a given [`ast::EnumDef`].
    ///
    /// The algorithm follows the following rules:
    ///
    /// 1. If the enum has a `repr` attribute, then we use the type that is
    ///    specified in the attribute.
    ///
    /// 2. Otherwise, loop over all of the variants, and find the largest
    ///    discriminant value.
    ///
    /// 3. If no discriminant values are specified, then we assume that the
    ///    discriminant type is the smallest unsigned integer that can represent
    ///    the number of variants that the enum has.
    ///
    /// 4. Otherwise, we compute the minimum number of bits required to fit the
    ///    discriminant value, and construct an integer type from it.
    ///
    /// @@Cleanup: ideally we should sync with using the algorithm specified in
    /// compiler/hash-ir/src/ty.rs in function (compute_discriminant_ty).   
    ///   
    pub(super) fn compute_discriminant_ty(
        &self,
        def: ast::AstNodeRef<ast::EnumDef>,
    ) -> SemanticResult<Node<IntTy>> {
        // Firstly, we check if the def has a `repr` attribute which indicates which
        // primitive integer type to use for the discriminant.
        if let Some(repr_hint) = attr_store().get_attr(def.id, attrs::REPR) {
            let repr = ReprAttr::parse(&repr_hint).unwrap(); // already checked earlier!

            if let ReprAttr::Int(ty) = repr {
                return Ok(Node::at(ty, NodeOrigin::Given(repr_hint.origin)));
            }
        }

        // Otherwise we have to loop through all of the variants, and check if they have
        // a direct discriminant value...
        let mut prev_discr = None;
        let mut has_discriminant_attr = false;
        let mut is_signed = false;

        for variant in def.entries.iter() {
            if let Some(discr_annot) = attr_store().get_attr(variant.id(), attrs::DISCRIMINANT) {
                let discr = discr_annot.get_arg(0).unwrap().as_big_int();
                has_discriminant_attr = true;
                is_signed |= discr < BigInt::from(0);

                // Otherwise, we set the previous discriminant to the current one.
                prev_discr = Some(discr);
            } else if let Some(prev) = prev_discr {
                // We just add one to the the biggest discriminant we have seen so far.
                prev_discr = Some(prev + 1);
            } else {
                // Initialise it with a zero if no initial discriminant is given.
                prev_discr = Some(BigInt::from(0));
            }
        }

        // If we get no variants, we still assume that the discriminant will use the
        // smallest unsigned integer.
        let max_discr = prev_discr.unwrap_or_default();
        let min_bits = max_discr.bits();

        // If we didn't have any registered discriminants, then we assume that the
        // type of the discriminants is the smallest unsigned integer that can represent
        // the number of variants.
        //
        // @@NonExhaustive: if we add a `non_exhaustive` attribute, what is the type
        // that we assume now, is it perhaps an i32 or isize?
        if !has_discriminant_attr || min_bits == 0 {
            let int = Integer::fit_unsigned(def.entries.len() as u128);
            return Ok(Node::at(IntTy::from_integer(int, false), NodeOrigin::Generated));
        }

        // Check whether the discriminant can fit in a `u8`, `u16`, `u32`, `u64`,
        // `u128`.
        let Some(int) = Integer::from_size(Size::from_bits(min_bits)) else {
            panic!("error: discriminant too large!")
        };

        Ok(Node::at(IntTy::from_integer(int, is_signed), NodeOrigin::Generated))
    }

    /// Check if any of the discriminants that are assigned to a variant are
    /// duplicated across the enum definition (whether by overflow or by
    /// explicit means).
    pub(super) fn check_enum_discriminants(
        &self,
        discrs: &[Node<Discriminant>],
        _discr_ty: Node<IntTy>,
    ) -> SemanticResult<()> {
        let mut i = 0;

        // Check if any of the discriminants have been used more than once.
        while i < discrs.len() {
            // @@Todo: maybe make this an error collector of sorts?

            let mut o = i + 1;
            while o < discrs.len() {
                if discrs[i].value == discrs[o].value {
                    return Err(SemanticError::DuplicateEnumDiscriminant {
                        original: discrs[i].origin.span().unwrap(),
                        offending: discrs[o].origin.span().unwrap(),
                        value: discrs[o].data,
                    });
                }

                o += 1;
            }

            i += 1;
        }

        Ok(())
    }

    /// Compute the value of the discriminant for a variant taking into account
    /// the computed discriminant type, and an optional previous
    /// discriminant value.
    pub(super) fn compute_discriminant_for_variant(
        &self,
        variant: &ast::AstNode<ast::EnumDefEntry>,
        discr_ty: Node<IntTy>,
        prev_discr: &mut Option<Discriminant>,
        discrs: &mut Vec<Node<Discriminant>>,
    ) -> SemanticResult<TermId> {
        // Default to using a `0` discriminant if none was specified.
        let prev = prev_discr.unwrap_or_else(|| Discriminant::initial(*discr_ty));

        // if there is a discriminant value for the given variant and
        // then set it as the last discriminant. If the variant does not have an
        // explicit discriminant, then we simply use the last known discriminant
        // and increment it by one.
        if let Some(discr_annot) = attr_store().get_attr(variant.id(), attrs::DISCRIMINANT) {
            let origin = NodeOrigin::Given(discr_annot.origin);
            let arg = discr_annot.get_arg(0).unwrap();

            let scalar = arg.value.as_scalar();
            let value = scalar.to_bits(scalar.size()).unwrap();
            let mut next_discr =
                Discriminant { value, ty: *discr_ty, kind: DiscriminantKind::Explicit };

            if next_discr.has_overflowed(self.env) {
                return Err(SemanticError::EnumDiscriminantOverflow {
                    location: origin.span().unwrap(),
                    annotation_origin: discr_ty.span(),
                    discriminant: next_discr,
                });
            } else if discr_ty.is_signed() {
                // @@Hack @@TIRConsts: we manually truncate the value of the discriminant to
                // being a u128 so that we can detect whether it overflows
                // or not. However, we should remove this when we can use
                // the `Const` format in the TIR which will automatically perform
                // the truncation.
                next_discr.value = discr_ty.size(self.target().ptr_size()).sign_extend(value);
            }

            *prev_discr = Some(next_discr);
            discrs.push(Node::at(next_discr, origin));
            Ok(create_term_from_const(arg.value, origin))
        } else {
            let origin = NodeOrigin::Given(variant.id());

            // We want to check if we are starting from the very beginning which
            // should actually use the zero discriminant.
            let (next_discr, _) =
                if prev_discr.is_some() { prev.checked_add(self.env, 1) } else { (prev, false) };

            // @@Hack: we convert the `u128` into an int constant
            // with the given discriminant type, later this should be
            // replaced by the new constant representation.
            let constant =
                Const::from_scalar_like(next_discr.value, (*discr_ty).to_repr_ty(), self.target());

            *prev_discr = Some(next_discr);
            discrs.push(Node::at(next_discr, origin));
            Ok(create_term_from_const(constant, origin))
        }
    }
}
