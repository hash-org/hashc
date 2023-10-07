//! Utilities that are used by the discovery pass.

use hash_ast::ast;
use hash_attrs::{
    attr::{attr_store, ReprAttr},
    builtin::attrs,
};
use hash_target::{abi::Integer, discriminant::Discriminant, primitives::IntTy, size::Size};
use hash_tir::tir::{HasAstNodeId, Node, NodeOrigin};
use num_bigint::BigInt;

use super::DiscoveryPass;
use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult},
    env::SemanticEnv,
};

impl<'env, E: SemanticEnv> DiscoveryPass<'env, E> {
    /// Compute the type of the discriminant from a given
    /// [`ast::EnumDef`].
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

        for variant in def.entries.iter() {
            if let Some(discr_annot) = attr_store().get_attr(variant.id(), attrs::DISCRIMINANT) {
                let discr = discr_annot.get_arg(0).unwrap().as_int().big_value();
                has_discriminant_attr = true;

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

        let min_bits = prev_discr.unwrap().bits();
        // If we didn't have any registered discriminants, then we assume that the
        // type of the discriminants is the smallest unsigned integer that can represent
        // the number of variants.
        //
        // @@NonExhaustive: if we add a `non_exhaustive` attribute, what is the type
        // that we assume now, is it perhaps an i32 or isize?
        if has_discriminant_attr || min_bits == 0 {
            let int = Integer::fit_unsigned(def.entries.len() as u128);
            return Ok(Node::at(IntTy::from_integer(int, false), NodeOrigin::Generated));
        }

        // Check whether the discriminant can fit in a `u8`, `u16`, `u32`, `u64`,
        // `u128`.
        let Some(int) = Integer::from_size(Size::from_bits(min_bits)) else {
            panic!("error: discriminant too large!")
        };

        Ok(Node::at(IntTy::from_integer(int, true), NodeOrigin::Generated))
    }

    /// Check if any of the discriminants that are assigned to a variant are
    /// duplicated across the enum definition (whether by overflow or by
    /// explicit means).
    pub(super) fn check_enum_discriminants(
        &self,
        discrs: &[Node<Discriminant>],
        discr_ty: Node<IntTy>,
    ) -> SemanticResult<()> {
        let discr_ty_size = discr_ty.data.size(self.target().ptr_size());

        // Check if any of the discriminants have been used more than once.
        let mut i = 0;
        while i < discrs.len() {
            let raw_value = discrs[i].value;
            // @@Todo: maybe make this an error collector of sorts?

            // @@Hack @@TIRConsts: we manually truncate the value of the discriminant to
            // being a u128 so that we can detect whether it overflows
            // or not. However, we should remove this when we can use
            // the `Const` format in the TIR which will automatically perform
            // the truncation.
            if discr_ty_size.truncate(raw_value) != raw_value {
                return Err(SemanticError::EnumDiscriminantOverflow {
                    location: discrs[i].span().unwrap(),
                    annotation_origin: discr_ty.span(),
                    discriminant: *discrs[i],
                });
            }

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
}
