//! Utilities that are used by the discovery pass.

use hash_ast::ast;
use hash_attrs::{
    attr::{attr_store, ReprAttr},
    builtin::attrs,
};
use hash_target::{abi::Integer, primitives::IntTy, size::Size};
use num_bigint::BigInt;

use super::DiscoveryPass;
use crate::{diagnostics::definitions::SemanticResult, env::SemanticEnv};

impl<'env, E: SemanticEnv> DiscoveryPass<'env, E> {
    /// Compute the type of the discriminant from a given
    /// [`ast::EnumDef`].
    pub(super) fn compute_discriminant_ty(
        &self,
        def: ast::AstNodeRef<ast::EnumDef>,
    ) -> SemanticResult<IntTy> {
        // Firstly, we check if the def has a `repr` attribute which indicates which
        // primitive integer type to use for the discriminant.
        if let Some(repr_hint) = attr_store().get_attr(def.id, attrs::REPR) {
            let repr = ReprAttr::parse(&repr_hint).unwrap(); // already checked earlier!

            if let ReprAttr::Int(ty) = repr {
                return Ok(ty);
            }
        }

        // Otherwise we have to loop through all of the variants, and check if they have
        // a direct discriminant value...
        let mut prev_discr = None;
        let mut has_discriminant_attr = false;

        for variant in def.entries.iter() {
            if let Some(discr_annot) = attr_store().get_attr(variant.id(), attrs::DISCRIMINANT) {
                let discr = discr_annot.get_arg_as_int(0).unwrap().big_value();
                has_discriminant_attr = true;

                // If we got a previous value, then we have to check
                // whether it doesn't overlap with the previous discriminant.
                if let Some(prev) = prev_discr {
                    if discr <= prev {
                        // Error!
                        panic!("todo: error!")
                    }
                }

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
            return Ok(IntTy::from_integer(int, false));
        }

        // Check whether the discriminant can fit in a `u8`, `u16`, `u32`, `u64`,
        // `u128`.
        let Some(int) = Integer::from_size(Size::from_bits(min_bits)) else {
            panic!("error: discriminant too large!")
        };

        Ok(IntTy::from_integer(int, true))
    }
}
