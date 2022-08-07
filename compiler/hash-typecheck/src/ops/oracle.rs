//! Functionality related to determining properties about terms and other
//! constructs.
use hash_ast::ast::{IntTy, ParamOrigin};

use super::AccessToOps;
use crate::storage::{terms::TermId, AccessToStorage, StorageRef};

pub struct Oracle<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for Oracle<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> Oracle<'tc> {
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// If the term is a string type.
    pub fn term_is_str_ty(&self, term: TermId) -> bool {
        self.unifier().terms_are_equal(term, self.core_defs().str_ty())
    }

    /// If the term is a char type.
    pub fn term_is_char_ty(&self, term: TermId) -> bool {
        self.unifier().terms_are_equal(term, self.core_defs().char_ty())
    }

    /// If the term is an integer type, returns its [IntTy].
    pub fn term_as_int_ty(&self, term: TermId) -> Option<IntTy> {
        macro_rules! check_for_tys {
            ($($ty:ident => $variant:ident),* $(,)?) => {
                $(
                    if self.unifier().terms_are_equal(term, self.core_defs().$ty()) {
                        return Some(IntTy::$variant);
                    }
                )*
            };
        }

        // Check if it is each of the integer types.
        check_for_tys!(
                i8_ty => I8,
                i16_ty => I16,
                i32_ty => I32,
                i64_ty => I64,
                isize_ty => ISize,
                u8_ty => U8,
                u16_ty => U16,
                u32_ty => U32,
                u64_ty => U64,
                usize_ty => USize,
        );

        // Otherwise not an int
        None
    }

    /// If the term is a list type, returns its inner type.
    pub fn term_as_list_ty(&self, term: TermId) -> Option<TermId> {
        let list_inner_ty = self.builder().create_unresolved_term();
        let builder = self.builder();
        let list_ty = builder.create_app_ty_fn_term(
            self.core_defs().list_ty_fn(),
            builder.create_args(
                [builder.create_nameless_arg(builder.create_unresolved_term())],
                ParamOrigin::TyFn,
            ),
        );
        let sub = self.unifier().unify_terms(list_ty, term).ok()?;
        Some(self.substituter().apply_sub_to_term(&sub, list_inner_ty))
    }

    /// If the term is the never type.
    pub fn term_is_never_ty(&self, term: TermId) -> bool {
        self.unifier().terms_are_equal(term, self.builder().create_never_ty())
    }
}
