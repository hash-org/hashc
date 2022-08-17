//! Functionality related to determining properties about terms and other
//! constructs.
use hash_ast::ast::{IntTy, ParamOrigin};

use super::AccessToOps;
use crate::storage::{
    primitives::{EnumDef, Level0Term, Level1Term, NominalDef, ScopeVar, StructDef, Term, TupleTy},
    terms::TermId,
    AccessToStorage, StorageRef,
};

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

    /// If the term is a scope variable.
    ///
    /// **Note**: assumes that the term is simplified.
    pub fn term_as_scope_var(&self, term: TermId) -> Option<ScopeVar> {
        match self.reader().get_term(term) {
            Term::ScopeVar(scope_var) => Some(scope_var),
            _ => None,
        }
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

    /// If the term is a [Level1Term::Tuple], return it.
    pub fn term_as_tuple_ty(&self, term: TermId) -> Option<TupleTy> {
        let reader = self.reader();

        match reader.get_term(term) {
            Term::Level1(Level1Term::Tuple(ty)) => Some(ty),
            _ => None,
        }
    }

    /// If the term is the never type.
    pub fn term_is_never_ty(&self, term: TermId) -> bool {
        self.unifier().terms_are_equal(term, self.builder().create_never_ty())
    }

    /// If the term is a literal term.
    pub fn term_is_literal(&self, term: TermId) -> bool {
        let reader = self.reader();

        matches!(reader.get_term(term), Term::Level0(Level0Term::Lit(_)))
    }

    /// Get a [Term] as a [StructDef].
    pub fn term_as_struct_def(&self, term: TermId) -> Option<StructDef> {
        match self.reader().get_term(term) {
            Term::Level1(Level1Term::NominalDef(def)) => match self.reader().get_nominal_def(def) {
                NominalDef::Struct(struct_def) => Some(struct_def),
                _ => None,
            },
            _ => None,
        }
    }

    /// Get a [Term] as a [EnumDef].
    pub fn term_as_enum_def(&self, term: TermId) -> Option<EnumDef> {
        match self.reader().get_term(term) {
            Term::Level1(Level1Term::NominalDef(def)) => match self.reader().get_nominal_def(def) {
                NominalDef::Enum(enum_def) => Some(enum_def),
                _ => None,
            },
            _ => None,
        }
    }

    /// Get a [Term] as a [NominalDef].
    pub fn term_as_nominal_def(&self, term: TermId) -> Option<NominalDef> {
        match self.reader().get_term(term) {
            Term::Level1(Level1Term::NominalDef(def)) => Some(self.reader().get_nominal_def(def)),
            _ => None,
        }
    }
}
