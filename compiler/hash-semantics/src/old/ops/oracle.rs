//! Functionality related to determining properties about terms and other
//! constructs.
use hash_source::{
    constant::{FloatTy, IntTy, SIntTy, UIntTy},
    identifier::Identifier,
};
use hash_tir::old::{
    nominals::{
        EnumDef, EnumVariant, EnumVariantValue, NominalDef, NominalDefId, StructDef, UnitDef,
    },
    scope::ScopeVar,
    terms::{FnTy, Level0Term, Level1Term, Level2Term, Term, TermId, TupleTy},
    trts::TrtDef,
};
use hash_utils::store::Store;

use super::AccessToOps;
use crate::old::{
    diagnostics::macros::tc_panic,
    storage::{AccessToStorage, StorageRef},
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

    /// Check if the [Term] is a primitive type.
    pub fn term_is_primitive(&self, term: TermId) -> bool {
        self.term_is_char_ty(term)
            || self.term_is_bool_ty(term)
            || self.term_is_str_ty(term)
            || self.term_as_int_ty(term).is_some()
            || self.term_as_float_ty(term).is_some()
    }

    /// If the term is a bool type.
    pub fn term_is_bool_ty(&self, term: TermId) -> bool {
        self.unifier().terms_are_equal(term, self.core_defs().bool_ty())
    }

    /// If the term is an integer type, returns its [IntTy].
    pub fn term_as_int_ty(&self, term: TermId) -> Option<IntTy> {
        macro_rules! check_for_tys {
            ($($ty:ident => $variant:expr),* $(,)?) => {
                $(
                    if self.unifier().terms_are_equal(term, self.core_defs().$ty()) {
                        return Some($variant);
                    }
                )*
            };
        }

        // Check if it is each of the integer types.
        check_for_tys!(
                i8_ty => IntTy::Int(SIntTy::I8),
                i16_ty => IntTy::Int(SIntTy::I16),
                i32_ty => IntTy::Int(SIntTy::I32),
                i64_ty => IntTy::Int(SIntTy::I64),
                isize_ty => IntTy::Int(SIntTy::ISize),
                u8_ty => IntTy::UInt(UIntTy::U8),
                u16_ty => IntTy::UInt(UIntTy::U16),
                u32_ty => IntTy::UInt(UIntTy::U32),
                u64_ty => IntTy::UInt(UIntTy::U64),
                usize_ty => IntTy::UInt(UIntTy::USize),
        );

        // Otherwise not an int
        None
    }

    /// If the term is a float type, returns its [FloatTy].
    pub fn term_as_float_ty(&self, term: TermId) -> Option<FloatTy> {
        macro_rules! check_for_tys {
            ($($ty:ident => $variant:expr),* $(,)?) => {
                $(
                    if self.unifier().terms_are_equal(term, self.core_defs().$ty()) {
                        return Some($variant);
                    }
                )*
            };
        }

        // Check if it is each of the integer types.
        check_for_tys!(
            f32_ty => FloatTy::F32,
            f64_ty => FloatTy::F64,
        );

        // Otherwise not a float.
        None
    }

    /// If the term is a list type, returns its inner type.
    pub fn term_as_list_ty(&self, _term: TermId) -> Option<TermId> {
        None
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

    /// If the term is a [StructDef] term.
    pub fn term_is_struct_def(&self, term: TermId) -> bool {
        self.term_as_struct_def(term).is_some()
    }

    /// If the term is a [UnitDef] term.
    pub fn term_is_unit_def(&self, term: TermId) -> bool {
        self.term_as_unit_def(term).is_some()
    }

    /// If the term is an enum type.
    pub fn term_is_enum_def(&self, term: TermId) -> bool {
        self.term_as_enum_def(term).is_some()
    }

    /// If the term is a [`Term::TyOf`], return its inner type.
    pub fn term_as_ty_of(&self, term: TermId) -> Option<TermId> {
        match self.reader().get_term(term) {
            Term::TyOf(inner) => Some(inner),
            _ => None,
        }
    }

    /// If the term is a function type, return it.
    pub fn term_as_fn_ty(&self, term: TermId) -> Option<FnTy> {
        match self.reader().get_term(term) {
            Term::Level1(Level1Term::Fn(fn_ty)) => Some(fn_ty),
            _ => None,
        }
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

    /// Get a [Term] as a [UnitDef].
    pub fn term_as_unit_def(&self, term: TermId) -> Option<UnitDef> {
        match self.reader().get_term(term) {
            Term::Level1(Level1Term::NominalDef(def)) => match self.reader().get_nominal_def(def) {
                NominalDef::Unit(unit_def) => Some(unit_def),
                _ => None,
            },
            _ => None,
        }
    }

    /// Get a [Term] as a [TrtDef].
    pub fn term_as_trt_def(&self, term: TermId) -> Option<TrtDef> {
        match self.reader().get_term(term) {
            Term::Level2(Level2Term::Trt(item)) => Some(self.reader().get_trt_def(item)),
            _ => None,
        }
    }

    /// Get a [Term] as a [NominalDef].
    pub fn term_as_nominal_def(&self, term: TermId) -> Option<NominalDef> {
        self.term_as_nominal_def_id(term).map(|id| self.reader().get_nominal_def(id))
    }

    /// Get a [Term] as a [NominalDefId].
    pub fn term_as_nominal_def_id(&self, term: TermId) -> Option<NominalDefId> {
        match self.reader().get_term(term) {
            Term::Level1(Level1Term::NominalDef(def)) => Some(def),
            _ => None,
        }
    }

    /// Check if the given [Term] has the given name (in its definition).
    pub fn term_is_named(&self, term: TermId, name: Identifier) -> bool {
        match self.reader().get_term(term) {
            Term::Level1(Level1Term::NominalDef(def)) => {
                self.nominal_def_store().map_fast(def, |def| def.name().contains(&name))
            }
            Term::TyFn(ty_fn) => ty_fn.name.contains(&name),
            Term::Level1(Level1Term::ModDef(def)) => {
                self.mod_def_store().map_fast(def, |def| def.name.contains(&name))
            }
            _ => false,
        }
    }

    /// Given an [`EnumVariantValue`], get its corresponding [`EnumVariant`].
    pub fn get_enum_variant_info(&self, enum_variant: EnumVariantValue) -> EnumVariant {
        let dummy_term =
            || self.builder().create_term(Term::Level0(Level0Term::EnumVariant(enum_variant)));
        match self.reader().get_nominal_def(enum_variant.def_id) {
            NominalDef::Enum(enum_def) => {
                *enum_def.variants.get(&enum_variant.name).unwrap_or_else(|| {
                    tc_panic!(
                        dummy_term(),
                        self,
                        "Enum variant name {} not found in enum def",
                        enum_variant.name
                    )
                })
            }
            _ => tc_panic!(dummy_term(), self, "Found non-enum in enum variant value"),
        }
    }

    /// If the term is an eum variant value, get it.
    pub fn term_as_enum_variant_value(&self, term: TermId) -> Option<EnumVariantValue> {
        match self.reader().get_term(term) {
            Term::Level0(Level0Term::EnumVariant(enum_variant)) => Some(enum_variant),
            _ => None,
        }
    }

    /// If the term is an eum variant term, get its data.
    pub fn get_enum_variant_term_data(&self, term: TermId) -> bool {
        self.term_as_enum_def(term).is_some()
    }
}
