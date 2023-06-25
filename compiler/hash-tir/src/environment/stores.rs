// @@Docs
use std::sync::OnceLock;

use super::super::{
    args::{ArgsStore, PatArgsStore},
    data::{CtorDefsStore, DataDefStore},
    fns::FnDefStore,
    locations::LocationStore,
    mods::{ModDefStore, ModMembersStore},
    params::ParamsStore,
    pats::{PatListStore, PatStore},
    scopes::StackStore,
    symbols::SymbolStore,
    terms::{TermListStore, TermStore},
    tys::TyStore,
};
use crate::{
    ast_info::AstInfo, atom_info::AtomInfoStore, control::MatchCasesStore,
    directives::AppliedDirectivesStore,
};

/// This macro creates the `Stores` struct, as well as accompanying creation and
/// access methods, for the given sequence of stores.
macro_rules! stores {
  ($($name:ident: $ty:ty),* $(,)?) => {
    #[derive(Debug)]
    pub struct Stores {
        $($name: $ty),*
    }

    impl Stores {
        pub fn new() -> Self {
            Self {
                $($name: <$ty>::new()),*
            }
        }

        $(
            pub fn $name(&self) -> & $ty {
                &self.$name
            }
        )*
    }

    impl Default for Stores {
        fn default() -> Self {
            Self::new()
        }
    }
  }
}

// All the stores that contain definitions for the typechecker.
stores! {
    args: ArgsStore,
    ctor_defs: CtorDefsStore,
    data_def: DataDefStore,
    fn_def: FnDefStore,
    location: LocationStore,
    mod_def: ModDefStore,
    mod_members: ModMembersStore,
    params: ParamsStore,
    pat: PatStore,
    pat_args: PatArgsStore,
    pat_list: PatListStore,
    stack: StackStore,
    symbol: SymbolStore,
    term: TermStore,
    term_list: TermListStore,
    ty: TyStore,
    match_cases: MatchCasesStore,
    atom_info: AtomInfoStore,
    ast_info: AstInfo,
    directives: AppliedDirectivesStore,
}

/// The global `Stores` instance.
static STORES: OnceLock<Stores> = OnceLock::new();

/// Access the global `Stores` instance.
pub fn global_stores() -> &'static Stores {
    STORES.get_or_init(Stores::new)
}

/// A trait for a store ID which can be used to access a store in `STORES`.
pub trait StoreId: Sized + Copy {
    type Value;
    type ValueRef: ?Sized;

    /// Get the value associated with this ID.
    fn value(self) -> Self::Value;

    /// Map the value associated with this ID to a new value.
    fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R;

    /// Modify the value associated with this ID.
    fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R;

    /// Set the value associated with this ID.
    fn set(self, value: Self::Value);
}

/// A trait for a sequence store ID which can be used to access a store in
/// `STORES`.
pub trait SequenceStoreValue: Sized {
    type Id: StoreId;

    /// Create a new empty value in the store.
    fn empty_seq() -> Self::Id;

    /// Create a new value in the store from the given iterator of functions.
    fn seq<F: FnOnce((Self::Id, usize)) -> Self, I: IntoIterator<Item = F>>(iter: I) -> Self::Id
    where
        I::IntoIter: ExactSizeIterator;
}

/// A trait for a store ID containing single items which can be used to access a
/// store in `STORES`.
pub trait SingleStoreValue: Sized {
    type Id: StoreId;

    /// Create a new value in the store from the given function.
    fn create(self) -> Self::Id {
        Self::create_with(|_| self)
    }

    /// Create a new value in the store from the given function.
    fn create_with<F: FnOnce(Self::Id) -> Self>(value: F) -> Self::Id;
}

/// Automatically implement `StoreId` and `SequenceStoreId` for a sequence store
/// ID type.
#[macro_export]
macro_rules! impl_sequence_store_id {
    ($id:ty, $value:ty, $store_name:ident) => {
        impl $crate::environment::stores::StoreId for $id {
            type Value = Vec<$value>;
            type ValueRef = [$value];

            fn value(self) -> Self::Value {
                $crate::environment::stores::global_stores().$store_name().get_vec(self)
            }

            fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R {
                $crate::environment::stores::global_stores().$store_name().map_fast(self, f)
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
                $crate::environment::stores::global_stores().$store_name().modify_fast(self, f)
            }

            fn set(self, value: Self::Value) {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .set_from_slice_cloned(self, &value);
            }
        }

        impl $crate::environment::stores::SequenceStoreValue for $value {
            type Id = $id;

            fn empty_seq() -> Self::Id {
                $crate::environment::stores::global_stores().$store_name().create_from_slice(&[])
            }

            fn seq<F: FnOnce((Self::Id, usize)) -> Self, I: IntoIterator<Item = F>>(
                values: I,
            ) -> Self::Id
            where
                I::IntoIter: ExactSizeIterator,
            {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .create_from_iter_with(values)
            }
        }

        impl $crate::environment::stores::StoreId for ($id, usize) {
            type Value = $value;
            type ValueRef = $value;

            fn value(self) -> Self::Value {
                $crate::environment::stores::global_stores().$store_name().get_element(self)
            }

            fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .map_fast(self.0, |v| f(&v[self.1]))
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .modify_fast(self.0, |v| f(&mut v[self.1]))
            }

            fn set(self, value: Self::Value) {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .set_at_index(self.0, self.1, value);
            }
        }
    };
}

/// Automatically implement `StoreId` and `SingleStoreId` for a single store ID
/// type.
#[macro_export]
macro_rules! impl_single_store_id {
    ($id:ty, $value:ty, $store_name:ident) => {
        impl $crate::environment::stores::StoreId for $id {
            type Value = $value;
            type ValueRef = $value;

            fn value(self) -> Self::Value {
                $crate::environment::stores::global_stores().$store_name().get(self)
            }

            fn map<R>(self, f: impl FnOnce(&Self::Value) -> R) -> R {
                $crate::environment::stores::global_stores().$store_name().map_fast(self, f)
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::Value) -> R) -> R {
                $crate::environment::stores::global_stores().$store_name().modify_fast(self, f)
            }

            fn set(self, value: Self::Value) {
                $crate::environment::stores::global_stores().$store_name().set(self, value);
            }
        }

        impl $crate::environment::stores::SingleStoreValue for $value {
            type Id = $id;
            fn create_with<F: FnOnce(Self::Id) -> Self>(value: F) -> Self::Id {
                $crate::environment::stores::global_stores().$store_name().create_with(value)
            }
        }
    };
}
