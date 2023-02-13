// @@Docs
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
    atom_info::AtomInfoStore, control::MatchCasesStore, directives::AppliedDirectivesStore,
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

// @@Performance: Most stores store copy types, why do we use ref-cells when we
// can use cells?

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
    directives: AppliedDirectivesStore,
}

/// A reference to [`Stores`] alongside a value.
///
/// Used to implement traits for values where the trait implementation requires
/// access to the [`Stores`] (for example formatting).
pub struct WithStores<'s, T> {
    stores: &'s Stores,
    pub value: T,
}

impl<'s, T: Clone> Clone for WithStores<'s, T> {
    fn clone(&self) -> Self {
        Self { stores: self.stores, value: self.value.clone() }
    }
}
impl<'s, T: Copy> Copy for WithStores<'s, T> {}

impl<'s, T> WithStores<'s, T> {
    pub fn new(stores: &'s Stores, value: T) -> Self {
        Self { stores, value }
    }

    pub fn stores(&self) -> &Stores {
        self.stores
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> WithStores<'s, U> {
        WithStores { stores: self.stores, value: f(self.value) }
    }
}

impl Stores {
    /// Attach a value to a [`Stores`] reference, creating a [`WithStores`]
    /// value.
    pub fn with<T>(&self, value: T) -> WithStores<T> {
        WithStores::new(self, value)
    }
}
