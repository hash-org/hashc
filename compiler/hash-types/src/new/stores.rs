use super::{
    args::{ArgsStore, PatArgsStore},
    data::{CtorDefsStore, DataDefStore},
    defs::{DefArgsStore, DefParamsStore, DefPatArgsStore},
    fns::FnDefStore,
    holes::HoleStore,
    mods::{ModDefStore, ModMembersStore},
    params::ParamsStore,
    pats::{PatListStore, PatStore},
    scopes::StackStore,
    symbols::SymbolStore,
    terms::{TermListStore, TermStore},
    trts::{TrtBoundsStore, TrtDefStore, TrtMembersStore},
    tys::TyStore,
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
    pat_args: PatArgsStore,
    ctor_defs: CtorDefsStore,
    data_def: DataDefStore,
    def_params: DefParamsStore,
    def_args: DefArgsStore,
    def_pat_args: DefPatArgsStore,
    fn_def: FnDefStore,
    hole: HoleStore,
    mod_members: ModMembersStore,
    mod_def: ModDefStore,
    params: ParamsStore,
    pat: PatStore,
    pat_list: PatListStore,
    stack: StackStore,
    symbol: SymbolStore,
    term: TermStore,
    term_list: TermListStore,
    trt_def: TrtDefStore,
    trt_members: TrtMembersStore,
    trt_bounds: TrtBoundsStore,
    ty: TyStore,
}
