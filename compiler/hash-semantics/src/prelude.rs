use hash_source::entry_point::EntryPointState;
use hash_tir::{
    intrinsics::make::make_root_mod,
    nodes::{mods::ModDefId, terms::fns::FnDefId},
};
use once_cell::sync::OnceCell;

/// Stores some "distinguished" items, namely the prelude and the root modules,
/// as well as the entry point function.
///
/// The prelude is the module that is implicitly imported into every module.
///
/// The root is the module that is the entry point of the program.
///
/// The entry point is the function that is the entry point of the program
/// inside the root module.
///
/// As this is available in `SemanticStorage`, it is available to all later
/// compiler stages.
#[derive(Default)]
pub struct DistinguishedItems {
    root_mod: OnceCell<ModDefId>,
    pub prelude_mod: OnceCell<ModDefId>,
    pub entry_point: EntryPointState<FnDefId>,
}

impl DistinguishedItems {
    pub fn root_mod(&self) -> ModDefId {
        *self.root_mod.get_or_init(make_root_mod)
    }
}
