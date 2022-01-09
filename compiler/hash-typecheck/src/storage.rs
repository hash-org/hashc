use hash_alloc::Wall;
use hash_ast::module::Modules;

use crate::{
    scope::ScopeStack,
    state::TypecheckState,
    traits::{CoreTraits, TraitImplStorage, TraitStorage},
    types::{CoreTypeDefs, TypeDefStorage, TypeVars, TypeStorage},
};

#[derive(Debug)]
pub struct GlobalStorage<'c, 'w, 'm> {
    pub modules: &'m Modules<'c>,
    pub core_traits: CoreTraits,
    pub core_type_defs: CoreTypeDefs,
    pub type_defs: TypeDefStorage<'c, 'w>,
    pub trait_impls: TraitImplStorage<'c, 'w>,
    pub traits: TraitStorage<'c, 'w>,
    pub types: TypeStorage<'c, 'w>,
    pub wall: &'w Wall<'c>,
}

impl<'c, 'w, 'm> GlobalStorage<'c, 'w, 'm> {
    pub fn new_with_modules(modules: &'m Modules<'c>, wall: &'w Wall<'c>) -> Self {
        let mut type_defs = TypeDefStorage::new(wall);
        let trait_impls = TraitImplStorage::new(wall);
        let traits = TraitStorage::new(wall);
        let mut types = TypeStorage::new(wall);
        let core_traits = CoreTraits::create(&mut types, wall);
        let core_type_defs = CoreTypeDefs::create(&mut type_defs, &mut types, &core_traits, wall);

        Self {
            modules,
            type_defs,
            trait_impls,
            traits,
            types,
            core_type_defs,
            core_traits,
            wall,
        }
    }

    pub fn wall(&self) -> &'w Wall<'c> {
        self.wall
    }
}

#[derive(Debug)]
pub struct ModuleStorage {
    pub type_vars: TypeVars,
    pub scopes: ScopeStack,
    pub state: TypecheckState,
}

impl ModuleStorage {
    pub fn new(global_storage: &mut GlobalStorage) -> Self {
        Self {
            type_vars: TypeVars::new(),
            scopes: ScopeStack::new(global_storage),
            state: TypecheckState::default(),
        }
    }
}
