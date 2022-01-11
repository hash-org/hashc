use hash_alloc::Wall;
use hash_ast::module::Modules;

use crate::{
    scope::ScopeStack,
    state::TypecheckState,
    traits::{CoreTraits, TraitImpls, Traits},
    types::{CoreTypeDefs, TypeDefs, TypeLocation, TypeVars, Types},
};

// @@TODO: Everything here needs to hold type locations!
#[derive(Debug)]
pub struct GlobalStorage<'c, 'w, 'm> {
    pub modules: &'m Modules<'c>,
    pub type_defs: TypeDefs<'c, 'w>,
    pub core_traits: CoreTraits,
    pub core_type_defs: CoreTypeDefs,
    pub trait_impls: TraitImpls<'c, 'w>,
    pub traits: Traits<'c, 'w>,
    pub types: Types<'c, 'w>,
    pub wall: &'w Wall<'c>,
}

impl<'c, 'w, 'm> GlobalStorage<'c, 'w, 'm> {
    pub fn new_with_modules(modules: &'m Modules<'c>, wall: &'w Wall<'c>) -> Self {
        let mut type_defs = TypeDefs::new(wall);
        let trait_impls = TraitImpls::new(wall);
        let traits = Traits::new(wall);
        let mut types = Types::new(wall);
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
