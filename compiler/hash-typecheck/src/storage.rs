use hash_alloc::Wall;
use hash_ast::module::Modules;

use crate::{
    scope::ScopeStack,
    state::TypecheckState,
    traits::{TraitImpls, Traits},
    types::{CoreTypeDefs, TypeDefs, TypeVars, Types},
};

#[derive(Debug)]
pub struct GlobalStorage<'c, 'w, 'm> {
    pub modules: &'m Modules<'c>,
    pub type_defs: TypeDefs<'c, 'w>,
    pub core_type_defs: CoreTypeDefs,
    pub trait_impls: TraitImpls<'c>,
    pub traits: Traits,
    pub types: Types<'c, 'w>,
}

impl<'c, 'w, 'm> GlobalStorage<'c, 'w, 'm> {
    pub fn new_with_modules(modules: &'m Modules<'c>, wall: &'w Wall<'c>) -> Self {
        let mut type_defs = TypeDefs::new(wall);
        let trait_impls = TraitImpls::default();
        let traits = Traits::default();
        let mut types = Types::new(wall);
        let core_type_defs = CoreTypeDefs::create(&mut type_defs, &mut types, wall);

        Self {
            modules,
            type_defs,
            trait_impls,
            traits,
            types,
            core_type_defs,
        }
    }
}

#[derive(Debug, Default)]
pub struct ModuleStorage {
    pub type_vars: TypeVars,
    pub scopes: ScopeStack,
    pub state: TypecheckState,
}

// #[derive(Debug, Default)]
// pub struct Storage<'c, 'w> {
//     pub type_defs: TypeDefs<'c>,
//     pub trait_impls: TraitImpls<'c>,
//     pub traits: Traits,
//     pub types: Types<'c, 'w>,
//     pub type_vars: TypeVars,
//     pub scopes: ScopeStack,
//     pub state: TypecheckState,
// }
