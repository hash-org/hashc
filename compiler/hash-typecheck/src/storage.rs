use std::collections::HashMap;

use hash_alloc::Wall;
use hash_source::SourceId;

use crate::{
    scope::ScopeStack,
    state::TypecheckState,
    traits::{CoreTraits, TraitImplStorage, TraitStorage},
    types::{CoreTypeDefs, TypeDefStorage, TypeId, TypeStorage, TypeVars},
};

#[derive(Debug, Default)]
pub struct CheckedSources {
    data: HashMap<SourceId, TypeId>,
}

impl CheckedSources {
    pub fn new() -> Self {
        Self {
            data: HashMap::new(),
        }
    }

    pub fn mark_checked(&mut self, source_id: SourceId, type_id: TypeId) {
        self.data.insert(source_id, type_id);
    }

    pub fn source_type_id(&mut self, source_id: SourceId) -> Option<TypeId> {
        self.data.get(&source_id).copied()
    }
}

// @@TODO: Everything here needs to hold type locations!
#[derive(Debug)]
pub struct GlobalStorage<'c, 'w> {
    pub checked_sources: CheckedSources,
    pub core_traits: CoreTraits,
    pub core_type_defs: CoreTypeDefs,
    pub type_defs: TypeDefStorage<'c, 'w>,
    pub trait_impls: TraitImplStorage<'c, 'w>,
    pub traits: TraitStorage<'c, 'w>,
    pub types: TypeStorage<'c, 'w>,
    pub wall: &'w Wall<'c>,
}

impl<'c, 'w> GlobalStorage<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        let checked_sources = CheckedSources::new();
        let mut type_defs = TypeDefStorage::new(wall);
        let trait_impls = TraitImplStorage::new(wall);
        let traits = TraitStorage::new(wall);
        let mut types = TypeStorage::new(wall);
        let core_traits = CoreTraits::create(&mut types, wall);
        let core_type_defs = CoreTypeDefs::create(&mut type_defs, &mut types, &core_traits, wall);

        Self {
            checked_sources,
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
pub struct SourceStorage {
    pub type_vars: TypeVars,
    pub scopes: ScopeStack,
    pub state: TypecheckState,
}

impl SourceStorage {
    pub fn new(current_module: SourceId, scopes: ScopeStack) -> Self {
        Self {
            type_vars: TypeVars::new(),
            scopes,
            state: TypecheckState::new(current_module),
        }
    }
}
