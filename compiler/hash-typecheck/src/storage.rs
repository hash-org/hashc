//! All rights reserved 2022 (c) The Hash Language authors
use crate::{
    scope::ScopeStack,
    state::TypecheckState,
    traits::{CoreTraits, TraitImplStorage, TraitStorage},
    types::{CoreTypeDefs, TypeDefStorage, TypeId, TypeStorage, TypeVars},
};
use hash_alloc::Wall;
use hash_source::SourceId;
use std::collections::HashMap;

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

#[derive(Debug)]
pub struct GlobalStorage<'c, 'w> {
    pub checked_sources: CheckedSources,
    pub core_traits: CoreTraits,
    pub core_type_defs: CoreTypeDefs,
    pub type_defs: TypeDefStorage<'c, 'w>,
    pub trait_impls: TraitImplStorage,
    pub traits: TraitStorage<'c, 'w>,
    pub types: TypeStorage<'c, 'w>,
    pub wall: &'w Wall<'c>,
}

impl<'c, 'w> GlobalStorage<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        let checked_sources = CheckedSources::new();
        let mut type_defs = TypeDefStorage::new(wall);
        let trait_impls = TraitImplStorage::new();
        let traits = TraitStorage::new(wall);
        let mut types = TypeStorage::new(wall);
        let core_traits = CoreTraits::create(&mut types, wall);
        let core_type_defs = CoreTypeDefs::create(&mut type_defs, &mut types, &core_traits);

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

mod new {
    #![allow(unused)]

    use hash_ast::ident::Identifier;
    use std::collections::HashMap;

    pub struct TyId;
    pub struct TrtDefId;
    pub struct StructDefId;
    pub struct EnumDefId;
    pub struct ModDefId;
    pub struct ResolutionId;

    enum Visibility {
        Public,
        Private,
    }

    enum Mutability {
        Mutable,
        Immutable,
    }

    struct ScopeMember {
        name: Identifier,
        ty: TyId,
        visibility: Visibility,
        mutability: Mutability,
        initialised: bool,
    }

    struct ConstMember {
        name: Identifier,
        ty: TyId,
        visibility: Visibility,
        initialised: bool,
    }

    struct TyArg {
        name: Identifier,
        value: TyId,
    }

    struct TyParam {
        name: Identifier,
        bound: TyId,
        default: Option<TyId>,
    }

    pub struct Param {
        name: Option<Identifier>,
        ty: TyId,
        has_default: bool,
    }

    pub enum ModDefOrigin {
        TrtImpl(TrtDefId),
        AnonImpl,
        Mod,
    }

    pub struct ModDef {
        name: Identifier,
        origin: ModDefOrigin,
        resolved_ty_args: Vec<TyArg>,
        members: Vec<ConstMember>,
    }

    pub enum StructFields {
        Explicit(Vec<Param>),
        Opaque,
    }

    pub struct StructDef {
        name: Identifier,
        fields: StructFields,
    }

    pub struct EnumVariant {
        name: Identifier,
        fields: Vec<Param>,
    }

    pub struct EnumDef {
        name: Identifier,
        variants: HashMap<Identifier, EnumVariant>,
    }

    pub struct TrtDef {
        name: Identifier,
        members: Vec<ConstMember>,
    }

    pub enum NominalDef {
        Struct(StructDefId),
        Enum(EnumDefId),
    }

    pub struct ImplGroup {
        nominal_def: Option<NominalDef>,
        modules: Vec<ModDefId>,
    }

    pub struct TupleTy {
        members: Vec<Param>,
    }

    pub struct FnTy {
        params: Vec<Param>,
        return_ty: TyId,
    }

    pub struct TyFnTy {
        params: Vec<TyParam>,
        return_ty: TyId,
    }

    pub struct UnresolvedTy {
        resolution_id: ResolutionId,
    }

    pub enum Ty {
        /// Any type, only to be used from within [Extends].
        Any,
        /// The type of a type
        Ty,
        /// Type that extends some other type.
        Extends(Box<Ty>),
        /// Definitions (structs, enums, traits, impl blocks, mod blocks)
        ImplGroup(ImplGroup),
        /// Tuple type.
        Tuple(TupleTy),
        /// Function type.
        Fn(FnTy),
        /// Type function type.
        TyFn(TyFnTy),
        /// Not yet resolved.
        Unresolved(UnresolvedTy),
    }
}
