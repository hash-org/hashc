#![allow(dead_code)]

use crate::{
    scope::ScopeStack,
    traits::{CoreTraits, TraitBound, TraitBounds},
};
use hash_alloc::{collections::row::Row, row, Wall};
use hash_ast::ident::{Identifier, IDENTIFIER_MAP};
use hash_source::location::SourceLocation;
use hash_utils::counter;
use slotmap::{new_key_type, SlotMap};
use std::hash::Hash;
use std::{cell::Cell, collections::HashMap, ptr};

#[derive(Debug)]
pub struct Generics<'c> {
    pub params: TypeList<'c>,
    pub bounds: TraitBounds<'c>,
}

impl Generics<'_> {
    pub fn empty() -> Self {
        Self {
            params: TypeList::default(),
            bounds: TraitBounds::empty(),
        }
    }
}

#[derive(Debug)]
pub struct EnumVariantParams<'c> {
    data: Row<'c, TypeId>,
}

#[derive(Debug)]
pub struct EnumVariant<'c> {
    pub name: Identifier,
    pub data: EnumVariantParams<'c>,
}

#[derive(Debug, Default)]
pub struct EnumVariants<'c> {
    data: HashMap<Identifier, EnumVariant<'c>>,
}

impl EnumVariants<'_> {
    pub fn empty() -> Self {
        Self::default()
    }
}

#[derive(Debug)]
pub struct EnumDef<'c> {
    pub name: Identifier,
    pub generics: Generics<'c>,
    pub variants: EnumVariants<'c>,
}

#[derive(Debug)]
pub struct StructFields {
    data: HashMap<Identifier, TypeId>,
}

impl StructFields {
    pub fn no_fields() -> Self {
        Self {
            data: HashMap::default(),
        }
    }

    pub fn get_field(&self, field: Identifier) -> Option<TypeId> {
        self.data.get(&field).copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = (Identifier, TypeId)> + '_ {
        self.data.iter().map(|(&a, &b)| (a, b))
    }
}

impl FromIterator<(Identifier, TypeId)> for StructFields {
    fn from_iter<T: IntoIterator<Item = (Identifier, TypeId)>>(iter: T) -> Self {
        Self {
            data: iter.into_iter().collect(),
        }
    }
}

#[derive(Debug)]
pub struct StructDef<'c> {
    pub name: Identifier,
    pub generics: Generics<'c>,
    pub fields: StructFields,
}

#[derive(Debug)]
pub enum TypeDefValueKind<'c> {
    Enum(EnumDef<'c>),
    Struct(StructDef<'c>),
}

#[derive(Debug)]
pub struct TypeDefValue<'c> {
    pub kind: TypeDefValueKind<'c>,
    pub location: Option<SourceLocation>,
}

counter! {
    name: TypeDefId,
    counter_name: TYPE_DEF_COUNTER,
    visibility: pub,
    method_visibility: pub(crate),
}

counter! {
    name: GenTypeVarId,
    counter_name: GEN_TYPE_VAR_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub enum PrimType {
    USize,
    Bool,
    U8,
    U16,
    U32,
    U64,
    ISize,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Char,
    Void,
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub struct TypeVar {
    pub name: Identifier,
}

#[derive(Debug)]
pub struct RefType {
    pub inner: TypeId,
}

#[derive(Debug)]
pub struct RawRefType {
    pub inner: TypeId,
}

pub type TypeList<'c> = Row<'c, TypeId>;

#[derive(Debug)]
pub struct UserType<'c> {
    pub def_id: TypeDefId,
    pub args: TypeList<'c>,
}

#[derive(Debug)]
pub struct FnType<'c> {
    pub args: TypeList<'c>,
    pub ret: TypeId,
}

#[derive(Debug)]
pub struct NamespaceType {
    pub members: ScopeStack,
}

#[derive(Debug)]
pub struct UnknownType<'c> {
    pub bounds: TraitBounds<'c>,
}

impl UnknownType<'_> {
    pub fn unbounded() -> Self {
        Self {
            bounds: TraitBounds::empty(),
        }
    }
}

#[derive(Debug)]
pub struct TupleType<'c> {
    pub types: Row<'c, TypeId>,
}

#[derive(Debug)]
pub enum TypeValue<'c> {
    Ref(RefType),
    RawRef(RawRefType),
    Fn(FnType<'c>),
    Var(TypeVar),
    User(UserType<'c>),
    Prim(PrimType),
    Tuple(TupleType<'c>),
    Unknown(UnknownType<'c>),
    Namespace(NamespaceType),
}

impl<'c> TypeValue<'c> {
    #[must_use]
    pub fn map_type_ids<F>(&self, mut f: F, wall: &Wall<'c>) -> Self
    where
        F: FnMut(TypeId) -> TypeId,
    {
        match self {
            TypeValue::Ref(RefType { inner }) => TypeValue::Ref(RefType { inner: f(*inner) }),
            TypeValue::RawRef(RawRefType { inner }) => {
                TypeValue::RawRef(RawRefType { inner: f(*inner) })
            }
            TypeValue::Fn(FnType { args, ret }) => TypeValue::Fn(FnType {
                args: Row::from_iter(args.iter().map(|&arg| f(arg)), wall),
                ret: f(*ret),
            }),
            TypeValue::User(UserType { args, def_id }) => TypeValue::User(UserType {
                args: Row::from_iter(args.iter().map(|&arg| f(arg)), wall),
                def_id: *def_id,
            }),
            TypeValue::Tuple(TupleType { types: args }) => TypeValue::Tuple(TupleType {
                types: Row::from_iter(args.iter().map(|&arg| f(arg)), wall),
            }),
            TypeValue::Var(var) => TypeValue::Var(*var),
            TypeValue::Prim(prim) => TypeValue::Prim(*prim),
            TypeValue::Unknown(UnknownType {
                bounds: TraitBounds { bounds },
            }) => TypeValue::Unknown(UnknownType {
                bounds: TraitBounds {
                    bounds: Row::from_iter(
                        bounds.iter().map(|TraitBound { trt, params }| TraitBound {
                            trt: *trt,
                            params: Row::from_iter(params.iter().map(|&arg| f(arg)), wall),
                        }),
                        wall,
                    ),
                },
            }),
            TypeValue::Namespace(ns) => TypeValue::Namespace(NamespaceType {
                members: ns.members.clone(),
            }),
        }
    }
}

impl<'c> Hash for &'c TypeValue<'c> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        ptr::hash(*self, state)
    }
}

impl<'c> PartialEq for &'c TypeValue<'c> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(*self, *other)
    }
}

impl<'c> Eq for &'c TypeValue<'c> {}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TypeVarStrategy {
    Match,
    Instantiate,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct UnifyOptions {
    type_var_strategy: TypeVarStrategy,
}

#[derive(Debug)]
pub struct CoreTypeDefs {
    pub str: TypeDefId,
    pub list: TypeDefId,
    pub map: TypeDefId,
    pub set: TypeDefId,
}

impl<'c, 'w> CoreTypeDefs {
    pub fn create(
        type_defs: &mut TypeDefs<'c, 'w>,
        types: &mut Types<'c, 'w>,
        core_traits: &CoreTraits,
        wall: &'w Wall<'c>,
    ) -> Self {
        let str = type_defs.create(
            TypeDefValueKind::Struct(StructDef {
                name: IDENTIFIER_MAP.create_ident("str"),
                generics: Generics::empty(),
                fields: StructFields::no_fields(),
            }),
            None,
        );

        let map_key = types.create_type_var("K");
        let map_value = types.create_type_var("V");
        let map = type_defs.create(
            TypeDefValueKind::Struct(StructDef {
                name: IDENTIFIER_MAP.create_ident("Map"),
                generics: Generics {
                    params: row![wall; map_key, map_value],
                    bounds: TraitBounds {
                        bounds: Row::from_iter(
                            [
                                TraitBound {
                                    trt: core_traits.hash,
                                    params: Row::from_iter([map_key], wall),
                                },
                                TraitBound {
                                    trt: core_traits.eq,
                                    params: Row::from_iter([map_key], wall),
                                },
                            ],
                            wall,
                        ),
                    },
                },
                fields: StructFields::no_fields(),
            }),
            None,
        );

        let list_el = types.create_type_var("T");
        let list = type_defs.create(
            TypeDefValueKind::Struct(StructDef {
                name: IDENTIFIER_MAP.create_ident("List"),
                generics: Generics {
                    params: row![wall; list_el],
                    bounds: TraitBounds::empty(),
                },
                fields: StructFields::no_fields(),
            }),
            None,
        );

        let set_el = types.create_type_var("T");
        let set = type_defs.create(
            TypeDefValueKind::Struct(StructDef {
                name: IDENTIFIER_MAP.create_ident("Set"),
                generics: Generics {
                    params: row![wall; set_el],
                    bounds: TraitBounds::empty(),
                },
                fields: StructFields::no_fields(),
            }),
            None,
        );

        Self {
            str,
            map,
            list,
            set,
        }
    }
}

#[derive(Debug)]
pub struct TypeDefs<'c, 'w> {
    data: HashMap<TypeDefId, Cell<&'c TypeDefValue<'c>>>,
    wall: &'w Wall<'c>,
}

impl<'c, 'w> TypeDefs<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        Self {
            data: HashMap::new(),
            wall,
        }
    }

    pub fn get(&self, ty_def: TypeDefId) -> &'c TypeDefValue<'c> {
        self.data.get(&ty_def).unwrap().get()
    }

    pub fn create(
        &mut self,
        def: TypeDefValueKind<'c>,
        location: Option<SourceLocation>,
    ) -> TypeDefId {
        let id = TypeDefId::new();
        self.data.insert(
            id,
            Cell::new(self.wall.alloc_value(TypeDefValue {
                kind: def,
                location,
            })),
        );
        id
    }
}

new_key_type! { pub struct TypeId; }

#[derive(Debug, Default)]
pub struct TypeLocation {
    data: HashMap<TypeId, SourceLocation>,
}

impl TypeLocation {
    pub fn get_location(&self, id: TypeId) -> Option<&SourceLocation> {
        self.data.get(&id)
    }

    pub fn add_location(&mut self, id: TypeId, location: SourceLocation) {
        self.data.insert(id, location);
    }
}

#[derive(Debug)]
pub struct Types<'c, 'w> {
    data: SlotMap<TypeId, Cell<&'c TypeValue<'c>>>,
    location_map: TypeLocation,
    wall: &'w Wall<'c>,
}

impl<'c, 'w> Types<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        let location_map = TypeLocation::default();

        Self {
            data: SlotMap::with_key(),
            location_map,
            wall,
        }
    }

    pub fn get(&self, ty: TypeId) -> &'c TypeValue<'c> {
        // @@Todo: resolve type variables bro!
        self.data.get(ty).unwrap().get()
    }

    pub fn get_location(&self, ty: TypeId) -> Option<&SourceLocation> {
        self.location_map.get_location(ty)
    }

    pub fn set(&self, target: TypeId, source: TypeId) {
        if target == source {
            return;
        }
        let other_val = self.data.get(source).unwrap().get();
        self.data.get(target).unwrap().set(other_val);
    }

    pub fn duplicate(&mut self, ty: TypeId) -> TypeId {
        match self.get(ty) {
            TypeValue::Ref(RefType { inner }) => {
                let inner = self.duplicate(*inner);
                self.create(TypeValue::Ref(RefType { inner }), None)
            }
            TypeValue::RawRef(RawRefType { inner }) => {
                let inner = self.duplicate(*inner);
                self.create(TypeValue::RawRef(RawRefType { inner }), None)
            }
            TypeValue::Fn(_) => todo!(),
            TypeValue::Var(_) => todo!(),
            TypeValue::User(_) => todo!(),
            TypeValue::Prim(_) => todo!(),
            TypeValue::Tuple(_) => todo!(),
            TypeValue::Unknown(_) => todo!(),
            TypeValue::Namespace(_) => todo!(),
        }
    }

    pub fn add_location(&mut self, ty: TypeId, location: SourceLocation) {
        self.location_map.add_location(ty, location);
    }

    pub fn create_type_var(&mut self, name: &str) -> TypeId {
        self.create(
            TypeValue::Var(TypeVar {
                name: IDENTIFIER_MAP.create_ident(name),
            }),
            None,
        )
    }

    pub fn create_unknown_type(&mut self) -> TypeId {
        self.create(TypeValue::Unknown(UnknownType::unbounded()), None)
    }

    pub fn create(&mut self, value: TypeValue<'c>, location: Option<SourceLocation>) -> TypeId {
        let id = self.data.insert(Cell::new(self.wall.alloc_value(value)));

        if let Some(location) = location {
            self.location_map.add_location(id, location);
        }

        id
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct TypeVarScopeKey(usize);

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TypeVarMode {
    Bound,
    Substitution(TypeId),
}

#[derive(Debug, Default)]
pub struct TypeVars {
    data: Vec<HashMap<TypeVar, TypeVarMode>>,
}

impl TypeVars {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn enter_bounded_type_var_scope(
        &mut self,
        type_vars: impl Iterator<Item = TypeVar>,
    ) -> TypeVarScopeKey {
        let key = TypeVarScopeKey(self.data.len());
        self.data
            .push(type_vars.map(|t| (t, TypeVarMode::Bound)).collect());
        key
    }

    pub fn potentially_resolve(&mut self, type_var: TypeVar) -> Option<TypeId> {
        self.find_type_var(type_var)
            .and_then(|(_, mode)| match mode {
                TypeVarMode::Bound => None,
                TypeVarMode::Substitution(ty_id) => Some(ty_id),
            })
    }

    pub fn find_type_var(&mut self, type_var: TypeVar) -> Option<(TypeVarScopeKey, TypeVarMode)> {
        for (i, scope) in self.data.iter().enumerate() {
            if let Some(&mode) = scope.get(&type_var) {
                return Some((TypeVarScopeKey(i), mode));
            }
        }
        None
    }

    pub fn exit_type_var_scope(&mut self, key: TypeVarScopeKey) {
        self.data.remove(key.0);
    }
}
