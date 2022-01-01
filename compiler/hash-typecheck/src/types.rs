#![allow(dead_code)]

use crate::{
    scope::Scope,
    traits::{CoreTraits, TraitBound, TraitBounds},
};
use hash_alloc::{brick::Brick, collections::row::Row, row, Wall};
use hash_ast::ident::{Identifier, IDENTIFIER_MAP};
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
        self.data.get(&field).map(|&t| t)
    }
}

#[derive(Debug)]
pub struct StructDef<'c> {
    pub name: Identifier,
    pub generics: Generics<'c>,
    pub fields: StructFields,
}

#[derive(Debug)]
pub enum TypeDefValue<'c> {
    Enum(EnumDef<'c>),
    Struct(StructDef<'c>),
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
    pub members: Scope,
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
        let str = type_defs.create(TypeDefValue::Struct(StructDef {
            name: IDENTIFIER_MAP.create_ident("str"),
            generics: Generics::empty(),
            fields: StructFields::no_fields(),
        }));

        let map_key = types.create_type_var("K");
        let map_value = types.create_type_var("V");
        let map = type_defs.create(TypeDefValue::Struct(StructDef {
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
        }));

        let list_el = types.create_type_var("T");
        let list = type_defs.create(TypeDefValue::Struct(StructDef {
            name: IDENTIFIER_MAP.create_ident("List"),
            generics: Generics {
                params: row![wall; list_el],
                bounds: TraitBounds::empty(),
            },
            fields: StructFields::no_fields(),
        }));

        let set_el = types.create_type_var("T");
        let set = type_defs.create(TypeDefValue::Struct(StructDef {
            name: IDENTIFIER_MAP.create_ident("Set"),
            generics: Generics {
                params: row![wall; set_el],
                bounds: TraitBounds::empty(),
            },
            fields: StructFields::no_fields(),
        }));

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
        &self.data.get(&ty_def).unwrap().get()
    }

    pub fn create(&mut self, def: TypeDefValue<'c>) -> TypeDefId {
        let id = TypeDefId::new();
        self.data
            .insert(id, Cell::new(Brick::new(def, self.wall).disown()));
        id
    }
}

new_key_type! { pub struct TypeId; }

#[derive(Debug)]
pub struct Types<'c, 'w> {
    data: SlotMap<TypeId, Cell<&'c TypeValue<'c>>>,
    wall: &'w Wall<'c>,
}

impl<'c, 'w> Types<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        Self {
            data: SlotMap::with_key(),
            wall,
        }
    }

    pub fn get(&self, ty: TypeId) -> &'c TypeValue<'c> {
        // @@Todo: resolve type variables bro!
        self.data.get(ty).unwrap().get()
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
                self.create(TypeValue::Ref(RefType { inner }))
            }
            TypeValue::RawRef(RawRefType { inner }) => {
                let inner = self.duplicate(*inner);
                self.create(TypeValue::RawRef(RawRefType { inner }))
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

    pub fn create_type_var(&mut self, name: &str) -> TypeId {
        self.create(TypeValue::Var(TypeVar {
            name: IDENTIFIER_MAP.create_ident(name),
        }))
    }

    pub fn create_unknown_type(&mut self) -> TypeId {
        self.create(TypeValue::Unknown(UnknownType::unbounded()))
    }

    pub fn create(&mut self, value: TypeValue<'c>) -> TypeId {
        self.data
            .insert(Cell::new(Brick::new(value, &self.wall).disown()))
    }
}

#[derive(Debug, Default)]
pub struct TypeVars {
    data: HashMap<TypeVar, TypeId>,
}

impl TypeVars {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn resolve(&self, var: TypeVar) -> Option<TypeId> {
        self.data.get(&var).map(|&x| x)
    }

    pub fn assign(&mut self, var: TypeVar, ty: TypeId) {
        self.data.insert(var, ty);
    }
}

// pub fn substitute_many<'c>(
//     &self,
//     ty: impl IntoIterator<Item = impl Deref<Target = TypeId>>,
//     types: &mut Types<'c>,
//     wall: &Wall<'c>,
// ) -> Row<'c, TypeId> {
//     Row::from_iter(
//         ty.into_iter().map(|ty| self.substitute(*ty, types, wall)),
//         wall,
//     )
// }

// pub fn substitute<'c>(&self, ty: TypeId, types: &mut Types<'c>, wall: &Wall<'c>) -> TypeId {
//     match types.get(ty) {
//         TypeValue::Ref(RefType { inner }) => {
//             let inner = self.substitute(*inner, types, wall);
//             types.create(TypeValue::Ref(RefType { inner }), wall)
//         }
//         TypeValue::RawRef(RawRefType { inner }) => {
//             let inner = self.substitute(*inner, types, wall);
//             types.create(TypeValue::RawRef(RawRefType { inner }), wall)
//         }
//         TypeValue::Fn(FnType { args, ret }) => {
//             let args = self.substitute_many(args, types, wall);
//             let ret = self.substitute(*ret, types, wall);
//             types.create(TypeValue::Fn(FnType { args, ret }), wall)
//         }
//         TypeValue::Var(type_var) => match self.resolve(*type_var) {
//             Some(resolved) => resolved,
//             None => ty,
//         },
//         TypeValue::User(UserType { def_id, args }) => {
//             let args = self.substitute_many(args, types, wall);
//             types.create(
//                 TypeValue::User(UserType {
//                     def_id: *def_id,
//                     args,
//                 }),
//                 wall,
//             )
//         }
//         TypeValue::Prim(_) => ty,
//         TypeValue::Unknown(UnknownType { bounds }) => {
//             let bounds = bounds.map(wall, |bound| TraitBound {
//                 trt: bound.trt,
//                 params: self.substitute_many(&bound.params, types, wall),
//             });
//             types.create(TypeValue::Unknown(UnknownType { bounds }), wall)
//         }
//         TypeValue::Namespace(_) => ty,
//     }
// }

#[cfg(test)]
mod tests {
    use hash_alloc::Castle;
    use hash_ast::module::ModuleBuilder;

    #[test]
    fn type_size() {
        let castle = Castle::new();
        let _wall = castle.wall();

        let _modules = ModuleBuilder::new().build();

        // let mut ctx = TypecheckCtx {
        //     types: Types::new(),
        //     type_defs: TypeDefs::new(),
        //     type_vars: TypeVars::new(),
        //     traits: Traits::new(),
        //     state: TypecheckState::default(),
        //     scopes: ScopeStack::new(),
        //     modules: &modules,
        // };

        // let t_arg = ctx.types.create(
        //     TypeValue::Var(TypeVar {
        //         name: IDENTIFIER_MAP.create_ident("T"),
        //     }),
        //     &wall,
        // );

        // let foo_def = ctx.type_defs.create(TypeDefValue::Enum(EnumDef {
        //     name: IDENTIFIER_MAP.create_ident("Option"),
        //     generics: Generics {
        //         bounds: TraitBounds::default(),
        //         params: row![&wall; t_arg],
        //     },
        //     variants: EnumVariants::empty(),
        // }));

        // let char = ctx.types.create(TypeValue::Prim(PrimType::Char), &wall);
        // let int = ctx.types.create(TypeValue::Prim(PrimType::I32), &wall);
        // let unknown = ctx
        //     .types
        //     .create(TypeValue::Unknown(UnknownType::unbounded()), &wall);
        // let foo = ctx.types.create(
        //     TypeValue::User(UserType {
        //         def_id: foo_def,
        //         args: row![&wall; int, unknown],
        //     }),
        //     &wall,
        // );

        // let fn1 = ctx.types.create(
        //     TypeValue::Fn(FnType {
        //         args: row![&wall; foo, unknown, char, int, foo],
        //         ret: int,
        //     }),
        //     &wall,
        // );

        // println!("{}", TypeWithCtx::new(fn1, &ctx));
    }
}
