#![allow(dead_code)]

use crate::{scope::Scope, traits::TraitBounds};
use hash_alloc::{brick::Brick, collections::row::Row, Wall};
use hash_ast::{ast::TypeId, ident::Identifier, location::Location};
use hash_utils::counter;
use std::{cell::Cell, collections::HashMap};

#[derive(Debug)]
pub struct Generics<'c> {
    pub params: TypeList<'c>,
    pub bounds: TraitBounds<'c>,
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
pub enum TypeValue<'c> {
    Ref(RefType),
    RawRef(RawRefType),
    Fn(FnType<'c>),
    Var(TypeVar),
    User(UserType<'c>),
    Prim(PrimType),
    Unknown(UnknownType<'c>),
    Namespace(NamespaceType),
}
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TypeVarStrategy {
    Match,
    Instantiate,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct UnifyOptions {
    type_var_strategy: TypeVarStrategy,
}

#[derive(Debug, Default)]
pub struct TypeDefs<'c> {
    data: HashMap<TypeDefId, TypeDefValue<'c>>,
}

impl<'c> TypeDefs<'c> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self, ty_def: TypeDefId) -> &TypeDefValue<'c> {
        self.data.get(&ty_def).unwrap()
    }

    pub fn create(&mut self, def: TypeDefValue<'c>) -> TypeDefId {
        let id = TypeDefId::new();
        self.data.insert(id, def);
        id
    }
}

#[derive(Debug)]
pub struct Types<'c, 'w> {
    data: HashMap<TypeId, Cell<&'c TypeValue<'c>>>,
    wall: &'w Wall<'c>,
}

impl<'c, 'w> Types<'c, 'w> {
    pub fn new(wall: &'w Wall<'c>) -> Self {
        Self {
            data: HashMap::new(),
            wall,
        }
    }

    pub fn get(&self, ty: TypeId) -> &'c TypeValue<'c> {
        // @@Todo: resolve type variables bro!
        self.data.get(&ty).unwrap().get()
    }

    pub fn set(&self, target: TypeId, source: TypeId) {
        if target == source {
            return;
        }
        let other_val = self.data.get(&source).unwrap().get();
        self.data.get(&target).unwrap().set(other_val);
    }

    pub fn create(&mut self, value: TypeValue<'c>) -> TypeId {
        let id = TypeId::new();
        self.data
            .insert(id, Cell::new(Brick::new(value, &self.wall).disown()));
        id
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

// pub fn resolve_compound_symbol(
//     &self,
//     symbols: &[Identifier],
//     types: &Types,
// ) -> Option<SymbolType> {
//     let mut last_scope = self.current_scope();
//     let mut symbols_iter = symbols.iter().peekable();

//     loop {
//         match last_scope.resolve_symbol(*symbols_iter.next().unwrap()) {
//             Some(symbol_ty @ SymbolType::Variable(type_id)) => match types.get(type_id) {
//                 TypeValue::Namespace(namespace_ty) => match symbols_iter.peek() {
//                     Some(_) => {
//                         last_scope = &namespace_ty.members;
//                         continue;
//                     }
//                     None => {
//                         return Some(symbol_ty);
//                     }
//                 },
//                 _ => {}
//             },
//             Some(symbol_ty) => match symbols_iter.peek() {
//                 Some(_) => {
//                     panic!("Found trying to namespace type.");
//                 }
//                 None => {
//                     return Some(symbol_ty);
//                 }
//             },
//             None => continue,
//         }
//     }
// }

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

#[derive(Debug)]
pub enum TypecheckError {
    TypeMismatch(TypeId, TypeId),
    UsingBreakOutsideLoop(Location),
    UsingContinueOutsideLoop(Location),
    UsingReturnOutsideFunction(Location),
    RequiresIrrefutablePattern(Location),
    UnresolvedSymbol(Vec<Identifier>),
    UsingVariableInTypePos(Vec<Identifier>),
    // @@Todo: turn this into variants
    Message(String),
}

pub type TypecheckResult<T> = Result<T, TypecheckError>;

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
