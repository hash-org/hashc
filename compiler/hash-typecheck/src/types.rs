#![allow(dead_code)]

use core::fmt;
use std::{
    borrow::{Borrow, BorrowMut},
    cell::Cell,
    collections::{BTreeMap, HashMap},
    ops::Deref,
};

use dashmap::DashMap;
use hash_alloc::{brick::Brick, collections::row::Row, row, Wall};
use hash_ast::{
    ast::TypeId,
    ident::Identifier,
    location::Location,
    module::{ModuleIdx, Modules},
};
use hash_utils::counter;

#[derive(Debug)]
pub struct Trait {}

counter! {
    name: TraitId,
    counter_name: TRAIT_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug, Default)]
pub struct TraitBounds<'c> {
    data: Row<'c, TraitBound<'c>>,
}

impl<'c> TraitBounds<'c> {
    pub fn empty() -> Self {
        Self { data: row![] }
    }

    pub fn map(&self, wall: &Wall<'c>, f: impl FnMut(&TraitBound<'c>) -> TraitBound<'c>) -> Self {
        TraitBounds {
            data: Row::from_iter(self.data.iter().map(f), wall),
        }
    }
}

#[derive(Debug)]
pub struct TraitBound<'c> {
    pub trt: TraitId,
    pub params: TypeList<'c>,
}

impl TraitBound<'_> {}

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
pub enum TypeDefValue<'c> {
    Enum(EnumDef<'c>),
    Struct(StructDef<'c>),
}

counter! {
    name: TypeDefId,
    counter_name: TYPE_DEF_COUNTER,
    visibility: pub,
    method_visibility:,
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

counter! {
    name: TraitImplId,
    counter_name: TRAIT_IMPL_COUNTER,
    visibility: pub,
    method_visibility:,
}

pub struct TraitImpl<'c> {
    pub args: TypeList<'c>,
    pub bounds: TraitBounds<'c>,
}

impl<'c> TraitImpl<'c> {
    pub fn instantiate(&self, given_args: &TypeList<'c>, ctx: &TypecheckCtx) -> Option<()> {
        if given_args.len() != self.args.len() {
            // @@TODO: error
            return None;
        }

        for (&trait_arg, &given_arg) in self.args.iter().zip(given_args.iter()) {}

        None
    }
}

pub struct ImplsForTrait<'c> {
    trt: TraitId,
    impls: BTreeMap<TraitImplId, TraitImpl<'c>>,
}

pub struct TraitImpls<'c> {
    data: HashMap<TraitId, ImplsForTrait<'c>>,
}

#[derive(Debug, Default)]
pub struct Types<'c> {
    data: HashMap<TypeId, Cell<&'c TypeValue<'c>>>,
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

impl<'c> Types<'c> {
    pub fn new() -> Self {
        Self {
            data: HashMap::new(),
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

    pub fn create(&mut self, value: TypeValue<'c>, wall: &Wall<'c>) -> TypeId {
        let id = TypeId::new();
        self.data
            .borrow_mut()
            .insert(id, Cell::new(Brick::new(value, wall).disown()));
        id
    }

    pub fn unify(
        &mut self,
        target: TypeId,
        source: TypeId,
        type_vars: &mut TypeVars,
    ) -> TypecheckResult<()> {
        // Already the same type
        if target == source {
            return Ok(());
        }

        // @@TODO: Figure out covariance, contravariance, and invariance rules.
        // Right now, there are no sub/super types, so these variance rules aren't applicable. In
        // other words, unify is symmetric over target/source. However it is not foreseeable that
        // this will continue to be the case in the future.

        let target_ty = self.get(target);
        let source_ty = self.get(source);

        use TypeValue::*;
        match (target_ty, source_ty) {
            (Ref(ref_target), Ref(ref_source)) => {
                self.unify(ref_target.inner, ref_source.inner, type_vars)?;

                Ok(())
            }
            (RawRef(raw_target), RawRef(raw_source)) => {
                self.unify(raw_target.inner, raw_source.inner, type_vars)?;

                Ok(())
            }
            (Fn(fn_target), Fn(fn_source)) => {
                self.unify_pairs(fn_target.args.iter().zip(fn_source.args.iter()), type_vars)?;
                // Maybe this should be flipped (see variance comment above)
                self.unify(fn_target.ret, fn_source.ret, type_vars)?;

                // let merged_sub = args_sub.merge(self, &ret_sub);

                // let unified_ty = Fn(FnType {
                //     args: unified_args,
                //     ret: Box::new(unified_ret),
                // });

                Ok(())
            }
            (Unknown(_), Unknown(_)) => {
                // @@TODO: Ensure that trait bounds are compatible

                Ok(())
            }
            (Unknown(_), _) => {
                // @@TODO: Ensure that trait bounds are compatible
                self.set(target, source);

                Ok(())
            }
            (_, Unknown(_)) => {
                // @@TODO: Ensure that trait bounds are compatible
                self.set(source, target);

                Ok(())
            }
            (Var(var_target), Var(var_source)) if var_target == var_source => Ok(()),
            (_, Var(var_source)) => match type_vars.resolve(*var_source) {
                Some(resolved) => self.unify(target, resolved, type_vars),
                None => Err(TypecheckError::TypeMismatch(target, source)),
            },
            (Var(var_target), _) => match type_vars.resolve(*var_target) {
                Some(resolved) => self.unify(resolved, source, type_vars),
                None => Err(TypecheckError::TypeMismatch(target, source)),
            },
            (User(user_target), User(user_source)) if user_target.def_id == user_source.def_id => {
                // Make sure we got same number of type arguments
                assert_eq!(user_target.args.len(), user_source.args.len());

                // Unify type arguments.
                self.unify_pairs(
                    (user_target.args.iter()).zip(user_source.args.iter()),
                    type_vars,
                )?;

                // let unified_ty_id = self.create(User(UserType {
                //     def_id: user_target.def_id,
                //     args: unified_args,
                // }));

                Ok(())
            }
            (Prim(prim_target), Prim(prim_source)) if prim_target == prim_source => Ok(()),
            // (Namespace(ns_target), Namespace(ns_source))
            //     if ns_target.module_idx == ns_source.module_idx =>
            // {
            //     Ok(())
            // }
            _ => Err(TypecheckError::TypeMismatch(target, source)),
        }
    }

    pub fn unify_pairs(
        &mut self,
        pairs: impl Iterator<Item = (impl Borrow<TypeId>, impl Borrow<TypeId>)>,
        type_vars: &mut TypeVars,
    ) -> TypecheckResult<()> {
        for (a, b) in pairs {
            let a_ty = *a.borrow();
            let b_ty = *b.borrow();
            self.unify(a_ty, b_ty, type_vars)?;
        }

        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct Traits {
    data: HashMap<TraitId, Trait>,
}

impl Traits {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolType {
    Variable(TypeId),
    Type(TypeId),
}

#[derive(Debug, Default)]
pub struct Scope {
    symbols: HashMap<Identifier, SymbolType>,
}

impl Scope {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn resolve_symbol(&self, symbol: Identifier) -> Option<SymbolType> {
        self.symbols.get(&symbol).map(|&s| s)
    }

    pub fn add_symbol(&mut self, symbol: Identifier, symbol_type: SymbolType) {
        // @@TODO: naming clashes
        self.symbols.insert(symbol, symbol_type);
    }
}

pub struct ScopeStack {
    scopes: Vec<Scope>,
}

impl Default for ScopeStack {
    fn default() -> Self {
        Self {
            scopes: vec![Scope::new()],
        }
    }
}

impl ScopeStack {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn resolve_symbol(&self, symbol: Identifier) -> Option<SymbolType> {
        for scope in self.iter_up() {
            if let Some(symbol_type) = scope.resolve_symbol(symbol) {
                return Some(symbol_type);
            }
        }

        None
    }

    pub fn resolve_compound_symbol(
        &self,
        symbols: &[Identifier],
        types: &Types,
    ) -> Option<SymbolType> {
        let mut last_scope = self.current_scope();
        let mut symbols_iter = symbols.iter().peekable();

        loop {
            match last_scope.resolve_symbol(*symbols_iter.next().unwrap()) {
                Some(symbol_ty @ SymbolType::Variable(type_id)) => match types.get(type_id) {
                    TypeValue::Namespace(namespace_ty) => match symbols_iter.peek() {
                        Some(_) => {
                            last_scope = &namespace_ty.members;
                            continue;
                        }
                        None => {
                            return Some(symbol_ty);
                        }
                    },
                    _ => {}
                },
                Some(symbol_ty) => match symbols_iter.peek() {
                    Some(_) => {
                        panic!("Found trying to namespace type.");
                    }
                    None => {
                        return Some(symbol_ty);
                    }
                },
                None => continue,
            }
        }
    }

    pub fn add_symbol(&mut self, symbol: Identifier, symbol_type: SymbolType) {
        self.current_scope_mut().add_symbol(symbol, symbol_type);
    }

    pub fn current_scope(&self) -> &Scope {
        self.scopes.last().unwrap()
    }

    pub fn extract_current_scope(&mut self) -> Scope {
        self.scopes.pop().unwrap()
    }

    pub fn current_scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    pub fn enter_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    pub fn iter_up(&self) -> impl Iterator<Item = &Scope> {
        self.scopes.iter().rev()
    }

    pub fn iter_up_mut(&mut self) -> impl Iterator<Item = &mut Scope> {
        self.scopes.iter_mut().rev()
    }

    pub fn pop_scope(&mut self) -> Scope {
        match self.scopes.pop() {
            Some(scope) => scope,
            None => panic!("Cannot pop root scope"),
        }
    }
}

#[derive(Debug)]
pub struct TypecheckState {
    pub in_loop: bool,
    pub ret_once: bool,
    pub func_ret_type: Option<TypeId>,
    pub current_module: ModuleIdx,
}

impl Default for TypecheckState {
    fn default() -> Self {
        Self {
            in_loop: false,
            ret_once: false,
            func_ret_type: None,
            current_module: ModuleIdx(0),
        }
    }
}

#[derive(Debug, Default)]
pub struct TypeVars {
    data: HashMap<TypeVar, TypeId>,
}

// struct VisitFnResult {

// }

// trait TypeValueVisitor<'c, O> {

//     fn types(&mut self) -> &mut Types<'c>;

//     fn visit_type(&mut self, ty: TypeId) -> O {
//         let type_value = self.types().get(ty);
//         self.visit_type_value(type_value)
//     }

//     fn visit_type_value(&mut self, type_value: &TypeValue<'c>) -> O {
//         match type_value {
//             TypeValue::Ref(inner) => self.visit_ref(inner),
//             TypeValue::RawRef(inner) => self.visit_raw_ref(inner),
//             TypeValue::Fn(_) => todo!(),
//             TypeValue::Var(_) => todo!(),
//             TypeValue::User(_) => todo!(),
//             TypeValue::Prim(_) => todo!(),
//             TypeValue::Unknown(_) => todo!(),
//             TypeValue::Namespace(_) => todo!(),
//         }
//     }

//     fn visit_ref(&mut self, value: &RefType) -> O {
//         self.visit_type(value.inner)
//     }

//     fn visit_raw_ref(&mut self, value: &RawRefType) -> O {
//         self.visit_type(value.inner)
//     }

//     fn visit_fn(&mut self, value: &FnType) -> (O) {
//         self.visit_type(value.args)
//         self.visit_type(value.ret)
//     }

//     fn visit_var(&mut self, value: &TypeVar) -> O {
//         self.visit_type(value.inner)
//     }

//     fn visit_user(&mut self, value: &UserType) -> O {
//         self.visit_type(value.inner)
//     }

//     fn visit_prim(&mut self, value: &PrimType) -> O {
//         self.visit_type(value.inner)
//     }

//     fn visit_unknown(&mut self, value: &UnknownType) -> O {
//         self.visit_type(value.inner)
//     }

//     fn visit_namespace(&mut self, value: &NamespaceType) -> O {
//         self.visit_type(value.inner)
//     }

//     // pub fn visit_ref(value: &mut TypeValue) -> O;
//     // pub fn visit_ref(value: &mut TypeValue) -> O;
// }

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

    pub fn substitute_many<'c>(
        &self,
        ty: impl IntoIterator<Item = impl Deref<Target = TypeId>>,
        types: &mut Types<'c>,
        wall: &Wall<'c>,
    ) -> Row<'c, TypeId> {
        Row::from_iter(
            ty.into_iter().map(|ty| self.substitute(*ty, types, wall)),
            wall,
        )
    }

    pub fn substitute<'c>(&self, ty: TypeId, types: &mut Types<'c>, wall: &Wall<'c>) -> TypeId {
        match types.get(ty) {
            TypeValue::Ref(RefType { inner }) => {
                let inner = self.substitute(*inner, types, wall);
                types.create(TypeValue::Ref(RefType { inner }), wall)
            }
            TypeValue::RawRef(RawRefType { inner }) => {
                let inner = self.substitute(*inner, types, wall);
                types.create(TypeValue::RawRef(RawRefType { inner }), wall)
            }
            TypeValue::Fn(FnType { args, ret }) => {
                let args = self.substitute_many(args, types, wall);
                let ret = self.substitute(*ret, types, wall);
                types.create(TypeValue::Fn(FnType { args, ret }), wall)
            }
            TypeValue::Var(type_var) => match self.resolve(*type_var) {
                Some(resolved) => resolved,
                None => ty,
            },
            TypeValue::User(UserType { def_id, args }) => {
                let args = self.substitute_many(args, types, wall);
                types.create(
                    TypeValue::User(UserType {
                        def_id: *def_id,
                        args,
                    }),
                    wall,
                )
            }
            TypeValue::Prim(_) => ty,
            TypeValue::Unknown(UnknownType { bounds }) => {
                let bounds = bounds.map(wall, |bound| TraitBound {
                    trt: bound.trt,
                    params: self.substitute_many(&bound.params, types, wall),
                });
                types.create(TypeValue::Unknown(UnknownType { bounds }), wall)
            }
            TypeValue::Namespace(_) => ty,
        }
    }
}

#[derive(Debug, Default)]
pub struct TypeInfo<'c> {
    pub types: Types<'c>,
    pub type_defs: TypeDefs<'c>,
    pub traits: Traits,
}

impl<'c> TypeInfo<'c> {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug, Default)]
pub struct TypecheckCtx {
    pub type_vars: TypeVars,
    pub state: TypecheckState,
    pub scopes: ScopeStack,
}

impl TypecheckCtx {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug)]
pub enum TypecheckError {
    TypeMismatch(TypeId, TypeId),
    UsingBreakOutsideLoop(Location),
    UsingContinueOutsideLoop(Location),
    UsingReturnOutsideFunction(Location),
    RequiresIrrefutablePattern(Location),
    // @@Todo: turn this into variants
    Message(String),
}

pub type TypecheckResult<T> = Result<T, TypecheckError>;

#[cfg(test)]
mod tests {
    use hash_alloc::{row, Castle};
    use hash_ast::{ident::IDENTIFIER_MAP, module::ModuleBuilder};

    use crate::writer::TypeWithCtx;

    use super::*;

    #[test]
    fn type_size() {
        let castle = Castle::new();
        let wall = castle.wall();

        let modules = ModuleBuilder::new().build();

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
