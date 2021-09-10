#![allow(dead_code)]

use core::fmt;
use std::{
    borrow::{Borrow, BorrowMut},
    cell::Cell,
    collections::{BTreeMap, HashMap},
};

use dashmap::DashMap;
use hash_alloc::{brick::Brick, collections::row::Row, row, Wall};
use hash_ast::{
    ast::TypeId,
    ident::Identifier,
    module::{ModuleIdx, Modules},
};
use hash_utils::counter;
use smallvec::smallvec;
use smallvec::SmallVec;

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

impl TraitBounds<'_> {
    pub fn empty() -> Self {
        Self { data: row![] }
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
    Char,
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
    pub module_idx: ModuleIdx,
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
        opts: &UnifyOptions,
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
                self.unify(ref_target.inner, ref_source.inner, opts)?;

                Ok(())
            }
            (RawRef(raw_target), RawRef(raw_source)) => {
                self.unify(raw_target.inner, raw_source.inner, opts)?;

                Ok(())
            }
            (Fn(fn_target), Fn(fn_source)) => {
                self.unify_pairs(fn_target.args.iter().zip(fn_source.args.iter()), opts)?;
                // Maybe this should be flipped (see variance comment above)
                self.unify(fn_target.ret, fn_source.ret, opts)?;

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
            (Var(var_target), _) => match type_vars.resolve(*var_target) {
                Some(resolved) => self.unify(resolved, source, opts, type_vars),
                None => match opts.type_var_strategy {
                    TypeVarStrategy::Match => Err(TypecheckError::TypeMismatch(target, source)),
                    TypeVarStrategy::Instantiate => {
                        type_vars.assign(*var_target, source);
                        Ok(())
                    }
                },
            },
            (User(user_target), User(user_source)) if user_target.def_id == user_source.def_id => {
                // Make sure we got same number of type arguments
                assert_eq!(user_target.args.len(), user_source.args.len());

                // Unify type arguments.
                self.unify_pairs((user_target.args.iter()).zip(user_source.args.iter()), opts)?;

                // let unified_ty_id = self.create(User(UserType {
                //     def_id: user_target.def_id,
                //     args: unified_args,
                // }));

                Ok(())
            }
            (Prim(prim_target), Prim(prim_source)) if prim_target == prim_source => Ok(()),
            (Namespace(ns_target), Namespace(ns_source))
                if ns_target.module_idx == ns_source.module_idx =>
            {
                Ok(())
            }
            _ => Err(TypecheckError::TypeMismatch(target, source)),
        }
    }

    pub fn unify_pairs(
        &mut self,
        pairs: impl Iterator<Item = (impl Borrow<TypeId>, impl Borrow<TypeId>)>,
        opts: &UnifyOptions,
    ) -> TypecheckResult<()> {
        for (a, b) in pairs {
            let a_ty = *a.borrow();
            let b_ty = *b.borrow();
            self.unify(a_ty, b_ty, opts)?;
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

    pub fn add_symbol(&mut self, symbol: Identifier, symbol_type: SymbolType) {
        self.current_scope_mut().add_symbol(symbol, symbol_type);
    }

    pub fn current_scope(&self) -> &Scope {
        self.scopes.last().unwrap()
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

pub struct TypecheckCtx<'c, 'm> {
    pub types: Types<'c>,
    pub type_defs: TypeDefs<'c>,
    pub type_vars: TypeVars,
    pub traits: Traits,
    pub state: TypecheckState,
    pub scopes: ScopeStack,
    pub modules: &'m Modules<'c>,
}

#[derive(Debug)]
pub enum TypecheckError {
    TypeMismatch(TypeId, TypeId),
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

        let mut ctx = TypecheckCtx {
            types: Types::new(),
            type_defs: TypeDefs::new(),
            traits: Traits::new(),
            state: TypecheckState::default(),
            scopes: ScopeStack::new(),
            modules: &modules,
        };

        let t_arg = ctx.types.create(
            TypeValue::Var(TypeVar {
                name: IDENTIFIER_MAP.create_ident("T"),
            }),
            &wall,
        );

        let foo_def = ctx.type_defs.create(TypeDefValue::Enum(EnumDef {
            name: IDENTIFIER_MAP.create_ident("Option"),
            generics: Generics {
                bounds: TraitBounds::default(),
                params: row![&wall; t_arg],
            },
            variants: EnumVariants::empty(),
        }));

        let char = ctx.types.create(TypeValue::Prim(PrimType::Char), &wall);
        let int = ctx.types.create(TypeValue::Prim(PrimType::I32), &wall);
        let unknown = ctx
            .types
            .create(TypeValue::Unknown(UnknownType::unbounded()), &wall);
        let foo = ctx.types.create(
            TypeValue::User(UserType {
                def_id: foo_def,
                args: row![&wall; int, unknown],
            }),
            &wall,
        );

        let fn1 = ctx.types.create(
            TypeValue::Fn(FnType {
                args: row![&wall; foo, unknown, char, int, foo],
                ret: int,
            }),
            &wall,
        );

        println!("{}", TypeWithCtx::new(fn1, &ctx));
    }
}
