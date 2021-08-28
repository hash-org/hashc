#![allow(dead_code)]

use core::fmt;
use std::{
    borrow::{Borrow, BorrowMut},
    cell::{Cell, Ref, RefCell, RefMut},
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use dashmap::DashMap;
use hash_alloc::{brick::Brick, Wall};
use hash_ast::{
    ast::TypeId,
    ident::Identifier,
    module::{ModuleIdx, Modules},
};
use hash_utils::counter;
use smallvec::smallvec;
use smallvec::SmallVec;

#[derive(Debug)]
pub struct Trait {
    id: TraitId,
}

counter! {
    name: TraitId,
    counter_name: TRAIT_COUNTER,
    visibility: pub,
    method_visibility:,
}

#[derive(Debug)]
pub struct TraitBounds {
    data: Vec<TraitBound>,
}

#[derive(Debug)]
pub struct TraitBound {
    pub trt: Trait,
    pub params: TypeArgs,
}

#[derive(Debug)]
pub struct Generics {
    pub bounds: TraitBounds,
    pub params: TypeArgs,
}

#[derive(Debug)]
pub struct EnumVariantParams {
    data: SmallVec<[TypeId; 6]>,
}

#[derive(Debug)]
pub struct EnumVariant {
    pub name: Identifier,
    pub data: EnumVariantParams,
}

#[derive(Debug)]
pub struct EnumVariants {
    data: HashMap<Identifier, EnumVariant>,
}

#[derive(Debug)]
pub struct EnumDef {
    pub name: Identifier,
    pub generics: Generics,
    pub variants: EnumVariants,
}

#[derive(Debug)]
pub struct StructFields {
    data: HashMap<Identifier, TypeId>,
}

#[derive(Debug)]
pub struct StructDef {
    pub name: Identifier,
    pub generics: Generics,
    pub fields: StructFields,
}

#[derive(Debug)]
pub struct TypeDefs {
    data: HashMap<TypeDefId, TypeDefValue>,
}

impl TypeDefs {
    pub fn get(&self, ty_def: TypeDefId) -> &TypeDefValue {
        self.data.get(&ty_def).unwrap()
    }
}

#[derive(Debug)]
pub enum TypeDefValue {
    Enum(EnumDef),
    Struct(StructDef),
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

#[derive(Debug, Eq, PartialEq, Copy, Clone, Hash)]
pub struct GenTypeVar {
    pub id: GenTypeVarId,
}

impl GenTypeVar {
    pub fn new() -> Self {
        Self {
            id: GenTypeVarId::new(),
        }
    }
}

impl fmt::Display for GenTypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "T{}", self.id.0)
    }
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

pub type TypeArgs = SmallVec<[TypeId; 6]>;

#[derive(Debug)]
pub struct UserType {
    pub def_id: TypeDefId,
    pub args: TypeArgs,
}

#[derive(Debug)]
pub struct FnType {
    pub args: TypeArgs,
    pub ret: TypeId,
}

#[derive(Debug)]
pub struct NamespaceType {
    pub module_idx: ModuleIdx,
}

#[derive(Debug)]
pub enum TypeValue {
    Ref(RefType),
    RawRef(RawRefType),
    Fn(FnType),
    Var(TypeVar),
    User(UserType),
    Prim(PrimType),
    Unknown,
    Namespace(NamespaceType),
}

pub struct Types<'c> {
    wall: Wall<'c>,
    data: HashMap<TypeId, Cell<&'c TypeValue>>,
}

impl<'c> Types<'c> {
    pub fn new(wall: Wall<'c>) -> Self {
        Self {
            wall,
            data: HashMap::new(),
        }
    }

    pub fn get(&self, ty: TypeId) -> &'c TypeValue {
        self.data.get(&ty).unwrap().get()
    }

    pub fn set(&self, target: TypeId, source: TypeId) {
        if target == source {
            return;
        }
        let other_val = self.data.get(&source).unwrap().get();
        self.data.get(&target).unwrap().set(other_val);
    }

    pub fn create(&mut self, value: TypeValue) -> TypeId {
        let id = TypeId::new();
        self.data
            .borrow_mut()
            .insert(id, Cell::new(Brick::new(value, &self.wall).disown()));
        id
    }

    pub fn unify(&mut self, target: TypeId, source: TypeId) -> TypecheckResult<()> {
        // Already the same type
        if target == source {
            return Ok(());
        }

        // @@TODO: Figure out covariance, contravariance, and invariance rules.
        let target_ty = self.get(target);
        let source_ty = self.get(source);

        use TypeValue::*;
        match (&*target_ty, &*source_ty) {
            (Ref(ref_target), Ref(ref_source)) => {
                self.unify(ref_target.inner, ref_source.inner)?;
            }
            (RawRef(raw_target), RawRef(raw_source)) => {
                self.unify(raw_target.inner, raw_source.inner)?;
            }
            (Fn(fn_target), Fn(fn_source)) => {
                self.unify_pairs(fn_target.args.iter().zip(fn_source.args.iter()))?;
                // Maybe this should be flipped (see variance comment above)
                self.unify(fn_target.ret, fn_source.ret)?;

                // let merged_sub = args_sub.merge(self, &ret_sub);

                // let unified_ty = Fn(FnType {
                //     args: unified_args,
                //     ret: Box::new(unified_ret),
                // });
            }
            (Unknown, Unknown) => {
                // @@TODO: Ensure that trait bounds are compatible
            }
            (Unknown, _) => {
                // @@TODO: Ensure that trait bounds are compatible
                self.set(target, source);
            }
            (_, Unknown) => {
                // @@TODO: Ensure that trait bounds are compatible
                self.set(source, target);
            }
            (Var(var_target), Var(var_source)) if var_target == var_source => {}
            (User(user_target), User(user_source)) if user_target.def_id == user_source.def_id => {
                // Make sure we got same number of type arguments
                assert_eq!(user_target.args.len(), user_source.args.len());

                // Unify type arguments.
                self.unify_pairs((user_target.args.iter()).zip(user_source.args.iter()))?;

                // let unified_ty_id = self.create(User(UserType {
                //     def_id: user_target.def_id,
                //     args: unified_args,
                // }));
            }
            (Prim(prim_target), Prim(prim_source)) if prim_target == prim_source => {}
            (Namespace(ns_target), Namespace(ns_source))
                if ns_target.module_idx == ns_source.module_idx => {}
            _ => {
                return Err(TypecheckError::TypeMismatch(target, source));
            }
        }

        Ok(())
    }

    pub fn unify_pairs(
        &mut self,
        pairs: impl Iterator<Item = (impl Borrow<TypeId>, impl Borrow<TypeId>)>,
    ) -> TypecheckResult<()> {
        for (a, b) in pairs {
            let a_ty = *a.borrow();
            let b_ty = *b.borrow();
            self.unify(a_ty, b_ty)?;
        }

        Ok(())
    }
}

pub struct Traits {
    data: HashMap<TraitId, Trait>,
}

pub struct GenTypeVars {
    data: HashMap<GenTypeVarId, TraitBounds>,
}

pub struct TypecheckState {
    pub in_loop: bool,
    pub ret_once: bool,
    pub func_ret_type: Option<TypeId>,
    pub gen_type_vars: GenTypeVars,
    pub current_module: ModuleIdx,
}

pub struct TypecheckCtx<'c, 'm> {
    pub types: Types<'c>,
    pub type_defs: TypeDefs,
    pub traits: Traits,
    pub state: TypecheckState,
    pub modules: &'m Modules<'c>,
}

#[derive(Debug)]
pub enum TypecheckError {
    TypeMismatch(TypeId, TypeId),
}

pub type TypecheckResult<T> = Result<T, TypecheckError>;

#[cfg(test)]
mod tests {
    use hash_alloc::Castle;

    use super::*;

    #[test]
    fn type_size() {
        let castle = Castle::new();
        let wall = castle.wall();
        let mut types = Types::new(wall);

        let char = types.create(TypeValue::Prim(PrimType::Char));
        let int = types.create(TypeValue::Prim(PrimType::I32));
        let unknown = types.create(TypeValue::Unknown);

        let fn1 = types.create(TypeValue::Fn(FnType {
            args: smallvec![unknown],
            ret: int,
        }));
        let fn2 = types.create(TypeValue::Fn(FnType {
            args: smallvec![char],
            ret: int,
        }));

        let unify_res = types.unify(fn1, fn2);

        println!("{:?}", unify_res);

        match types.get(fn1) {
            TypeValue::Fn(FnType { args, ret }) => {
                println!("args of fn1: {:?}", args.iter().map(|&a| types.get(a)).collect::<Vec<_>>());
                println!("ret of fn1: {:?}", types.get(*ret));
            }
            _ => {}
        }
    }
}
