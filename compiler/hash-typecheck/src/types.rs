#![allow(dead_code)]

use core::fmt;
use std::{
    borrow::{Borrow, BorrowMut},
    cell::Cell,
    collections::HashMap,
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

#[derive(Debug, Default)]
pub struct TraitBounds {
    data: Vec<TraitBound>,
}

impl TraitBounds {
    pub fn empty() -> Self {
        Self::default()
    }
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

#[derive(Debug, Default)]
pub struct EnumVariants {
    data: HashMap<Identifier, EnumVariant>,
}

impl EnumVariants {
    pub fn empty() -> Self {
        Self::default()
    }
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

#[derive(Debug, Default)]
pub struct TypeDefs {
    data: HashMap<TypeDefId, TypeDefValue>,
}

impl TypeDefs {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self, ty_def: TypeDefId) -> &TypeDefValue {
        self.data.get(&ty_def).unwrap()
    }

    pub fn create(&mut self, def: TypeDefValue) -> TypeDefId {
        let id = TypeDefId::new();
        self.data.insert(id, def);
        id
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
        // Right now, there are no sub/super types, so these variance rules aren't applicable. In
        // other words, unify is symmetric over target/source. However it is not foreseeable that
        // this will continue to be the case in the future.

        let target_ty = self.get(target);
        let source_ty = self.get(source);

        use TypeValue::*;
        match (target_ty, source_ty) {
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

#[derive(Debug, Default)]
pub struct Traits {
    data: HashMap<TraitId, Trait>,
}

impl Traits {
    pub fn new() -> Self {
        Self::default()
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
    use hash_ast::{ident::IDENTIFIER_MAP, module::ModuleBuilder};

    use crate::writer::TypeWriter;

    use super::*;

    #[test]
    fn type_size() {
        let castle = Castle::new();
        let wall = castle.wall();

        let modules = ModuleBuilder::new().build();

        let mut ctx = TypecheckCtx {
            types: Types::new(wall),
            type_defs: TypeDefs::new(),
            traits: Traits::new(),
            state: TypecheckState::default(),
            modules: &modules,
        };

        let t_arg = ctx.types.create(TypeValue::Var(TypeVar {
            name: IDENTIFIER_MAP.create_ident("T"),
        }));

        let foo_def = ctx.type_defs.create(TypeDefValue::Enum(EnumDef {
            name: IDENTIFIER_MAP.create_ident("Option"),
            generics: Generics {
                bounds: TraitBounds::empty(),
                params: smallvec![t_arg],
            },
            variants: EnumVariants::empty(),
        }));

        let char = ctx.types.create(TypeValue::Prim(PrimType::Char));
        let int = ctx.types.create(TypeValue::Prim(PrimType::I32));
        let unknown = ctx.types.create(TypeValue::Unknown);
        let foo = ctx.types.create(TypeValue::User(UserType {
            def_id: foo_def,
            args: smallvec![int, unknown],
        }));

        let fn1 = ctx.types.create(TypeValue::Fn(FnType {
            args: smallvec![foo, unknown, char, int, foo],
            ret: int,
        }));

        println!("{}", TypeWriter::new(fn1, &ctx));
    }
}
