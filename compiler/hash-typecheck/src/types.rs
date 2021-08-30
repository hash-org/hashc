#![allow(dead_code)]

use core::fmt;
use std::{
    borrow::{Borrow, BorrowMut},
    cell::Cell,
    collections::HashMap,
};

use dashmap::DashMap;
use hash_alloc::{brick::Brick, collections::row::Row, Wall};
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
pub struct TraitBounds<'c> {
    data: Row<'c, TraitBound<'c>>,
}

#[derive(Debug)]
pub struct TraitBound<'c> {
    pub trt: Trait,
    pub params: TypeArgs<'c>,
}

#[derive(Debug)]
pub struct Generics<'c> {
    pub bounds: TraitBounds<'c>,
    pub params: TypeArgs<'c>,
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

pub type TypeArgs<'c> = Row<'c, TypeId>;

#[derive(Debug)]
pub struct UserType<'c> {
    pub def_id: TypeDefId,
    pub args: TypeArgs<'c>,
}

#[derive(Debug)]
pub struct FnType<'c> {
    pub args: TypeArgs<'c>,
    pub ret: TypeId,
}

#[derive(Debug)]
pub struct NamespaceType {
    pub module_idx: ModuleIdx,
}

#[derive(Debug)]
pub enum TypeValue<'c> {
    Ref(RefType),
    RawRef(RawRefType),
    Fn(FnType<'c>),
    Var(TypeVar),
    User(UserType<'c>),
    Prim(PrimType),
    Unknown,
    Namespace(NamespaceType),
}

pub struct Types<'c> {
    data: HashMap<TypeId, Cell<&'c TypeValue<'c>>>,
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
    pub type_defs: TypeDefs<'c>,
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
    use hash_alloc::{row, Castle};
    use hash_ast::{ident::IDENTIFIER_MAP, module::ModuleBuilder};

    use crate::writer::TypeWriter;

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
        let unknown = ctx.types.create(TypeValue::Unknown, &wall);
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

        println!("{}", TypeWriter::new(fn1, &ctx));
    }
}
