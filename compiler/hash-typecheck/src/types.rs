#![allow(dead_code)]

use core::fmt;
use std::{borrow::Borrow, cell::RefCell, collections::HashMap, ops::Deref};

use dashmap::DashMap;
use hash_ast::{
    ast::TypeId,
    ident::Identifier,
    module::{ModuleIdx, Modules},
};
use hash_utils::counter;
use smallvec::SmallVec;

use crate::unify::Substitutions;

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
    pub id: TypeId,
}

#[derive(Debug)]
pub struct RawRefType {
    pub id: TypeId,
}

#[derive(Debug, Eq, PartialEq, Default)]
pub struct TypeArgs {
    data: SmallVec<[TypeId; 6]>,
}

impl TypeArgs {
    pub fn iter(&self) -> impl Iterator<Item = TypeId> + '_ {
        self.data.iter().map(|&x| x)
    }
}

impl Extend<TypeId> for TypeArgs {
    fn extend<T: IntoIterator<Item = TypeId>>(&mut self, iter: T) {
        self.data.extend(iter);
    }
}

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
pub enum TypeValue {
    Ref(RefType),
    RawRef(RawRefType),
    Fn(FnType),
    GenVar(GenTypeVar),
    Var(TypeVar),
    User(UserType),
    Prim(PrimType),
}

#[derive(Default)]
pub struct Types {
    data: RefCell<HashMap<TypeId, TypeValue>>,
}

impl Types {
    pub fn new() -> Self {
        Self {
            data: RefCell::new(HashMap::new()),
        }
    }

    pub fn get(&self, ty: TypeId) -> &TypeValue {
        self.data.borrow().get(&ty).unwrap()
    }

    pub fn create(&self, value: TypeValue) -> TypeId {
        let id = TypeId::new();
        self.data.borrow_mut().insert(id, value);
        id
    }

    pub fn unify(&self, a: TypeId, b: TypeId) -> TypecheckResult<(TypeId, Substitutions)> {
        let ty_a = self.get(a);
        let ty_b = self.get(b);

        // @@TODO: Figure out covariance, contravariance, and invariance rules.

        use TypeValue::*;
        match (ty_a, ty_b) {
            (Ref(ref_a), Ref(ref_b)) => self.unify(ref_a.id, ref_b.id),
            (RawRef(raw_a), RawRef(raw_b)) => self.unify(raw_a.id, raw_b.id),
            (Fn(fn_a), Fn(fn_b)) => {
                let (unified_args, args_sub) =
                    self.unify_pairs::<TypeArgs, _, _>(fn_a.args.iter().zip(fn_b.args.iter()))?;
                // Maybe this should be flipped (see variance comment above)
                let (unified_ret, ret_sub) = self.unify(fn_a.ret, fn_b.ret)?;

                let mut merged_sub = args_sub;
                merged_sub.update(self, &ret_sub);

                let unified_ty_id = self.create(Fn(FnType {
                    args: unified_args,
                    ret: unified_ret,
                }));

                Ok((unified_ty_id, merged_sub))
            }
            (GenVar(gen_a), GenVar(gen_b)) => {
                // Ensure that trait bounds are compatible
                // Copy over each bound (?)
                // Substitute. (?)
                todo!()
            }
            (GenVar(gen_a), _) => {
                // @@TODO: Ensure that trait bounds are compatible

                Ok((b, Substitutions::single(gen_a.id, b)))
            }
            (_, GenVar(gen_b)) => {
                // @@TODO: Ensure that trait bounds are compatible

                Ok((a, Substitutions::single(gen_b.id, a)))
            }
            (Var(var_a), Var(var_b)) if var_a == var_b => Ok((a, Substitutions::empty())),
            (User(user_a), User(user_b)) if user_a.def_id == user_b.def_id => {
                // Unify type arguments.
                let (unified_args, sub) = self
                    .unify_pairs::<TypeArgs, _, _>((user_a.args.iter()).zip(user_b.args.iter()))?;

                let unified_ty_id = self.create(User(UserType {
                    def_id: user_a.def_id,
                    args: unified_args,
                }));

                Ok((unified_ty_id, sub))
            }
            (Prim(prim_a), Prim(prim_b)) if prim_a == prim_b => Ok((a, Substitutions::empty())),
            _ => Err(TypecheckError::TypeMismatch(a, b)),
        }
    }

    pub fn unify_pairs<'ctx, C, P, T>(&self, pairs: P) -> TypecheckResult<(C, Substitutions)>
    where
        C: Default + Extend<TypeId>,
        P: Iterator<Item = (T, T)>,
        T: Borrow<TypeId>,
    {
        let mut acc_sub = Substitutions::empty();
        let mut type_ids = C::default();

        let size_hint = pairs.size_hint();
        type_ids.extend_reserve(size_hint.1.unwrap_or(size_hint.0));

        for (a, b) in pairs {
            let a_ty = *a.borrow();
            let b_ty = *b.borrow();
            let (ty, sub) = self.unify(a_ty, b_ty)?;

            type_ids.extend_one(ty);
            acc_sub.update(self, &sub);
        }

        Ok((type_ids, acc_sub))
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
    pub types: Types,
    pub type_defs: TypeDefs,
    pub traits: Traits,
    pub state: TypecheckState,
    pub modules: &'m Modules<'c>,
}

pub enum TypecheckError {
    TypeMismatch(TypeId, TypeId),
}

pub type TypecheckResult<T> = Result<T, TypecheckError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        println!("{:?}", std::mem::size_of::<TypeValue>());
    }
}
