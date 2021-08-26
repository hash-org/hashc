#![allow(dead_code)]

use core::fmt;
use std::collections::HashMap;

use hash_ast::{
    ast::TypeId,
    ident::Identifier,
    module::{ModuleIdx, Modules},
};
use hash_utils::counter;
use smallvec::SmallVec;

pub struct Trait {
    id: TraitId,
}

counter! {
    name: TraitId,
    counter_name: TRAIT_COUNTER,
    visibility: pub,
    method_visibility:,
}

pub struct TypeParams {
    data: SmallVec<[TypeId; 6]>,
}

pub struct TraitBounds {
    data: Vec<TraitBound>,
}

pub struct TraitBound {
    pub trt: Trait,
    pub params: TypeParams,
}

pub struct Generics {
    pub bounds: TraitBounds,
    pub params: TypeParams,
}

pub struct EnumVariantParams {
    data: SmallVec<[TypeId; 6]>,
}

pub struct EnumVariant {
    pub name: Identifier,
    pub data: EnumVariantParams,
}

pub struct EnumVariants {
    data: HashMap<Identifier, EnumVariant>,
}

pub struct EnumDef {
    pub name: Identifier,
    pub generics: Generics,
    pub variants: EnumVariants,
}

pub struct StructFields {
    data: HashMap<Identifier, TypeId>,
}

pub struct StructDef {
    pub name: Identifier,
    pub generics: Generics,
    pub fields: StructFields,
}

pub struct TypeDefs {
    data: HashMap<TypeDefId, TypeDefValue>,
}

impl TypeDefs {
    pub fn get(&self, ty_def: TypeDefId) -> &TypeDefValue {
        self.data.get(&ty_def).unwrap()
    }
}

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

pub struct RefType {
    pub id: TypeId,
}

pub struct RawRefType {
    pub id: TypeId,
}

#[derive(Debug, Eq, PartialEq)]
pub struct TypeArgs {
    data: SmallVec<[TypeId; 6]>,
}

impl TypeArgs {
    pub fn iter(&self) -> impl Iterator<Item=TypeId> + '_ {
        self.data.iter().map(|&x| x)
    }
}

pub struct UserType {
    pub def: TypeDefId,
    pub args: TypeArgs,
}

pub struct FnType {
    pub args: TypeArgs,
    pub ret: TypeId,
}

pub enum TypeValue {
    Ref(RefType),
    RawRef(RawRefType),
    Fn(FnType),
    GenVar(GenTypeVar),
    Var(TypeVar),
    User(UserType),
    Prim(PrimType),
}

pub struct Types {
    data: HashMap<TypeId, TypeValue>,
}

impl Types {
    pub fn get(&self, ty: TypeId) -> &TypeValue {
        self.data.get(&ty).unwrap()
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

pub struct TypecheckCtx<'m> {
    pub types: Types,
    pub type_defs: TypeDefs,
    pub traits: Traits,
    pub state: TypecheckState,
    pub modules: &'m Modules,
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
