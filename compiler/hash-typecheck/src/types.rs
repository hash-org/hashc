#![allow(dead_code)]

use core::fmt;
use std::collections::HashMap;

use hash_ast::{ast::TypeId, ident::Identifier};
use hash_utils::counter;
use smallvec::SmallVec;

//
// struct str = { contents: [u8] }
//
// trait size = <T> => (T) => usize;
//
// struct ArrayData = <T> => {
//     data: &raw T,
//     len: usize,
//     capacity: usize,
// }
//
// let drop<ArrayData<T>> = (array: ArrayData<T>) => {
//     free(array.data);
// };
//
// struct Array = <T> => {
//     data: &ArrayData<T>,
// }
//
//
//

pub struct Trait {
    id: TraitId,
}

counter! {
    name: TraitId,
    counter_name: TRAIT_COUNTER,
    visibility:,
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

pub enum TypeDefValue {
    Enum(EnumDef),
    Struct(StructDef),
}

counter! {
    name: TypeDefId,
    counter_name: TYPE_DEF_COUNTER,
    visibility:,
    method_visibility:,
}

counter! {
    name: GenTypeVarId,
    counter_name: GEN_TYPE_VAR_COUNTER,
    visibility:,
    method_visibility:,
}

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
    id: GenTypeVarId,
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

pub struct TypeVar {
    pub name: Identifier,
}

pub struct RefType {
    pub inner: Type,
}

pub struct RawRefType {
    pub inner: Type,
}

pub struct TypeArgs {
    data: SmallVec<[TypeId; 6]>,
}

pub struct UserType {
    pub def: TypeDef,
    pub args: TypeArgs,
}

pub struct FnType {
    pub args: TypeArgs,
    pub ret: Type,
}

pub struct Type {
    id: TypeId,
}
pub struct TypeDef {
    id: TypeDefId,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        println!("{:?}", std::mem::size_of::<TypeValue>());
    }
}
