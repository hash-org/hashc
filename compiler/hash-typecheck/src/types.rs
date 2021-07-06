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

pub struct TraitBound {
    trt: Trait,
    params: Vec<Type>,
}

pub struct Generics {
    params: Vec<Type>,
    bounds: Vec<TraitBound>,
}

pub struct EnumVariant {
    name: Identifier,
    data: Vec<Type>,
}

pub struct EnumDef {
    name: Identifier,
    generics: Generics,
    variants: HashMap<Identifier, EnumVariant>,
}

pub struct StructDef {
    name: Identifier,
    generics: Generics,
    fields: HashMap<Identifier, Type>,
}

pub struct TypeDefs {
    data: HashMap<TypeDefId, TypeDef>,
}

pub enum TypeDef {
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
    name: Identifier,
}

pub struct RefType {
    inner: TypeId,
}

pub struct RawRefType {
    inner: TypeId,
}

type TypeArgs = SmallVec<[TypeId; 6]>;

pub struct UserType {
    type_def_id: TypeDefId,
    args: TypeArgs,
}

pub struct FnType {
    args: TypeArgs,
    ret: TypeId,
}

pub enum Type {
    Ref(RefType),
    RawRef(RawRefType),
    Fn(FnType),
    GenTypeVar(GenTypeVar),
    TypeVar(TypeVar),
    User(UserType),
    Prim(PrimType),
}

pub struct Types {
    data: HashMap<TypeId, Type>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        println!("{:?}", std::mem::size_of::<Type>());
    }
}
