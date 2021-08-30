use core::fmt;

use hash_ast::{ast::TypeId, ident::IDENTIFIER_MAP};
use hash_utils::tree_writing::{TreeNode, TreeWriter};

use crate::types::{
    EnumDef, FnType, NamespaceType, RawRefType, RefType, StructDef, TypeVar, TypecheckCtx, Types,
    UserType,
};

pub struct TypeWriter<'t, 'c, 'm> {
    ty: TypeId,
    ctx: &'t TypecheckCtx<'c, 'm>,
}

impl<'t, 'c, 'm> TypeWriter<'t, 'c, 'm> {
    pub fn new(ty: TypeId, ctx: &'t TypecheckCtx<'c, 'm>) -> Self {
        Self { ty, ctx }
    }

    pub fn for_type(&self, ty: TypeId) -> Self {
        Self { ty, ..*self }
    }

    pub fn to_tree_node(&self) -> TreeNode {
        match self.ctx.types.get(self.ty) {
            crate::types::TypeValue::Ref(RefType { inner }) => {
                TreeNode::branch("ref", vec![self.for_type(*inner).to_tree_node()])
            }
            crate::types::TypeValue::RawRef(RawRefType { inner }) => {
                TreeNode::branch("raw_ref", vec![self.for_type(*inner).to_tree_node()])
            }
            crate::types::TypeValue::Fn(FnType { args, ret }) => TreeNode::branch(
                "function",
                vec![
                    TreeNode::branch(
                        "arguments",
                        args.iter()
                            .map(|a| self.for_type(*a).to_tree_node())
                            .collect(),
                    ),
                    TreeNode::branch("return", vec![self.for_type(*ret).to_tree_node()]),
                ],
            ),
            crate::types::TypeValue::Var(TypeVar { name }) => {
                TreeNode::leaf(format!("var \"{}\"", IDENTIFIER_MAP.ident_name(*name)))
            }
            crate::types::TypeValue::Prim(prim) => TreeNode::leaf(format!(
                "primitive \"{}\"",
                match prim {
                    crate::types::PrimType::USize => "usize",
                    crate::types::PrimType::U8 => "u8",
                    crate::types::PrimType::U16 => "u16",
                    crate::types::PrimType::U32 => "u32",
                    crate::types::PrimType::U64 => "u64",
                    crate::types::PrimType::ISize => "isize",
                    crate::types::PrimType::I8 => "i8",
                    crate::types::PrimType::I16 => "i16",
                    crate::types::PrimType::I32 => "i32",
                    crate::types::PrimType::I64 => "i64",
                    crate::types::PrimType::Char => "char",
                }
            )),
            crate::types::TypeValue::User(UserType { def_id, args }) => {
                let label = match self.ctx.type_defs.get(*def_id) {
                    crate::types::TypeDefValue::Enum(EnumDef { name, .. }) => {
                        format!("enum \"{}\"", IDENTIFIER_MAP.ident_name(*name))
                    }
                    crate::types::TypeDefValue::Struct(StructDef { name, .. }) => {
                        format!("struct \"{}\"", IDENTIFIER_MAP.ident_name(*name))
                    }
                };

                TreeNode::branch(
                    label,
                    vec![TreeNode::branch(
                        "parameters",
                        args.iter()
                            .map(|&a| self.for_type(a).to_tree_node())
                            .collect(),
                    )],
                )
            }
            crate::types::TypeValue::Unknown => TreeNode::leaf("unknown".to_owned()),
            crate::types::TypeValue::Namespace(NamespaceType { module_idx }) => {
                TreeNode::leaf(format!("namespace ({:?})", module_idx))
            }
        }
    }
}

impl<'t, 'c, 'm> fmt::Display for TypeWriter<'t, 'c, 'm> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tree_node = self.to_tree_node();
        let tree_writer = TreeWriter::new(&tree_node);
        write!(f, "{}", tree_writer)
    }
}
