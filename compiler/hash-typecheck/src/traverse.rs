use std::mem;

use hash_alloc::Wall;
use hash_ast::{
    ast::{self, AstNode, AstNodeRef, TypeId},
    location::Location,
};

use crate::{
    types::{
        PrimType, RawRefType, RefType, TypeValue, TypecheckCtx, TypecheckError, TypecheckResult,
        UnknownType,
    },
    writer::TypeWithCtx,
};

pub struct Traverser<'c, 'm> {
    ctx: TypecheckCtx<'c, 'm>,
    wall: Wall<'c>,
}

impl<'c, 'm> Traverser<'c, 'm> {
    pub fn new(ctx: TypecheckCtx<'c, 'm>, wall: Wall<'c>) -> Self {
        Self { ctx, wall }
    }

    pub fn into_inner(self) -> (TypecheckCtx<'c, 'm>, Wall<'c>) {
        (self.ctx, self.wall)
    }

    pub fn traverse_function_call_args(
        &mut self,
        node: AstNodeRef<ast::FunctionCallArgs<'c>>,
    ) -> TypecheckResult<Vec<TypeId>> {
        // @@Performance: remove copying, return an iterator
        node.entries
            .iter()
            .map(|arg| self.traverse_expression(arg.ast_ref()))
            .collect()
    }

    pub fn traverse_function_call_expr(
        &mut self,
        node: AstNodeRef<ast::FunctionCallExpr<'c>>,
    ) -> TypecheckResult<TypeId> {
        let fn_type = self.traverse_expression(node.subject.ast_ref())?;
        let given_args = self.traverse_function_call_args(node.args.ast_ref())?;

        let fn_ret = match self.ctx.types.get(fn_type) {
            crate::types::TypeValue::Fn(fn_def_type) => {
                self.ctx.types.unify_pairs(
                    given_args.iter().zip(fn_def_type.args.iter()),
                    &mut self.ctx.type_vars,
                )?;
                fn_def_type.ret
            }
            _ => {
                return Err(TypecheckError::Message(format!(
                    "Expected a function type, got '{}'.",
                    TypeWithCtx::new(fn_type, &self.ctx),
                )))
            }
        };

        Ok(fn_ret)
    }

    pub fn traverse_variable_expr(
        &mut self,
        _: AstNodeRef<ast::VariableExpr<'c>>,
    ) -> TypecheckResult<TypeId> {
        // @@Todo
        Ok(self
            .ctx
            .types
            .create(TypeValue::Unknown(UnknownType::unbounded()), &self.wall))
    }

    pub fn traverse_literal(
        &mut self,
        node: AstNodeRef<ast::Literal<'c>>,
    ) -> TypecheckResult<TypeId> {
        match node.body() {
            ast::Literal::Str(_) => todo!(),
            ast::Literal::Char(_) => Ok(self
                .ctx
                .types
                .create(TypeValue::Prim(PrimType::Char), &self.wall)),
            ast::Literal::Int(_) => Ok(self
                .ctx
                .types
                .create(TypeValue::Prim(PrimType::I32), &self.wall)),
            ast::Literal::Float(_) => Ok(self
                .ctx
                .types
                .create(TypeValue::Prim(PrimType::F32), &self.wall)),
            ast::Literal::Set(_) => todo!(),
            ast::Literal::Map(_) => todo!(),
            ast::Literal::List(_) => todo!(),
            ast::Literal::Tuple(_) => todo!(),
            ast::Literal::Struct(_) => todo!(),
            ast::Literal::Function(_) => todo!(),
        }
    }

    pub fn traverse_type(&mut self, node: AstNodeRef<ast::Type<'c>>) -> TypecheckResult<TypeId> {
        match node.body() {
            ast::Type::Named(_) => {
                todo!()
            }
            ast::Type::Ref(inner_ty) => {
                let inner = self.traverse_type(inner_ty.ast_ref())?;
                Ok(self
                    .ctx
                    .types
                    .create(TypeValue::Ref(RefType { inner }), &self.wall))
            }
            ast::Type::RawRef(inner_ty) => {
                let inner = self.traverse_type(inner_ty.ast_ref())?;
                Ok(self
                    .ctx
                    .types
                    .create(TypeValue::RawRef(RawRefType { inner }), &self.wall))
            }
            ast::Type::TypeVar(_) => todo!(),
            ast::Type::Existential => todo!(),
            ast::Type::Infer => todo!(),
        }
    }

    pub fn traverse_typed_expr(
        &mut self,
        node: AstNodeRef<ast::TypedExpr<'c>>,
    ) -> TypecheckResult<TypeId> {
        let expr = self.traverse_expression(node.expr.ast_ref())?;
        let ty = self.traverse_type(node.ty.ast_ref())?;
        self.ctx.types.unify(expr, ty, &mut self.ctx.type_vars)?;
        Ok(expr)
    }

    pub fn traverse_expression(
        &mut self,
        node: AstNodeRef<ast::Expression<'c>>,
    ) -> TypecheckResult<TypeId> {
        match node.kind() {
            ast::ExpressionKind::FunctionCall(fn_call) => {
                self.traverse_function_call_expr(node.with_body(fn_call))
            }
            ast::ExpressionKind::Intrinsic(_) => todo!(),
            ast::ExpressionKind::Variable(variable) => {
                self.traverse_variable_expr(node.with_body(variable))
            }
            ast::ExpressionKind::PropertyAccess(_) => todo!(),
            ast::ExpressionKind::Ref(inner) => {
                let inner_ty = self.traverse_expression(inner.ast_ref())?;
                Ok(self
                    .ctx
                    .types
                    .create(TypeValue::Ref(RefType { inner: inner_ty }), &self.wall))
            }
            ast::ExpressionKind::Deref(inner) => {
                let given_ref_ty = self.traverse_expression(inner.ast_ref())?;

                let created_inner_ty = self
                    .ctx
                    .types
                    .create(TypeValue::Unknown(UnknownType::unbounded()), &self.wall);
                let created_ref_ty = self.ctx.types.create(
                    TypeValue::Ref(RefType {
                        inner: created_inner_ty,
                    }),
                    &self.wall,
                );
                self.ctx
                    .types
                    .unify(created_ref_ty, given_ref_ty, &mut self.ctx.type_vars)?;

                Ok(created_inner_ty)
            }
            ast::ExpressionKind::LiteralExpr(literal_expr) => {
                self.traverse_literal(literal_expr.ast_ref())
            }
            ast::ExpressionKind::Typed(typed_expr) => {
                self.traverse_typed_expr(node.with_body(typed_expr))
            }
            ast::ExpressionKind::Block(block) => self.traverse_block(block.ast_ref()),
            ast::ExpressionKind::Import(_) => todo!(),
        }
    }

    pub fn traverse_statement(
        &mut self,
        node: AstNodeRef<ast::Statement<'c>>,
    ) -> TypecheckResult<()> {
        match node.body() {
            ast::Statement::Expr(expr) => {
                let _ = self.traverse_expression(expr.ast_ref())?;
                Ok(())
            }
            ast::Statement::Return(maybe_expr) => match self.ctx.state.func_ret_type {
                Some(ret) => {
                    let given_ret = maybe_expr
                        .as_ref()
                        .map(|expr| self.traverse_expression(expr.ast_ref()))
                        .unwrap_or_else(|| {
                            Ok(self
                                .ctx
                                .types
                                .create(TypeValue::Prim(PrimType::Void), &self.wall))
                        })?;

                    // @@Todo: Here we might want to unify bidirectionally.
                    self.ctx
                        .types
                        .unify(ret, given_ret, &mut self.ctx.type_vars)?;

                    Ok(())
                }
                None => Err(TypecheckError::UsingReturnOutsideFunction(node.location())),
            },
            ast::Statement::Block(block) => self.traverse_block(block.ast_ref()).map(|_| ()),
            ast::Statement::Break => {
                if !self.ctx.state.in_loop {
                    Err(TypecheckError::UsingBreakOutsideLoop(node.location()))
                } else {
                    Ok(())
                }
            }
            ast::Statement::Continue => {
                if !self.ctx.state.in_loop {
                    Err(TypecheckError::UsingContinueOutsideLoop(node.location()))
                } else {
                    Ok(())
                }
            }
            ast::Statement::Let(_) => todo!(),
            ast::Statement::Assign(_) => todo!(),
            ast::Statement::StructDef(_) => todo!(),
            ast::Statement::EnumDef(_) => todo!(),
            ast::Statement::TraitDef(_) => todo!(),
        }
    }

    pub fn traverse_block(&mut self, node: AstNodeRef<ast::Block<'c>>) -> TypecheckResult<TypeId> {
        match node.body() {
            ast::Block::Match(_) => todo!(),
            ast::Block::Loop(loop_block) => {
                let last_in_loop = mem::replace(&mut self.ctx.state.in_loop, true);
                self.traverse_block(loop_block.ast_ref())?;
                self.ctx.state.in_loop = last_in_loop;

                Ok(self
                    .ctx
                    .types
                    .create(TypeValue::Prim(PrimType::Void), &self.wall))
            }
            ast::Block::Body(body_block) => self.traverse_body_block(node.with_body(body_block)),
        }
    }

    pub fn traverse_body_block(
        &mut self,
        node: AstNodeRef<ast::BodyBlock<'c>>,
    ) -> TypecheckResult<TypeId> {
        for statement in &node.statements {
            self.traverse_statement(statement.ast_ref())?;
        }
        match &node.expr {
            Some(expr) => self.traverse_expression(expr.ast_ref()),
            None => Ok(self
                .ctx
                .types
                .create(TypeValue::Prim(PrimType::Void), &self.wall)),
        }
    }

    pub fn traverse_module(&mut self, node: AstNodeRef<ast::Module<'c>>) -> TypecheckResult<()> {
        for statement in &node.contents {
            self.traverse_statement(statement.ast_ref())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use hash_alloc::Castle;
    use hash_ast::module::ModuleBuilder;

    use super::*;
    use crate::{
        types::{ScopeStack, Traits, TypeDefs, TypeVars, TypecheckState, Types},
        writer::TypeWithCtx,
    };

    #[test]
    fn traverse_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let modules = ModuleBuilder::new().build();

        let mut ctx = TypecheckCtx {
            types: Types::new(),
            type_defs: TypeDefs::new(),
            type_vars: TypeVars::new(),
            traits: Traits::new(),
            state: TypecheckState::default(),
            scopes: ScopeStack::new(),
            modules: &modules,
        };
    }
}
