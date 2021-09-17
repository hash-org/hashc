use hash_alloc::Wall;
use hash_ast::{
    ast::{self, AstNode, AstNodeRef, TypeId},
    location::Location,
};

use crate::{
    types::{PrimType, TypeValue, TypecheckCtx, TypecheckError, TypecheckResult},
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

    pub fn traverse_expression(
        &mut self,
        node: AstNodeRef<ast::Expression<'c>>,
    ) -> TypecheckResult<TypeId> {
        match node.kind() {
            ast::ExpressionKind::FunctionCall(fn_call) => {
                self.traverse_function_call_expr(node.with_body(fn_call))
            }
            ast::ExpressionKind::Intrinsic(_) => todo!(),
            ast::ExpressionKind::Variable(_) => todo!(),
            ast::ExpressionKind::PropertyAccess(_) => todo!(),
            ast::ExpressionKind::Ref(_) => todo!(),
            ast::ExpressionKind::Deref(_) => todo!(),
            ast::ExpressionKind::LiteralExpr(_) => todo!(),
            ast::ExpressionKind::Typed(_) => todo!(),
            ast::ExpressionKind::Block(_) => todo!(),
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
            ast::Statement::Return(_) => todo!(),
            ast::Statement::Block(_) => todo!(),
            ast::Statement::Break => todo!(),
            ast::Statement::Continue => todo!(),
            ast::Statement::Let(_) => todo!(),
            ast::Statement::Assign(_) => todo!(),
            ast::Statement::StructDef(_) => todo!(),
            ast::Statement::EnumDef(_) => todo!(),
            ast::Statement::TraitDef(_) => todo!(),
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
