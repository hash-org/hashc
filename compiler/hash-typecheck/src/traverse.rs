use std::{borrow::Borrow, collections::HashMap, mem};

use hash_alloc::{collections::row::Row, Castle, Wall};
use hash_ast::{
    ast::{self, AstNode, AstNodeRef, TypeId},
    location::Location,
    module::{Module, ModuleIdx, Modules},
};

use crate::{
    types::{
        FnType, NamespaceType, PrimType, RawRefType, RefType, TypeInfo, TypeValue, TypecheckCtx,
        TypecheckError, TypecheckResult, UnknownType,
    },
    writer::TypeWithCtx,
};

pub struct TraversePatternOutput {
    is_refutable: bool,
    ty: TypeId,
}

impl TraversePatternOutput {}

pub struct ModuleTraverser<'c, 'm> {
    type_info: TypeInfo<'c>,
    traversed_modules: HashMap<ModuleIdx, TypeId>,
    modules: &'m Modules<'c>,
    castle: &'c Castle,
}

impl<'c, 'm> ModuleTraverser<'c, 'm> {
    pub fn new(modules: &'m Modules<'c>, castle: &'c Castle) -> Self {
        Self {
            modules,
            castle,
            type_info: TypeInfo::new(),
            traversed_modules: HashMap::new(),
        }
    }

    pub fn type_info(&self) -> &TypeInfo<'c> {
        &self.type_info
    }

    pub fn traverse(self) -> TypecheckResult<TypeInfo<'c>> {
        let _ = self.traverse_module(self.modules.get_entry_point_unchecked().index())?;
        Ok(self.type_info)
    }

    pub fn traverse_module(&mut self, module_idx: ModuleIdx) -> TypecheckResult<TypeId> {
        match self.traversed_modules.get(&module_idx) {
            Some(&namespace_id) => Ok(namespace_id),
            None => {
                let module = self.modules.get_by_index(module_idx);
                let ctx = TypecheckCtx::new();
                let traverser = Traverser::new(self, ctx, Wall::new(&self.castle));
                let namespace_id = traverser.traverse_module(module.ast())?;
                self.traversed_modules.insert(module_idx, namespace_id);
                Ok(namespace_id)
            }
        }
    }
}

pub struct Traverser<'c, 'm, 't> {
    module_traverser: &'t ModuleTraverser<'c, 'm>,
    ctx: TypecheckCtx,
    wall: Wall<'c>,
}

impl<'c, 'm, 't> Traverser<'c, 'm, 't> {
    pub fn new(
        module_traverser: &'t ModuleTraverser<'c, 'm>,
        ctx: TypecheckCtx,
        wall: Wall<'c>,
    ) -> Self {
        Self {
            ctx,
            wall,
            module_traverser,
        }
    }

    fn type_info(&self) -> &TypeInfo<'c> {
        self.module_traverser.type_info()
    }

    fn unify_pairs(
        &mut self,
        pairs: impl Iterator<Item = (impl Borrow<TypeId>, impl Borrow<TypeId>)>,
    ) -> TypecheckResult<()> {
        self.type_info()
            .types
            .unify_pairs(pairs, &mut self.ctx.type_vars)
    }

    fn unify(&mut self, a: TypeId, b: TypeId) -> TypecheckResult<()> {
        self.type_info().types.unify(a, b, &mut self.ctx.type_vars)
    }

    fn create_type(&mut self, value: TypeValue<'c>) -> TypeId {
        self.type_info().types.create(value, &self.wall)
    }

    fn get_type(&mut self, ty: TypeId) -> &TypeValue<'c> {
        self.type_info().types.get(ty)
    }

    fn create_unknown_type(&mut self) -> TypeId {
        self.type_info()
            .types
            .create(TypeValue::Unknown(UnknownType::unbounded()), &self.wall)
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

        let fn_ret = match self.type_info().types.get(fn_type) {
            crate::types::TypeValue::Fn(fn_def_type) => {
                self.unify_pairs(given_args.iter().zip(fn_def_type.args.iter()))?;
                fn_def_type.ret
            }
            _ => {
                return Err(TypecheckError::Message(format!(
                    "Expected a function type, got '{}'.",
                    TypeWithCtx::new(fn_type, &self.type_info()),
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
            .type_info()
            .types
            .create(TypeValue::Unknown(UnknownType::unbounded()), &self.wall))
    }

    pub fn traverse_function_def(
        &mut self,
        node: AstNodeRef<ast::FunctionDef<'c>>,
    ) -> TypecheckResult<TypeId> {
        let ast::FunctionDef {
            args,
            fn_body,
            return_ty,
        } = node.body();

        let mut args_ty = Row::with_capacity(args.len(), &self.wall);
        for arg in args {
            let arg_ty = match &arg.ty {
                Some(ty) => self.traverse_type(ty.ast_ref())?,
                None => self.create_unknown_type(),
            };
            args_ty.push(arg_ty, &self.wall);
        }

        let ret_ty = return_ty
            .as_ref()
            .map(|return_ty| self.traverse_type(return_ty.ast_ref()))
            .unwrap_or_else(|| Ok(self.create_unknown_type()))?;

        let old_ret_ty = self.ctx.state.func_ret_type.replace(ret_ty);
        let old_ret_once = mem::replace(&mut self.ctx.state.ret_once, false);
        let body_ty = self.traverse_expression(fn_body.ast_ref())?;
        self.ctx.state.func_ret_type = old_ret_ty;
        let ret_once = mem::replace(&mut self.ctx.state.ret_once, old_ret_once);

        // unify returns
        match self.get_type(body_ty) {
            TypeValue::Prim(PrimType::Void) => {
                if ret_once {
                    let body_ty = self.create_unknown_type();
                    self.unify(ret_ty, body_ty)?;
                } else {
                    self.unify(ret_ty, body_ty)?;
                }
            }
            _ => {
                self.unify(ret_ty, body_ty)?;
            }
        };

        let fn_ty = self.create_type(TypeValue::Fn(FnType {
            args: args_ty,
            ret: ret_ty,
        }));

        Ok(fn_ty)
    }

    pub fn traverse_literal(
        &mut self,
        node: AstNodeRef<ast::Literal<'c>>,
    ) -> TypecheckResult<TypeId> {
        match node.body() {
            ast::Literal::Str(_) => todo!(),
            ast::Literal::Char(_) => Ok(self
                .type_info()
                .types
                .create(TypeValue::Prim(PrimType::Char), &self.wall)),
            ast::Literal::Int(_) => Ok(self
                .type_info()
                .types
                .create(TypeValue::Prim(PrimType::I32), &self.wall)),
            ast::Literal::Float(_) => Ok(self
                .type_info()
                .types
                .create(TypeValue::Prim(PrimType::F32), &self.wall)),
            ast::Literal::Function(func_def) => {
                self.traverse_function_def(node.with_body(func_def))
            }
            ast::Literal::Set(_) => todo!(),
            ast::Literal::Map(_) => todo!(),
            ast::Literal::List(_) => todo!(),
            ast::Literal::Tuple(_) => todo!(),
            ast::Literal::Struct(_) => todo!(),
        }
    }

    pub fn traverse_named_type(
        &mut self,
        node: AstNodeRef<ast::NamedType<'c>>,
    ) -> TypecheckResult<TypeId> {
        todo!()
        // match self.type_info().scopes.re(node.name.path) {

        // }
    }

    pub fn traverse_type(&mut self, node: AstNodeRef<ast::Type<'c>>) -> TypecheckResult<TypeId> {
        match node.body() {
            ast::Type::Named(_) => {
                todo!()
            }
            ast::Type::Ref(inner_ty) => {
                let inner = self.traverse_type(inner_ty.ast_ref())?;
                Ok(self
                    .type_info()
                    .types
                    .create(TypeValue::Ref(RefType { inner }), &self.wall))
            }
            ast::Type::RawRef(inner_ty) => {
                let inner = self.traverse_type(inner_ty.ast_ref())?;
                Ok(self
                    .type_info()
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
        self.unify(expr, ty)?;
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
                    .type_info()
                    .types
                    .create(TypeValue::Ref(RefType { inner: inner_ty }), &self.wall))
            }
            ast::ExpressionKind::Deref(inner) => {
                let given_ref_ty = self.traverse_expression(inner.ast_ref())?;

                let created_inner_ty = self
                    .type_info()
                    .types
                    .create(TypeValue::Unknown(UnknownType::unbounded()), &self.wall);
                let created_ref_ty = self.type_info().types.create(
                    TypeValue::Ref(RefType {
                        inner: created_inner_ty,
                    }),
                    &self.wall,
                );
                self.unify(created_ref_ty, given_ref_ty)?;

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
                                .type_info()
                                .types
                                .create(TypeValue::Prim(PrimType::Void), &self.wall))
                        })?;

                    // @@Todo: Here we might want to unify bidirectionally.
                    self.unify(ret, given_ret)?;
                    self.ctx.state.ret_once = true;

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
            ast::Statement::Let(let_statement) => {
                let pattern_result = self.traverse_pattern(let_statement.pattern.ast_ref())?;
                if pattern_result.is_refutable {
                    return Err(TypecheckError::RequiresIrrefutablePattern(node.location()));
                }

                let type_result = let_statement
                    .ty
                    .as_ref()
                    .map(|ty| self.traverse_type(ty.ast_ref()))
                    .transpose()?;

                // @@Todo: bounds

                let value_result = let_statement
                    .value
                    .as_ref()
                    .map(|value| self.traverse_expression(value.ast_ref()))
                    .transpose()?;

                // @@Todo: Bidirectional
                if let (Some(value_result), Some(type_result)) = (value_result, type_result) {
                    self.unify(value_result, type_result)?;
                }

                // This is probably not right
                if let Some(value_result) = value_result {
                    self.unify(pattern_result.ty, value_result)?;
                }

                Ok(())
            }
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
                    .type_info()
                    .types
                    .create(TypeValue::Prim(PrimType::Void), &self.wall))
            }
            ast::Block::Body(body_block) => self.traverse_body_block(node.with_body(body_block)),
        }
    }

    pub fn traverse_pattern(
        &mut self,
        node: AstNodeRef<ast::Pattern<'c>>,
    ) -> TypecheckResult<TraversePatternOutput> {
        match node.body() {
            ast::Pattern::Enum(_) => todo!(),
            ast::Pattern::Struct(_) => todo!(),
            ast::Pattern::Namespace(_) => todo!(),
            ast::Pattern::Tuple(_) => todo!(),
            ast::Pattern::Literal(_) => todo!(),
            ast::Pattern::Or(_) => todo!(),
            ast::Pattern::If(_) => todo!(),
            ast::Pattern::Binding(_) => todo!(),

            ast::Pattern::Ignore => todo!(),
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
                .type_info()
                .types
                .create(TypeValue::Prim(PrimType::Void), &self.wall)),
        }
    }

    pub fn traverse_module(&mut self, node: &ast::Module<'c>) -> TypecheckResult<TypeId> {
        for statement in &node.contents {
            self.traverse_statement(statement.ast_ref())?;
        }

        let namespace_ty = self.create_type(TypeValue::Namespace(NamespaceType {
            members: self.ctx.scopes.extract_current_scope(),
        }));

        Ok(namespace_ty)
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

        // let mut ctx = TypecheckCtx {
        //     types: Types::new(),
        //     type_defs: TypeDefs::new(),
        //     type_vars: TypeVars::new(),
        //     traits: Traits::new(),
        //     state: TypecheckState::default(),
        //     scopes: ScopeStack::new(),
        //     modules: &modules,
        // };
    }
}
