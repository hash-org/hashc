use crate::scope::ScopeStack;
use crate::state::TypecheckState;
use crate::storage::{GlobalStorage, ModuleStorage};
use crate::types::{TypeVar, UserType};
use crate::unify::{unify, unify_many, unify_pairs};
use crate::{
    types::{
        FnType, NamespaceType, PrimType, RawRefType, RefType, TypeValue, TypecheckError,
        TypecheckResult, UnknownType,
    },
};
use hash_alloc::row;
use hash_alloc::{collections::row::Row, Wall};
use hash_ast::ast;
use hash_ast::visitor::AstVisitor;
use hash_ast::{
    ast::TypeId,
    module::{ModuleIdx, Modules},
    visitor,
    visitor::walk,
};
use std::{borrow::Borrow, collections::HashMap, mem};

pub struct TraversePatternOutput {
    is_refutable: bool,
    ty: TypeId,
}

impl TraversePatternOutput {}

pub struct GlobalTypechecker<'c, 'w, 'm> {
    global_storage: GlobalStorage<'c, 'w, 'm>,
    already_checked: HashMap<ModuleIdx, TypeId>,
    global_wall: &'w Wall<'c>,
}

impl<'c, 'w, 'm> GlobalTypechecker<'c, 'w, 'm> {
    pub fn for_modules(modules: &'m Modules<'c>, wall: &'w Wall<'c>) -> Self {
        Self {
            global_storage: GlobalStorage::new_with_modules(modules, wall),
            already_checked: HashMap::new(),
            global_wall: wall,
        }
    }

    pub fn typecheck_all(mut self) -> TypecheckResult<GlobalStorage<'c, 'w, 'm>> {
        for module in self.global_storage.modules.iter() {
            self.typecheck_module(module.index())?;
        }
        Ok(self.global_storage)
    }

    fn typecheck_module(&mut self, module_idx: ModuleIdx) -> TypecheckResult<TypeId> {
        if let Some(&ty_id) = self.already_checked.get(&module_idx) {
            Ok(ty_id)
        } else {
            let module_checker = ModuleTypechecker::new(self, module_idx);
            let ty_id = module_checker.typecheck()?;
            self.already_checked.insert(module_idx, ty_id);
            Ok(ty_id)
        }
    }
}

pub struct ModuleTypechecker<'c, 'w, 'm, 'g> {
    global_tc: &'g mut GlobalTypechecker<'c, 'w, 'm>,
    module_storage: ModuleStorage,
    module_idx: ModuleIdx,
}

impl<'c, 'w, 'm, 'g> ModuleTypechecker<'c, 'w, 'm, 'g> {
    pub fn new(global_tc: &'g mut GlobalTypechecker<'c, 'w, 'm>, module_idx: ModuleIdx) -> Self {
        Self {
            global_tc,
            module_storage: ModuleStorage::default(),
            module_idx,
        }
    }

    pub fn wall(&self) -> &'w Wall<'c> {
        self.global_tc.global_wall
    }

    pub fn typecheck(mut self) -> TypecheckResult<TypeId> {
        let module = self
            .global_tc
            .global_storage
            .modules
            .get_by_index(self.module_idx);
        let ctx = self.wall();
        self.visit_module(ctx, module.ast())
    }

    fn unify_pairs(
        &mut self,
        pairs: impl Iterator<Item = (impl Borrow<TypeId>, impl Borrow<TypeId>)>,
    ) -> TypecheckResult<()> {
        unify_pairs(
            &mut self.module_storage,
            &self.global_tc.global_storage,
            pairs,
        )
    }

    fn unify_many(&mut self, type_list: impl Iterator<Item = TypeId>) -> TypecheckResult<TypeId> {
        let def = self.create_unknown_type();
        unify_many(
            &mut self.module_storage,
            &self.global_tc.global_storage,
            type_list,
            def,
        )
    }

    fn unify(&mut self, a: TypeId, b: TypeId) -> TypecheckResult<()> {
        unify(
            &mut self.module_storage,
            &self.global_tc.global_storage,
            a,
            b,
        )
    }

    fn create_type(&mut self, value: TypeValue<'c>) -> TypeId {
        let types = &mut self.global_tc.global_storage.types;
        types.create(value)
    }

    fn get_type(&self, ty: TypeId) -> &'c TypeValue<'c> {
        let types = &self.global_tc.global_storage.types;
        types.get(ty)
    }

    fn create_unknown_type(&mut self) -> TypeId {
        let types = &mut self.global_tc.global_storage.types;
        types.create(TypeValue::Unknown(UnknownType::unbounded()))
    }

    fn resolve_type_var(&mut self, type_var: TypeVar) -> Option<TypeId> {
        self.module_storage.type_vars.resolve(type_var)
    }

    fn tc_state(&mut self) -> &mut TypecheckState {
        &mut self.module_storage.state
    }

    fn scopes(&mut self) -> &mut ScopeStack {
        &mut self.module_storage.scopes
    }
}

impl<'c, 'w, 'm, 'g> visitor::AstVisitor<'c> for ModuleTypechecker<'c, 'w, 'm, 'g> {
    type Ctx = Wall<'c>;

    type CollectionContainer<T: 'c> = Row<'c, T>;
    fn try_collect_items<T: 'c, E, I: Iterator<Item = Result<T, E>>>(
        ctx: &Self::Ctx,
        items: I,
    ) -> Result<Self::CollectionContainer<T>, E> {
        Row::try_from_iter(items, ctx)
    }

    type Error = TypecheckError;

    type ImportRet = TypeId;
    fn visit_import(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Import>,
    ) -> Result<Self::ImportRet, Self::Error> {
        self.global_tc.typecheck_module(node.index)
    }

    type NameRet = ();

    fn visit_name(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        todo!()
    }

    type AccessNameRet = ();

    fn visit_access_name(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::AccessName<'c>>,
    ) -> Result<Self::AccessNameRet, Self::Error> {
        todo!()
    }

    type LiteralRet = TypeId;
    fn visit_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Literal<'c>>,
    ) -> Result<Self::LiteralRet, Self::Error> {
        walk::walk_literal_same_children(self, ctx, node)
    }

    type ExpressionRet = TypeId;
    fn visit_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Expression<'c>>,
    ) -> Result<Self::ExpressionRet, Self::Error> {
        walk::walk_expression_same_children(self, ctx, node)
    }

    type VariableExprRet = TypeId;
    fn visit_variable_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::VariableExpr<'c>>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        todo!()
    }

    type IntrinsicKeyRet = TypeId;
    fn visit_intrinsic_key(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::IntrinsicKey>,
    ) -> Result<Self::IntrinsicKeyRet, Self::Error> {
        todo!()
    }

    type FunctionCallArgsRet = Row<'c, TypeId>;
    fn visit_function_call_args(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallArgs<'c>>,
    ) -> Result<Self::FunctionCallArgsRet, Self::Error> {
        Ok(walk::walk_function_call_args(self, ctx, node)?.entries)
    }

    type FunctionCallExprRet = TypeId;
    fn visit_function_call_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionCallExpr<'c>>,
    ) -> Result<Self::FunctionCallExprRet, Self::Error> {
        let walk::FunctionCallExpr {
            args: given_args,
            subject: fn_ty,
        } = walk::walk_function_call_expr(self, ctx, node)?;

        let ret_ty = self.create_unknown_type();
        let expected_fn_ty = self.create_type(TypeValue::Fn(FnType {
            args: given_args,
            ret: ret_ty,
        }));
        self.unify(expected_fn_ty, fn_ty)?;

        Ok(expected_fn_ty)
    }

    type PropertyAccessExprRet = TypeId;
    fn visit_property_access_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::PropertyAccessExpr<'c>>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error> {
        todo!()
    }

    type RefExprRet = TypeId;
    fn visit_ref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefExpr<'c>>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let walk::RefExpr {
            inner_expr: inner_ty,
        } = walk::walk_ref_expr(self, ctx, node)?;
        Ok(self.create_type(TypeValue::Ref(RefType { inner: inner_ty })))
    }

    type DerefExprRet = TypeId;
    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DerefExpr<'c>>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let walk::DerefExpr(given_ref_ty) = walk::walk_deref_expr(self, ctx, node)?;

        let created_inner_ty = self.create_type(TypeValue::Unknown(UnknownType::unbounded()));
        let created_ref_ty = self.create_type(TypeValue::Ref(RefType {
            inner: created_inner_ty,
        }));
        self.unify(created_ref_ty, given_ref_ty)?;

        Ok(created_inner_ty)
    }

    type LiteralExprRet = TypeId;
    fn visit_literal_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LiteralExpr<'c>>,
    ) -> Result<Self::LiteralExprRet, Self::Error> {
        Ok(walk::walk_literal_expr(self, ctx, node)?.0)
    }

    type TypedExprRet = TypeId;
    fn visit_typed_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypedExpr<'c>>,
    ) -> Result<Self::TypedExprRet, Self::Error> {
        let walk::TypedExpr { expr, ty } = walk::walk_typed_expr(self, ctx, node)?;
        self.unify(expr, ty)?;
        Ok(expr)
    }

    type BlockExprRet = TypeId;
    fn visit_block_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BlockExpr<'c>>,
    ) -> Result<Self::BlockExprRet, Self::Error> {
        Ok(walk::walk_block_expr(self, ctx, node)?.0)
    }

    type ImportExprRet = TypeId;
    fn visit_import_expr(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::ImportExpr<'c>>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        todo!()
    }

    type TypeRet = TypeId;
    fn visit_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Type<'c>>,
    ) -> Result<Self::TypeRet, Self::Error> {
        walk::walk_type_same_children(self, ctx, node)
    }

    type NamedTypeRet = TypeId;
    fn visit_named_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::NamedType<'c>>,
    ) -> Result<Self::NamedTypeRet, Self::Error> {
        todo!()
        // let resolved_symbol = self
        //     .module_traverser
        //     .storage
        //     .scopes
        //     .resolve_compound_symbol(&node.name.path, &self.module_traverser.storage.types);
        // match resolved_symbol {
        //     Some(SymbolType::Type(type_id)) => Ok(type_id),
        //     Some(SymbolType::Variable(_)) => Err(TypecheckError::UsingVariableInTypePos(
        //         node.name.path.to_owned(),
        //     )),
        //     None => Err(TypecheckError::UnresolvedSymbol(node.name.path.to_owned())),
        // }
    }

    type RefTypeRet = TypeId;
    fn visit_ref_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefType<'c>>,
    ) -> Result<Self::RefTypeRet, Self::Error> {
        let walk::RefType(inner) = walk::walk_ref_type(self, ctx, node)?;
        Ok(self.create_type(TypeValue::Ref(RefType { inner })))
    }

    type RawRefTypeRet = TypeId;
    fn visit_raw_ref_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RawRefType<'c>>,
    ) -> Result<Self::RawRefTypeRet, Self::Error> {
        let walk::RawRefType(inner) = walk::walk_raw_ref_type(self, ctx, node)?;
        Ok(self.create_type(TypeValue::RawRef(RawRefType { inner })))
    }

    type TypeVarRet = TypeId;
    fn visit_type_var(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeVar<'c>>,
    ) -> Result<Self::TypeVarRet, Self::Error> {
        match self.resolve_type_var(TypeVar {
            name: node.name.ident,
        }) {
            Some(type_var_id) => Ok(type_var_id),
            // @@Todo: maybe we should check if there is a normal symbol with that name, for more
            // descriptive errors.
            None => Err(TypecheckError::UnresolvedSymbol(vec![node.name.ident])),
        }
    }

    type ExistentialTypeRet = TypeId;
    fn visit_existential_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::ExistentialType>,
    ) -> Result<Self::ExistentialTypeRet, Self::Error> {
        // By definition, an existential type is an anonymous type variable.
        Ok(self.create_unknown_type())
    }

    type InferTypeRet = TypeId;
    fn visit_infer_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::InferType>,
    ) -> Result<Self::InferTypeRet, Self::Error> {
        // @@Todo: Is this right?
        Ok(self.create_unknown_type())
    }

    type MapLiteralRet = TypeId;
    fn visit_map_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapLiteral<'c>>,
    ) -> Result<Self::MapLiteralRet, Self::Error> {
        let entries = node
            .elements
            .iter()
            .map(|entry| self.visit_map_literal_entry(ctx, entry.ast_ref()))
            .collect::<Result<Vec<_>, _>>()?;

        let key_ty = self.unify_many(entries.iter().map(|&(key, _)| key))?;
        let value_ty = self.unify_many(entries.iter().map(|&(_, value)| value))?;

        // @@Todo: get map def id somehow
        let map_type_def_id = (|| todo!())();
        let map_literal_ty = self.create_type(TypeValue::User(UserType {
            def_id: map_type_def_id,
            args: row![&self.wall(); key_ty, value_ty],
        }));

        Ok(map_literal_ty)
    }

    type MapLiteralEntryRet = (TypeId, TypeId);
    fn visit_map_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MapLiteralEntry<'c>>,
    ) -> Result<Self::MapLiteralEntryRet, Self::Error> {
        let walk::MapLiteralEntry { key, value } = walk::walk_map_literal_entry(self, ctx, node)?;
        Ok((key, value))
    }

    type ListLiteralRet = TypeId;
    fn visit_list_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::ListLiteral<'c>>,
    ) -> Result<Self::ListLiteralRet, Self::Error> {
        todo!()
    }

    type SetLiteralRet = TypeId;
    fn visit_set_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::SetLiteral<'c>>,
    ) -> Result<Self::SetLiteralRet, Self::Error> {
        todo!()
    }

    type TupleLiteralRet = TypeId;
    fn visit_tuple_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TupleLiteral<'c>>,
    ) -> Result<Self::TupleLiteralRet, Self::Error> {
        todo!()
    }

    type StrLiteralRet = TypeId;
    fn visit_str_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error> {
        todo!()
    }

    type CharLiteralRet = TypeId;
    fn visit_char_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error> {
        Ok(self.create_type(TypeValue::Prim(PrimType::Char)))
    }

    type FloatLiteralRet = TypeId;
    fn visit_float_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error> {
        Ok(self.create_type(TypeValue::Prim(PrimType::F32)))
    }

    type IntLiteralRet = TypeId;
    fn visit_int_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error> {
        Ok(self.create_type(TypeValue::Prim(PrimType::I32)))
    }

    type StructLiteralRet = TypeId;
    fn visit_struct_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StructLiteral<'c>>,
    ) -> Result<Self::StructLiteralRet, Self::Error> {
        todo!()
    }

    type StructLiteralEntryRet = ();
    fn visit_struct_literal_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StructLiteralEntry<'c>>,
    ) -> Result<Self::StructLiteralEntryRet, Self::Error> {
        todo!()
    }

    type FunctionDefRet = TypeId;
    fn visit_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionDef<'c>>,
    ) -> Result<Self::FunctionDefRet, Self::Error> {
        let args_ty = Self::try_collect_items(
            ctx,
            node.args
                .iter()
                .map(|arg| self.visit_function_def_arg(ctx, arg.ast_ref())),
        )?;

        let return_ty = node
            .return_ty
            .as_ref()
            .map(|return_ty| self.visit_type(ctx, return_ty.ast_ref()))
            .unwrap_or_else(|| Ok(self.create_unknown_type()))?;

        let old_ret_ty = self.tc_state().func_ret_type.replace(return_ty);
        let old_ret_once = mem::replace(&mut self.tc_state().ret_once, false);

        let body_ty = self.visit_expression(ctx, node.fn_body.ast_ref())?;

        self.tc_state().func_ret_type = old_ret_ty;
        let ret_once = mem::replace(&mut self.tc_state().ret_once, old_ret_once);

        // unify returns
        match self.get_type(body_ty) {
            TypeValue::Prim(PrimType::Void) => {
                if ret_once {
                    let body_ty = self.create_unknown_type();
                    self.unify(return_ty, body_ty)?;
                } else {
                    self.unify(return_ty, body_ty)?;
                }
            }
            _ => {
                self.unify(return_ty, body_ty)?;
            }
        };

        let fn_ty = self.create_type(TypeValue::Fn(FnType {
            args: args_ty,
            ret: return_ty,
        }));

        Ok(fn_ty)
    }

    type FunctionDefArgRet = TypeId;
    fn visit_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionDefArg<'c>>,
    ) -> Result<Self::FunctionDefArgRet, Self::Error> {
        let walk::FunctionDefArg { name: _, ty } = walk::walk_function_def_arg(self, ctx, node)?;
        Ok(ty.unwrap_or_else(|| self.create_unknown_type()))
    }

    type BlockRet = TypeId;
    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Block<'c>>,
    ) -> Result<Self::BlockRet, Self::Error> {
        walk::walk_block_same_children(self, ctx, node)
    }

    type MatchCaseRet = TypeId;
    fn visit_match_case(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::MatchCase<'c>>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        todo!()
    }

    type MatchBlockRet = TypeId;
    fn visit_match_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::MatchBlock<'c>>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        todo!()
    }

    type LoopBlockRet = TypeId;
    fn visit_loop_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LoopBlock<'c>>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        let last_in_loop = mem::replace(&mut self.tc_state().in_loop, true);
        self.visit_block(ctx, node.0.ast_ref())?;
        self.tc_state().in_loop = last_in_loop;

        Ok(self.create_type(TypeValue::Prim(PrimType::Void)))
    }

    type BodyBlockRet = TypeId;
    fn visit_body_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BodyBlock<'c>>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        let walk::BodyBlock {
            statements: _,
            expr,
        } = walk::walk_body_block(self, ctx, node)?;
        Ok(expr.unwrap_or_else(|| self.create_type(TypeValue::Prim(PrimType::Void))))
    }

    type StatementRet = ();
    fn visit_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Statement<'c>>,
    ) -> Result<Self::StatementRet, Self::Error> {
        walk::walk_statement_same_children(self, ctx, node)
    }

    type ExprStatementRet = ();
    fn visit_expr_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ExprStatement<'c>>,
    ) -> Result<Self::ExprStatementRet, Self::Error> {
        let walk::ExprStatement(_) = walk::walk_expr_statement(self, ctx, node)?;
        Ok(())
    }

    type ReturnStatementRet = ();
    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ReturnStatement<'c>>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        match self.tc_state().func_ret_type {
            Some(ret) => {
                let given_ret = walk::walk_return_statement(self, ctx, node)?
                    .0
                    .unwrap_or_else(|| self.create_type(TypeValue::Prim(PrimType::Void)));

                // @@Todo: Here we might want to unify bidirectionally.
                self.unify(ret, given_ret)?;
                self.tc_state().ret_once = true;

                Ok(())
            }
            None => Err(TypecheckError::UsingReturnOutsideFunction(node.location())),
        }
    }

    type BlockStatementRet = ();
    fn visit_block_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BlockStatement<'c>>,
    ) -> Result<Self::BlockStatementRet, Self::Error> {
        let walk::BlockStatement(_) = walk::walk_block_statement(self, ctx, node)?;
        Ok(())
    }

    type BreakStatementRet = ();
    fn visit_break_statement(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        if !self.tc_state().in_loop {
            Err(TypecheckError::UsingBreakOutsideLoop(node.location()))
        } else {
            Ok(())
        }
    }

    type ContinueStatementRet = ();
    fn visit_continue_statement(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        if !self.tc_state().in_loop {
            Err(TypecheckError::UsingContinueOutsideLoop(node.location()))
        } else {
            Ok(())
        }
    }

    type LetStatementRet = ();
    fn visit_let_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LetStatement<'c>>,
    ) -> Result<Self::LetStatementRet, Self::Error> {
        let pattern_result = self.visit_pattern(ctx, node.pattern.ast_ref())?;
        if pattern_result.is_refutable {
            return Err(TypecheckError::RequiresIrrefutablePattern(node.location()));
        }

        let type_result = node
            .ty
            .as_ref()
            .map(|ty| self.visit_type(ctx, ty.ast_ref()))
            .transpose()?;

        // @@Todo: bounds

        let value_result = node
            .value
            .as_ref()
            .map(|value| self.visit_expression(ctx, value.ast_ref()))
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

    type AssignStatementRet = ();

    fn visit_assign_statement(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::AssignStatement<'c>>,
    ) -> Result<Self::AssignStatementRet, Self::Error> {
        todo!()
    }

    type StructDefEntryRet = ();

    fn visit_struct_def_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StructDefEntry<'c>>,
    ) -> Result<Self::StructDefEntryRet, Self::Error> {
        todo!()
    }

    type StructDefRet = ();

    fn visit_struct_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StructDef<'c>>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        todo!()
    }

    type EnumDefEntryRet = ();

    fn visit_enum_def_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::EnumDefEntry<'c>>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        todo!()
    }

    type EnumDefRet = ();

    fn visit_enum_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::EnumDef<'c>>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        todo!()
    }

    type TraitDefRet = ();

    fn visit_trait_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TraitDef<'c>>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        todo!()
    }

    type PatternRet = TraversePatternOutput;
    fn visit_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::Pattern<'c>>,
    ) -> Result<Self::PatternRet, Self::Error> {
        todo!()
    }

    type TraitBoundRet = ();

    fn visit_trait_bound(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TraitBound<'c>>,
    ) -> Result<Self::TraitBoundRet, Self::Error> {
        todo!()
    }

    type BoundRet = ();

    fn visit_bound(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::Bound<'c>>,
    ) -> Result<Self::BoundRet, Self::Error> {
        todo!()
    }

    type EnumPatternRet = ();

    fn visit_enum_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::EnumPattern<'c>>,
    ) -> Result<Self::EnumPatternRet, Self::Error> {
        todo!()
    }

    type StructPatternRet = ();

    fn visit_struct_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StructPattern<'c>>,
    ) -> Result<Self::StructPatternRet, Self::Error> {
        todo!()
    }

    type NamespacePatternRet = ();

    fn visit_namespace_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::NamespacePattern<'c>>,
    ) -> Result<Self::NamespacePatternRet, Self::Error> {
        todo!()
    }

    type TuplePatternRet = ();

    fn visit_tuple_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TuplePattern<'c>>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        todo!()
    }

    type StrLiteralPatternRet = ();

    fn visit_str_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error> {
        todo!()
    }

    type CharLiteralPatternRet = ();

    fn visit_char_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error> {
        todo!()
    }

    type IntLiteralPatternRet = ();

    fn visit_int_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error> {
        todo!()
    }

    type FloatLiteralPatternRet = ();

    fn visit_float_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error> {
        todo!()
    }

    type LiteralPatternRet = ();

    fn visit_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error> {
        todo!()
    }

    type OrPatternRet = ();

    fn visit_or_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::OrPattern<'c>>,
    ) -> Result<Self::OrPatternRet, Self::Error> {
        todo!()
    }

    type IfPatternRet = ();

    fn visit_if_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::IfPattern<'c>>,
    ) -> Result<Self::IfPatternRet, Self::Error> {
        todo!()
    }

    type BindingPatternRet = ();

    fn visit_binding_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::BindingPattern<'c>>,
    ) -> Result<Self::BindingPatternRet, Self::Error> {
        todo!()
    }

    type IgnorePatternRet = ();

    fn visit_ignore_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error> {
        todo!()
    }

    type DestructuringPatternRet = ();

    fn visit_destructuring_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::DestructuringPattern<'c>>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error> {
        todo!()
    }

    type ModuleRet = TypeId;
    fn visit_module(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Module<'c>>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let walk::Module { contents: _ } = walk::walk_module(self, ctx, node)?;

        let curr_scope = self.scopes().extract_current_scope();
        let namespace_ty = self.create_type(TypeValue::Namespace(NamespaceType {
            members: curr_scope,
        }));

        Ok(namespace_ty)
    }
}

#[cfg(test)]
mod tests {
    use hash_alloc::Castle;
    use hash_ast::module::ModuleBuilder;

    #[test]
    fn traverse_test() {
        let castle = Castle::new();
        let _wall = castle.wall();

        let _modules = ModuleBuilder::new().build();

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
