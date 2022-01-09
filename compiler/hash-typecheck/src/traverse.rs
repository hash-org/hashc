use crate::scope::{resolve_compound_symbol, ScopeStack, SymbolType};
use crate::state::TypecheckState;
use crate::storage::{GlobalStorage, ModuleStorage};
use crate::traits::{TraitBounds, TraitId, Traits};
use crate::types::{
    CoreTypeDefs, EnumDef, FnType, Generics, NamespaceType, PrimType, RawRefType, RefType,
    StructDef, StructFields, TupleType, TypeDefs, TypeId, TypeValue, TypeVars, Types, UnknownType,
};
use crate::types::{TypeDefId, TypeVar, UserType};
use crate::unify::{Substitution, Unifier, UnifyStrategy};
use crate::{
    error::{Symbol, TypecheckError, TypecheckResult},
    types::TypeDefValueKind,
};
use core::panic;
use hash_alloc::row;
use hash_alloc::{collections::row::Row, Wall};
use hash_ast::visitor::AstVisitor;
use hash_ast::{ast, ident::Identifier};
use hash_ast::{module::Modules, visitor, visitor::walk};
use hash_source::{
    location::{Location, SourceLocation},
    module::ModuleIdx,
};
use std::collections::HashSet;
use std::iter;
use std::{collections::HashMap, mem};

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

    pub fn typecheck_all(mut self) -> (TypecheckResult<()>, GlobalStorage<'c, 'w, 'm>) {
        for module in self.global_storage.modules.iter() {
            match self.typecheck_module(module.index()) {
                Ok(_) => continue,
                Err(e) => {
                    return (Err(e), self.global_storage);
                }
            }
        }
        (Ok(()), self.global_storage)
    }

    pub fn typecheck_interactive(
        mut self,
        block: ast::AstNodeRef<ast::BodyBlock<'c>>,
    ) -> (TypecheckResult<TypeId>, GlobalStorage<'c, 'w, 'm>) {
        let module_checker =
            ModuleTypechecker::new(&mut self, ModuleOrInteractive::Interactive(block));
        (module_checker.typecheck(), self.global_storage)
    }

    fn typecheck_module(&mut self, module_idx: ModuleIdx) -> TypecheckResult<TypeId> {
        if let Some(&ty_id) = self.already_checked.get(&module_idx) {
            Ok(ty_id)
        } else {
            let module_checker =
                ModuleTypechecker::new(self, ModuleOrInteractive::Module(module_idx));
            let ty_id = module_checker.typecheck()?;
            self.already_checked.insert(module_idx, ty_id);
            Ok(ty_id)
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ModuleOrInteractive<'i, 'c> {
    Module(ModuleIdx),
    Interactive(ast::AstNodeRef<'i, ast::BodyBlock<'c>>),
}

pub struct ModuleTypechecker<'c, 'w, 'm, 'g, 'i> {
    global_tc: &'g mut GlobalTypechecker<'c, 'w, 'm>,
    module_storage: ModuleStorage,
    module_or_interactive: ModuleOrInteractive<'i, 'c>,
}

impl<'c, 'w, 'm, 'g, 'i> ModuleTypechecker<'c, 'w, 'm, 'g, 'i> {
    pub fn new(
        global_tc: &'g mut GlobalTypechecker<'c, 'w, 'm>,
        module_or_interactive: ModuleOrInteractive<'i, 'c>,
    ) -> Self {
        let module_storage = ModuleStorage::new(&mut global_tc.global_storage);
        Self {
            global_tc,
            module_storage,
            module_or_interactive,
        }
    }

    pub fn wall(&self) -> &'w Wall<'c> {
        self.global_tc.global_wall
    }

    /// If the [ModuleOrInteractive] is the interactive mode, we return the [ModuleIdx] of `0` because
    /// this assumption holds when the interactive mode starts up
    pub fn current_module(&self) -> ModuleIdx {
        match self.module_or_interactive {
            ModuleOrInteractive::Module(idx) => idx,
            ModuleOrInteractive::Interactive(_) => ModuleIdx(0),
        }
    }

    pub fn source_location(&self, location: Location) -> SourceLocation {
        SourceLocation {
            location,
            module_index: self.current_module(),
        }
    }

    pub fn typecheck(mut self) -> TypecheckResult<TypeId> {
        match self.module_or_interactive {
            ModuleOrInteractive::Module(module_idx) => {
                let module = self
                    .global_tc
                    .global_storage
                    .modules
                    .get_by_index(module_idx);
                self.visit_module(self.wall(), module.ast())
            }
            ModuleOrInteractive::Interactive(block) => self.visit_body_block(self.wall(), block),
        }
    }

    fn create_type(&mut self, value: TypeValue<'c>) -> TypeId {
        self.global_tc.global_storage.types.create(value)
    }

    fn traits(&self) -> &Traits<'c, 'w> {
        &self.global_tc.global_storage.traits
    }

    fn types(&self) -> &Types<'c, 'w> {
        &self.global_tc.global_storage.types
    }

    fn type_defs(&self) -> &TypeDefs<'c, 'w> {
        &self.global_tc.global_storage.type_defs
    }

    fn type_defs_mut(&mut self) -> &mut TypeDefs<'c, 'w> {
        &mut self.global_tc.global_storage.type_defs
    }

    fn type_vars(&self) -> &TypeVars {
        &self.module_storage.type_vars
    }

    fn type_vars_mut(&mut self) -> &mut TypeVars {
        &mut self.module_storage.type_vars
    }

    fn create_unknown_type(&mut self) -> TypeId {
        self.global_tc.global_storage.types.create_unknown_type()
    }

    fn create_tuple_type(&mut self, types: Row<'c, TypeId>) -> TypeId {
        self.global_tc
            .global_storage
            .types
            .create(TypeValue::Tuple(TupleType { types }))
    }

    fn create_str_type(&mut self) -> TypeId {
        let str_def_id = self.core_type_defs().str;
        self.global_tc
            .global_storage
            .types
            .create(TypeValue::User(UserType {
                def_id: str_def_id,
                args: row![self.wall()],
            }))
    }

    fn create_list_type(&mut self, el_ty: TypeId) -> TypeId {
        let list_def_id = self.core_type_defs().list;
        self.global_tc
            .global_storage
            .types
            .create(TypeValue::User(UserType {
                def_id: list_def_id,
                args: row![self.wall(); el_ty],
            }))
    }

    fn create_set_type(&mut self, el_ty: TypeId) -> TypeId {
        let set_def_id = self.core_type_defs().set;
        self.global_tc
            .global_storage
            .types
            .create(TypeValue::User(UserType {
                def_id: set_def_id,
                args: row![self.wall(); el_ty],
            }))
    }

    fn create_map_type(&mut self, key_ty: TypeId, value_ty: TypeId) -> TypeId {
        let map_def_id = self.core_type_defs().map;
        self.global_tc
            .global_storage
            .types
            .create(TypeValue::User(UserType {
                def_id: map_def_id,
                args: row![self.wall(); key_ty, value_ty],
            }))
    }

    fn tc_state(&mut self) -> &mut TypecheckState {
        &mut self.module_storage.state
    }

    fn scopes(&mut self) -> &mut ScopeStack {
        &mut self.module_storage.scopes
    }

    fn core_type_defs(&mut self) -> &CoreTypeDefs {
        &self.global_tc.global_storage.core_type_defs
    }

    fn unifier<'s>(&'s mut self) -> Unifier<'c, 'w, 'm, 's, 's> {
        Unifier::new(&mut self.module_storage, &mut self.global_tc.global_storage)
    }

    fn resolve_compound_symbol(
        &mut self,
        symbols: &[Identifier],
        location: SourceLocation,
    ) -> TypecheckResult<SymbolType> {
        resolve_compound_symbol(
            &self.module_storage.scopes,
            &mut self.global_tc.global_storage.types,
            symbols,
            location,
        )
    }
}

impl<'c, 'w, 'm, 'g, 'i> visitor::AstVisitor<'c> for ModuleTypechecker<'c, 'w, 'm, 'g, 'i> {
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
        Ok(())
    }

    type AccessNameRet = ();
    fn visit_access_name(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::AccessName<'c>>,
    ) -> Result<Self::AccessNameRet, Self::Error> {
        Ok(())
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
        node: ast::AstNodeRef<ast::VariableExpr<'c>>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        let loc = self.source_location(node.location());

        match self.resolve_compound_symbol(&node.name.path, loc)? {
            SymbolType::Variable(var_ty_id) => Ok(var_ty_id),
            SymbolType::Type(_) | SymbolType::TypeDef(_) => {
                Err(TypecheckError::UsingTypeInVariablePos(Symbol::Compound {
                    path: node.name.path.to_owned(),
                    location: Some(loc),
                }))
            }
        }
    }

    type IntrinsicKeyRet = TypeId;
    fn visit_intrinsic_key(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::IntrinsicKey>,
    ) -> Result<Self::IntrinsicKeyRet, Self::Error> {
        // @@Todo: maybe we want to store intrinsic types somewhere
        Ok(self.create_unknown_type())
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
        self.unifier()
            .unify(expected_fn_ty, fn_ty, UnifyStrategy::ModifyBoth)?;

        Ok(ret_ty)
    }

    type PropertyAccessExprRet = TypeId;
    fn visit_property_access_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::PropertyAccessExpr<'c>>,
    ) -> Result<Self::PropertyAccessExprRet, Self::Error> {
        let property_ident = node.property.body().ident;
        let walk::PropertyAccessExpr { subject, .. } =
            walk::walk_property_access_expr(self, ctx, node)?;

        match self.types().get(subject) {
            TypeValue::User(UserType { def_id, .. }) => {
                let ty_def = self.type_defs().get(*def_id);

                match &ty_def.kind {
                    TypeDefValueKind::Struct(StructDef { fields, name, .. }) => {
                        if let Some(field_ty) = fields.get_field(property_ident) {
                            Ok(field_ty)
                        } else {
                            Err(TypecheckError::InvalidPropertyAccess {
                                ty_def_name: *name,
                                ty_def_location: ty_def.location,
                                field_name: property_ident,
                                location: self.source_location(node.location()),
                            })
                        }
                    }
                    TypeDefValueKind::Enum(EnumDef { /*name, */ .. }) => Err(TypecheckError::TypeIsNotStruct {
                        ty: subject,
                        // ty_def_name: *name,
                        ty_def_location: ty_def.location,
                        location: self.source_location(node.location()),
                    }),
                }
            }
            _ => Err(TypecheckError::TypeIsNotStruct {
                ty: subject,
                ty_def_location: None,
                location: self.source_location(node.location()),
            }),
        }
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
        self.unifier()
            .unify(created_ref_ty, given_ref_ty, UnifyStrategy::ModifyBoth)?;

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
        self.unifier().unify(expr, ty, UnifyStrategy::ModifyBoth)?;
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
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ImportExpr<'c>>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        Ok(walk::walk_import_expr(self, ctx, node)?.0)
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
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamedType<'c>>,
    ) -> Result<Self::NamedTypeRet, Self::Error> {
        let location = self.source_location(node.location());

        match self.resolve_compound_symbol(&node.name.path, location)? {
            SymbolType::Type(ty_id) => Ok(ty_id),
            SymbolType::TypeDef(def_id) => {
                let walk::NamedType { type_args, .. } = walk::walk_named_type(self, ctx, node)?;
                let def = self.type_defs().get(def_id);

                // @@Todo bounds
                match &def.kind {
                    TypeDefValueKind::Enum(EnumDef { generics, .. })
                    | TypeDefValueKind::Struct(StructDef { generics, .. }) => {
                        let args_sub = self.unifier().instantiate_vars_list(&generics.params)?;
                        let instantiated_args = self
                            .unifier()
                            .apply_sub_to_list_make_vec(&args_sub, &generics.params);

                        self.unifier().unify_pairs(
                            type_args.iter().zip(instantiated_args.iter()),
                            UnifyStrategy::ModifyTarget,
                        )?;
                        let ty = self.create_type(TypeValue::User(UserType {
                            def_id,
                            args: type_args,
                        }));
                        Ok(ty)
                    }
                }
            }
            SymbolType::Variable(_) => {
                Err(TypecheckError::UsingVariableInTypePos(Symbol::Compound {
                    path: node.name.path.to_owned(),
                    location: Some(location),
                }))
            }
        }
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
        Ok(self.create_type(TypeValue::Var(TypeVar {
            name: node.name.ident,
        })))
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

        let key_ty = self.unifier().unify_many(
            entries.iter().map(|&(key, _)| key),
            UnifyStrategy::ModifyBoth,
        )?;
        let value_ty = self.unifier().unify_many(
            entries.iter().map(|&(_, value)| value),
            UnifyStrategy::ModifyBoth,
        )?;

        Ok(self.create_map_type(key_ty, value_ty))
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
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListLiteral<'c>>,
    ) -> Result<Self::ListLiteralRet, Self::Error> {
        let entries = node
            .elements
            .iter()
            .map(|el| self.visit_expression(ctx, el.ast_ref()))
            .collect::<Result<Vec<_>, _>>()?;
        let el_ty = self
            .unifier()
            .unify_many(entries.iter().map(|&el| el), UnifyStrategy::ModifyBoth)?;

        Ok(self.create_list_type(el_ty))
    }

    type SetLiteralRet = TypeId;
    fn visit_set_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::SetLiteral<'c>>,
    ) -> Result<Self::SetLiteralRet, Self::Error> {
        let entries = node
            .elements
            .iter()
            .map(|el| self.visit_expression(ctx, el.ast_ref()))
            .collect::<Result<Vec<_>, _>>()?;
        let el_ty = self
            .unifier()
            .unify_many(entries.iter().map(|&el| el), UnifyStrategy::ModifyBoth)?;

        Ok(self.create_set_type(el_ty))
    }

    type TupleLiteralRet = TypeId;
    fn visit_tuple_literal(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleLiteral<'c>>,
    ) -> Result<Self::TupleLiteralRet, Self::Error> {
        let walk::TupleLiteral { elements } = walk::walk_tuple_literal(self, ctx, node)?;
        Ok(self.create_tuple_type(elements))
    }

    type StrLiteralRet = TypeId;
    fn visit_str_literal(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error> {
        Ok(self.create_str_type())
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
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructLiteral<'c>>,
    ) -> Result<Self::StructLiteralRet, Self::Error> {
        let location = self.source_location(node.location());
        let symbol_res = self.resolve_compound_symbol(&node.name.path, location)?;

        match symbol_res {
            SymbolType::Variable(_) => {
                Err(TypecheckError::UsingVariableInTypePos(Symbol::Compound {
                    path: node.name.path.to_owned(),
                    location: Some(location),
                }))
            }
            SymbolType::TypeDef(def_id) => {
                let type_def = self.type_defs().get(def_id);
                let (ty_id, _) = self.instantiate_type_def_unknown_args(def_id)?;
                match &type_def.kind {
                    TypeDefValueKind::Struct(struct_def) => {
                        self.typecheck_known_struct_literal(ctx, node, def_id, ty_id, &struct_def)
                    }
                    _ => Err(TypecheckError::TypeIsNotStruct {
                        ty: ty_id,
                        location,
                        ty_def_location: type_def.location,
                    }),
                }
            }
            SymbolType::Type(ty_id) => {
                let ty = self.types().get(ty_id);
                match ty {
                    TypeValue::User(UserType { def_id, .. }) => {
                        let type_def = self.type_defs().get(*def_id);

                        match &type_def.kind {
                            TypeDefValueKind::Struct(struct_def) => self
                                .typecheck_known_struct_literal(
                                    ctx,
                                    node,
                                    *def_id,
                                    ty_id,
                                    &struct_def,
                                ),
                            _ => Err(TypecheckError::TypeIsNotStruct {
                                ty: ty_id,
                                location,
                                ty_def_location: type_def.location,
                            }),
                        }
                    }
                    _ => Err(TypecheckError::TypeIsNotStruct {
                        ty: ty_id,
                        location,
                        ty_def_location: None,
                    }),
                }
            }
        }
    }

    type StructLiteralEntryRet = (Identifier, TypeId);
    fn visit_struct_literal_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructLiteralEntry<'c>>,
    ) -> Result<Self::StructLiteralEntryRet, Self::Error> {
        let walk::StructLiteralEntry { value, .. } =
            walk::walk_struct_literal_entry(self, ctx, node)?;
        Ok((node.name.ident, value))
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

        // unifier().unify returns
        match self.types().get(body_ty) {
            TypeValue::Prim(PrimType::Void) => {
                if ret_once {
                    let body_ty = self.create_unknown_type();
                    self.unifier()
                        .unify(return_ty, body_ty, UnifyStrategy::ModifyBoth)?;
                } else {
                    self.unifier()
                        .unify(return_ty, body_ty, UnifyStrategy::ModifyBoth)?;
                }
            }
            _ => {
                self.unifier()
                    .unify(return_ty, body_ty, UnifyStrategy::ModifyBoth)?;
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
        let ast::Name { ident } = node.name.body();
        let walk::FunctionDefArg { ty, .. } = walk::walk_function_def_arg(self, ctx, node)?;
        let arg_ty = ty.unwrap_or_else(|| self.create_unknown_type());
        self.scopes()
            .add_symbol(*ident, SymbolType::Variable(arg_ty));
        Ok(arg_ty)
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

                self.unifier()
                    .unify(ret, given_ret, UnifyStrategy::ModifyBoth)?;
                self.tc_state().ret_once = true;

                Ok(())
            }
            None => Err(TypecheckError::UsingReturnOutsideFunction(
                self.source_location(node.location()),
            )),
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
            Err(TypecheckError::UsingBreakOutsideLoop(
                self.source_location(node.location()),
            ))
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
            Err(TypecheckError::UsingContinueOutsideLoop(
                self.source_location(node.location()),
            ))
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
        let walk::LetStatement {
            pattern: pattern_ty,
            ty: annot_maybe_ty,
            bound: _,
            value: value_maybe_ty,
        } = walk::walk_let_statement(self, ctx, node)?;
        // if pattern_result.is_refutable {
        //     return Err(TypecheckError::RequiresIrrefutablePattern(node.location()));
        // }

        // @@Todo: bounds
        let annot_ty = annot_maybe_ty.unwrap_or_else(|| self.create_unknown_type());
        let value_ty = value_maybe_ty.unwrap_or_else(|| self.create_unknown_type());
        self.unifier().unify_many(
            [annot_ty, value_ty, pattern_ty].into_iter(),
            UnifyStrategy::ModifyBoth,
        )?;

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

    type StructDefEntryRet = (Identifier, TypeId);
    fn visit_struct_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructDefEntry<'c>>,
    ) -> Result<Self::StructDefEntryRet, Self::Error> {
        let walk::StructDefEntry { ty, default, .. } =
            walk::walk_struct_def_entry(self, ctx, node)?;

        let default_ty = default.unwrap_or_else(|| self.create_unknown_type());
        let field_ty = ty.unwrap_or_else(|| self.create_unknown_type());
        self.unifier()
            .unify(field_ty, default_ty, UnifyStrategy::ModifyBoth)?;

        Ok((node.name.ident, field_ty))
    }

    type StructDefRet = ();
    fn visit_struct_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StructDef<'c>>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        // @@Todo: the bound scope needs to be created for each type variable successively, not at
        // the end. Otherwise trait bounds will not resolve the type variables correctly.
        let bound = node
            .bound
            .as_ref()
            .map(|b| self.visit_bound(ctx, b.ast_ref()))
            .transpose()?;

        // Enter the bound if one exists, returning a key
        let maybe_type_var_key = bound
            .as_ref()
            .map(|bound| {
                // @@Todo: trait bounds
                let bound_vars: Vec<_> = bound
                    .iter()
                    .map(|&ty| match self.types().get(ty) {
                        TypeValue::Var(var) => Ok(*var),
                        _ => {
                            // We need to get the location of the bound for error reporting
                            let bound_location = node.bound.as_ref().unwrap().location();

                            Err(TypecheckError::BoundRequiresStrictlyTypeVars(
                                self.source_location(bound_location),
                            ))
                        }
                    })
                    .collect::<Result<_, _>>()?;

                Ok(self
                    .type_vars_mut()
                    .enter_bounded_type_var_scope(bound_vars.into_iter()))
            })
            .transpose()?;

        // Traverse the fields
        let fields = node
            .entries
            .iter()
            .map(|entry| self.visit_struct_def_entry(ctx, entry.ast_ref()))
            .collect::<Result<StructFields, _>>()?;

        // @@Todo: trait bounds

        // Create the type
        let current_module = self.current_module();

        let def_id = self.type_defs_mut().create(
            TypeDefValueKind::Struct(StructDef {
                name: node.name.ident,
                generics: Generics {
                    params: bound.unwrap_or_else(|| row![ctx; ]),
                    bounds: TraitBounds::empty(),
                },
                fields,
            }),
            Some(SourceLocation::new(node.name.location(), current_module)),
        );

        // Add the name to scope
        self.scopes()
            .add_symbol(node.name.ident, SymbolType::TypeDef(def_id));

        // Exit the bound if we entered one
        if let Some(type_var_key) = maybe_type_var_key {
            self.type_vars_mut().exit_type_var_scope(type_var_key);
        }

        Ok(())
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

    type PatternRet = TypeId;
    fn visit_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Pattern<'c>>,
    ) -> Result<Self::PatternRet, Self::Error> {
        walk::walk_pattern_same_children(self, ctx, node)
    }

    type TraitBoundRet = TraitId;
    fn visit_trait_bound(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TraitBound<'c>>,
    ) -> Result<Self::TraitBoundRet, Self::Error> {
        let walk::TraitBound {
            name: _,
            type_args: _,
        } = walk::walk_trait_bound(self, ctx, node)?;
        todo!()
        // match self.traits().get(trait_id) {}

        // @@Todo
        // Ok(())
    }

    type BoundRet = Row<'c, TypeId>;
    fn visit_bound(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Bound<'c>>,
    ) -> Result<Self::BoundRet, Self::Error> {
        let walk::Bound {
            type_args,
            trait_bounds: _,
        } = walk::walk_bound(self, ctx, node)?;

        // @@Todo: bounds
        Ok(type_args)
    }

    type EnumPatternRet = TypeId;
    fn visit_enum_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::EnumPattern<'c>>,
    ) -> Result<Self::EnumPatternRet, Self::Error> {
        todo!()
    }

    type StructPatternRet = TypeId;
    fn visit_struct_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StructPattern<'c>>,
    ) -> Result<Self::StructPatternRet, Self::Error> {
        todo!()
    }

    type NamespacePatternRet = TypeId;
    fn visit_namespace_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::NamespacePattern<'c>>,
    ) -> Result<Self::NamespacePatternRet, Self::Error> {
        todo!()
    }

    type TuplePatternRet = TypeId;
    fn visit_tuple_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TuplePattern<'c>>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        todo!()
    }

    type StrLiteralPatternRet = TypeId;
    fn visit_str_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error> {
        Ok(self.create_str_type())
    }

    type CharLiteralPatternRet = TypeId;
    fn visit_char_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error> {
        Ok(self.create_type(TypeValue::Prim(PrimType::Char)))
    }

    type IntLiteralPatternRet = TypeId;
    fn visit_int_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error> {
        Ok(self.create_type(TypeValue::Prim(PrimType::I32)))
    }

    type FloatLiteralPatternRet = TypeId;
    fn visit_float_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error> {
        Ok(self.create_type(TypeValue::Prim(PrimType::F32)))
    }

    type LiteralPatternRet = TypeId;
    fn visit_literal_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LiteralPattern>,
    ) -> Result<Self::LiteralPatternRet, Self::Error> {
        walk::walk_literal_pattern_same_children(self, ctx, node)
    }

    type OrPatternRet = TypeId;
    fn visit_or_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::OrPattern<'c>>,
    ) -> Result<Self::OrPatternRet, Self::Error> {
        todo!()
    }

    type IfPatternRet = TypeId;
    fn visit_if_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IfPattern<'c>>,
    ) -> Result<Self::IfPatternRet, Self::Error> {
        let walk::IfPattern { pattern, condition } = walk::walk_if_pattern(self, ctx, node)?;
        match self.types().get(condition) {
            TypeValue::Prim(PrimType::Bool) => Ok(pattern),
            _ => Err(TypecheckError::ExpectingBooleanInCondition {
                location: self.source_location(node.location()),
                found: condition,
            }),
        }
    }

    type BindingPatternRet = TypeId;
    fn visit_binding_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BindingPattern<'c>>,
    ) -> Result<Self::BindingPatternRet, Self::Error> {
        let variable_ty = self.create_unknown_type();
        self.scopes()
            .add_symbol(node.0.ident, SymbolType::Variable(variable_ty));
        Ok(variable_ty)
    }

    type IgnorePatternRet = TypeId;
    fn visit_ignore_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error> {
        Ok(self.create_unknown_type())
    }

    type DestructuringPatternRet = TypeId;
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
        let members =
            ScopeStack::with_scopes(&mut self.global_tc.global_storage, iter::once(curr_scope));
        let namespace_ty = self.create_type(TypeValue::Namespace(NamespaceType { members }));

        Ok(namespace_ty)
    }
}

impl<'c, 'w, 'm, 'g, 'i> ModuleTypechecker<'c, 'w, 'm, 'g, 'i> {
    fn typecheck_known_struct_literal(
        &mut self,
        ctx: &<Self as AstVisitor<'c>>::Ctx,
        node: ast::AstNodeRef<ast::StructLiteral<'c>>,
        def_id: TypeDefId,
        ty_id: TypeId,
        StructDef {
            name,
            fields,
            generics: _,
        }: &StructDef,
    ) -> TypecheckResult<TypeId> {
        let walk::StructLiteral {
            name: _,
            entries,
            type_args: _,
        } = walk::walk_struct_literal(self, ctx, node)?;

        // Make sure all fields are present
        let entries_given: HashSet<_> = entries.iter().map(|&(entry_name, _)| entry_name).collect();

        for (expected, _) in fields.iter() {
            if !entries_given.contains(&expected) {
                let ty_def = self.type_defs().get(def_id);

                let name_node = &node.body().name;
                let location = self.source_location(name_node.location());

                return Err(TypecheckError::MissingStructField {
                    ty_def_location: ty_def.location,
                    ty_def_name: *name,
                    field_name: expected,
                    location,
                });
            }
        }

        let ty_def = self.type_defs().get(def_id);

        // Unify args
        for (index, &(entry_name, entry_ty)) in (&entries).iter().enumerate() {
            match fields.get_field(entry_name) {
                Some(field_ty) => {
                    self.unifier()
                        .unify(entry_ty, field_ty, UnifyStrategy::ModifyTarget)?
                }
                None => {
                    let entry = node.entries.get(index).unwrap();

                    return Err(TypecheckError::UnresolvedStructField {
                        ty_def_location: ty_def.location,
                        ty_def_name: *name,
                        field_name: entry_name,
                        location: self.source_location(entry.location()), // @@Correctness: use location of struct field rather than struct def...
                    });
                }
            }
        }

        Ok(ty_id)
    }

    /// Returns a substitution for the type arguments as well.
    fn instantiate_type_def_unknown_args(
        &mut self,
        def_id: TypeDefId,
    ) -> TypecheckResult<(TypeId, Substitution)> {
        let type_def = &self.type_defs().get(def_id).kind;

        let (TypeDefValueKind::Struct(StructDef { generics, .. })
        | TypeDefValueKind::Enum(EnumDef { generics, .. })) = type_def;

        // @@Todo: bounds

        // We don't know what the arguments are, so we instantiate them to be all
        // unknown.
        let mut unifier = self.unifier();
        let vars_sub = unifier.instantiate_vars_list(&generics.params)?;
        let instantiated_vars = unifier.apply_sub_to_list_make_row(&vars_sub, &generics.params);
        let ty_id = self.create_type(TypeValue::User(UserType {
            def_id,
            args: instantiated_vars,
        }));

        Ok((ty_id, vars_sub))
    }
}
