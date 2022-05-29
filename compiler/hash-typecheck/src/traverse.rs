//! All rights reserved 2022 (c) The Hash Language authors
use crate::types::{
    CoreTypeDefs, EnumDef, FnType, NamespaceType, PrimType, RefType, StructDef, TupleType,
    TypeDefStorage, TypeId, TypeStorage, TypeValue, TypeVars,
};
use crate::types::{TypeDefId, TypeVar, UserType};
use crate::unify::{Substitution, Unifier, UnifyStrategy};
use crate::{
    error::ArgumentLengthMismatch,
    storage::{GlobalStorage, SourceStorage},
};
use crate::{
    refutability::is_pattern_irrefutable,
    traits::{MatchTraitImplResult, TraitHelper, TraitId, TraitImplStorage, TraitStorage},
};

use crate::scope::{resolve_compound_symbol, ScopeStack, SymbolType};
use crate::{
    error::{Symbol, TypecheckError, TypecheckResult},
    types::TypeDefValueKind,
};
use crate::{state::TypecheckState, types::EnumVariant};
use core::panic;
use hash_alloc::row;
use hash_alloc::{collections::row::Row, Wall};
use hash_ast::ast::{self, AccessName, BindingPattern};
use hash_ast::ident::Identifier;
use hash_ast::visitor::AstVisitor;
use hash_ast::{visitor, visitor::walk};
use hash_pipeline::sources::{SourceRef, Sources};
use hash_source::ModuleId;
use hash_source::{
    location::{Location, SourceLocation},
    SourceId,
};
use slotmap::Key;
use std::iter;
use std::mem;

pub struct SourceTypechecker<'c, 'w, 'g, 'src> {
    global_storage: &'g mut GlobalStorage<'c, 'w>,
    wall: &'w Wall<'c>,
    sources: &'src Sources<'c>,
    source_storage: SourceStorage,
    source_id: SourceId,
}

impl<'c, 'w, 'g, 'src> SourceTypechecker<'c, 'w, 'g, 'src> {
    pub fn new(
        source_id: SourceId,
        sources: &'src Sources<'c>,
        global_storage: &'g mut GlobalStorage<'c, 'w>,
        scopes: ScopeStack,
        wall: &'w Wall<'c>,
    ) -> Self {
        let source_storage = SourceStorage::new(source_id, scopes);
        Self {
            sources,
            global_storage,
            source_storage,
            wall,
            source_id,
        }
    }

    pub fn into_source_storage(self) -> SourceStorage {
        self.source_storage
    }

    pub fn wall(&self) -> &'w Wall<'c> {
        self.wall
    }

    pub fn some_source_location(&self, location: Location) -> Option<SourceLocation> {
        Some(self.source_location(location))
    }

    pub fn source_location(&self, location: Location) -> SourceLocation {
        SourceLocation {
            location,
            source_id: self.source_id,
        }
    }

    pub fn typecheck(&mut self) -> TypecheckResult<TypeId> {
        let ctx = self.wall();

        if let Some(ty_id) = self
            .global_storage
            .checked_sources
            .source_type_id(self.source_id)
        {
            Ok(ty_id)
        } else {
            match self.sources.get_source(self.source_id) {
                SourceRef::Interactive(interactive) => {
                    let result = self.visit_body_block(ctx, interactive.node())?;
                    self.global_storage
                        .checked_sources
                        .mark_checked(self.source_id, result);
                    Ok(result)
                }
                SourceRef::Module(module) => {
                    let result = self.visit_module(ctx, module.node())?;
                    self.global_storage
                        .checked_sources
                        .mark_checked(self.source_id, result);
                    Ok(result)
                }
            }
        }
    }

    fn create_type(&mut self, value: TypeValue<'c>, location: Option<SourceLocation>) -> TypeId {
        self.global_storage.types.create(value, location)
    }

    fn traits(&self) -> &TraitStorage<'c, 'w> {
        &self.global_storage.traits
    }

    fn _traits_mut(&mut self) -> &mut TraitStorage<'c, 'w> {
        &mut self.global_storage.traits
    }

    fn _trait_impls_mut(&mut self) -> &mut TraitImplStorage<'c, 'w> {
        &mut self.global_storage.trait_impls
    }

    fn trait_helper(&mut self) -> TraitHelper<'c, 'w, '_, '_> {
        TraitHelper::new(&mut self.source_storage, self.global_storage)
    }

    fn types(&self) -> &TypeStorage<'c, 'w> {
        &self.global_storage.types
    }

    fn types_mut(&mut self) -> &mut TypeStorage<'c, 'w> {
        &mut self.global_storage.types
    }

    fn type_defs(&self) -> &TypeDefStorage<'c, 'w> {
        &self.global_storage.type_defs
    }

    fn _type_defs_mut(&mut self) -> &mut TypeDefStorage<'c, 'w> {
        &mut self.global_storage.type_defs
    }

    fn _type_vars(&self) -> &TypeVars {
        &self.source_storage.type_vars
    }

    fn _type_vars_mut(&mut self) -> &mut TypeVars {
        &mut self.source_storage.type_vars
    }

    fn create_unknown_type(&mut self) -> TypeId {
        self.global_storage.types.create_unknown_type()
    }

    fn create_void_type(&mut self) -> TypeId {
        self.global_storage.types.create_void_type()
    }

    fn add_location_to_ty(&mut self, ty: TypeId, location: SourceLocation) {
        self.global_storage.types.add_location(ty, location)
    }

    fn create_tuple_type(&mut self, types: Row<'c, (Option<Identifier>, TypeId)>) -> TypeId {
        self.global_storage
            .types
            .create(TypeValue::Tuple(TupleType { types }), None)
    }

    fn create_str_type(&mut self, location: Option<SourceLocation>) -> TypeId {
        let str_def_id = self.core_type_defs().str;
        self.global_storage.types.create(
            TypeValue::User(UserType {
                def_id: str_def_id,
                args: row![self.wall()],
            }),
            location,
        )
    }

    fn create_list_type(&mut self, el_ty: TypeId) -> TypeId {
        let list_def_id = self.core_type_defs().list;
        self.global_storage.types.create(
            TypeValue::User(UserType {
                def_id: list_def_id,
                args: row![self.wall(); el_ty],
            }),
            None,
        )
    }

    fn create_set_type(&mut self, el_ty: TypeId) -> TypeId {
        let set_def_id = self.core_type_defs().set;
        self.global_storage.types.create(
            TypeValue::User(UserType {
                def_id: set_def_id,
                args: row![self.wall(); el_ty],
            }),
            None,
        )
    }

    fn create_map_type(&mut self, key_ty: TypeId, value_ty: TypeId) -> TypeId {
        let map_def_id = self.core_type_defs().map;
        self.global_storage.types.create(
            TypeValue::User(UserType {
                def_id: map_def_id,
                args: row![self.wall(); key_ty, value_ty],
            }),
            None,
        )
    }

    fn tc_state(&mut self) -> &mut TypecheckState {
        &mut self.source_storage.state
    }

    fn scopes(&mut self) -> &mut ScopeStack {
        &mut self.source_storage.scopes
    }

    fn core_type_defs(&mut self) -> &CoreTypeDefs {
        &self.global_storage.core_type_defs
    }

    fn unifier<'s>(&'s mut self) -> Unifier<'c, 'w, 's, 's> {
        Unifier::new(&mut self.source_storage, self.global_storage)
    }

    fn resolve_compound_symbol(
        &mut self,
        symbols: &AccessName<'_>,
    ) -> TypecheckResult<(Identifier, SymbolType)> {
        resolve_compound_symbol(
            &self.source_storage.scopes,
            &self.global_storage.types,
            symbols,
            self.source_id,
        )
    }
}

impl<'c, 'w, 'g, 'src> visitor::AstVisitor<'c> for SourceTypechecker<'c, 'w, 'g, 'src> {
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
        let import_module_id = self
            .sources
            .get_module_id_by_path(&node.resolved_path)
            .unwrap();
        let scope_stack = ScopeStack::new(self.global_storage);
        let mut inner_checker = SourceTypechecker::new(
            SourceId::Module(import_module_id),
            self.sources,
            self.global_storage,
            scope_stack,
            self.wall,
        );
        inner_checker.typecheck()
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
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::VariableExpr<'c>>,
    ) -> Result<Self::VariableExprRet, Self::Error> {
        let loc = self.source_location(node.location());

        match self.resolve_compound_symbol(&node.name)? {
            (_, SymbolType::Variable(var_ty_id)) => {
                if !node.type_args.is_empty() {
                    Err(TypecheckError::TypeArgumentLengthMismatch {
                        mismatch: ArgumentLengthMismatch::new(0, node.type_args.len()),
                        // It is not empty, as checked above.
                        location: self.some_source_location(node.type_args.location().unwrap()),
                    })
                } else {
                    Ok(var_ty_id)
                }
            }
            (_, SymbolType::Trait(var_trait_id)) => {
                self.visit_trait_variable(ctx, var_trait_id, node, None)
            }
            (ident, SymbolType::EnumVariant(ty_def_id)) => self
                .query_type_of_enum_variant(ty_def_id, ident, loc)
                .map(|(id, _)| id),
            _ => Err(TypecheckError::SymbolIsNotAVariable(Symbol::Compound {
                path: node.name.path(),
                location: Some(loc),
            })),
        }
    }

    type DirectiveExprRet = TypeId;
    fn visit_directive_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DirectiveExpr<'c>>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        // @@Future: At the moment, we're completely passing the 'directive' within the
        //          typechecking stage. This will change when we solidify how we want
        //          to type directives and then they become essentially indistinguishable
        //          from normal functions that perform operations on code.
        let walk::DirectiveExpr { subject, .. } = walk::walk_directive_expr(self, ctx, node)?;
        Ok(subject)
    }

    type FunctionCallArgsRet = Row<'c, (Option<Identifier>, TypeId)>;
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
        let given_args = self.visit_function_call_args(ctx, node.args.ast_ref())?;
        let return_ty = self.create_unknown_type();

        let args_ty_location = self.source_location(node.body().args.location());
        let expected_fn_ty = self.create_type(
            TypeValue::Fn(FnType {
                args: given_args,
                return_ty,
            }),
            Some(args_ty_location),
        );

        let given_ty = match node.subject.kind() {
            ast::ExpressionKind::Variable(var) => match self.resolve_compound_symbol(&var.name)? {
                (_, SymbolType::Trait(trait_id)) => self.visit_trait_variable(
                    ctx,
                    trait_id,
                    node.with_body(var),
                    Some(expected_fn_ty),
                )?,
                _ => walk::walk_function_call_expr(self, ctx, node)?.subject,
            },
            _ => walk::walk_function_call_expr(self, ctx, node)?.subject,
        };

        self.unifier()
            .unify(expected_fn_ty, given_ty, UnifyStrategy::ModifyBoth)?;

        Ok(return_ty)
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
                    TypeDefValueKind::Enum(EnumDef { .. }) => {
                        Err(TypecheckError::TypeIsNotStruct {
                            ty: subject,
                            ty_def_location: ty_def.location,
                            location: self.source_location(node.location()),
                        })
                    }
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
            ..
        } = walk::walk_ref_expr(self, ctx, node)?;

        let ty_location = self.source_location(node.location());
        Ok(self.create_type(
            TypeValue::Ref(RefType { inner: inner_ty }),
            Some(ty_location),
        ))
    }

    type DerefExprRet = TypeId;
    fn visit_deref_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DerefExpr<'c>>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let walk::DerefExpr(given_ref_ty) = walk::walk_deref_expr(self, ctx, node)?;

        let ref_location = self.source_location(node.location());

        let created_inner_ty = self.create_unknown_type();
        let created_ref_ty = self.create_type(
            TypeValue::Ref(RefType {
                inner: created_inner_ty,
            }),
            Some(ref_location),
        );
        self.unifier()
            .unify(created_ref_ty, given_ref_ty, UnifyStrategy::ModifyBoth)?;

        Ok(created_inner_ty)
    }

    type UnsafeExprRet = TypeId;
    fn visit_unsafe_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::UnsafeExpr<'c>>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let walk::UnsafeExpr(inner_ty) = walk::walk_unsafe_expr(self, ctx, node)?;

        // @@Incomplete: For now this does nothing but serve as a modifier on expressions. Later
        //               we will be able to define rules about what is and what isn't allowed in
        //               safe/unsafe blocks.
        Ok(inner_ty)
    }

    type LiteralExprRet = TypeId;
    fn visit_literal_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::LiteralExpr<'c>>,
    ) -> Result<Self::LiteralExprRet, Self::Error> {
        Ok(walk::walk_literal_expr(self, ctx, node)?.0)
    }

    type AsExprRet = TypeId;
    fn visit_as_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AsExpr<'c>>,
    ) -> Result<Self::AsExprRet, Self::Error> {
        let walk::AsExpr { expr, ty } = walk::walk_as_expr(self, ctx, node)?;
        self.unifier().unify(expr, ty, UnifyStrategy::ModifyBoth)?;
        Ok(expr)
    }

    type TypeExprRet = TypeId;

    fn visit_type_expr(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeExpr<'c>>,
    ) -> Result<Self::TypeExprRet, Self::Error> {
        let walk::TypeExpr(inner) = walk::walk_type_expr(self, ctx, node)?;

        Ok(inner)
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

    type TupleTypeRet = TypeId;
    fn visit_tuple_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TupleType<'c>>,
    ) -> Result<Self::TupleTypeRet, Self::Error> {
        let walk::TupleType { entries } = walk::walk_tuple_type(self, ctx, node)?;
        let ty_location = self.some_source_location(node.location());

        Ok(self
            .types_mut()
            .create(TypeValue::Tuple(TupleType { types: entries }), ty_location))
    }

    type ListTypeRet = TypeId;
    fn visit_list_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::ListType<'c>>,
    ) -> Result<Self::ListTypeRet, Self::Error> {
        todo!()
    }

    type SetTypeRet = TypeId;
    fn visit_set_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::SetType<'c>>,
    ) -> Result<Self::SetTypeRet, Self::Error> {
        todo!()
    }

    type MapTypeRet = TypeId;
    fn visit_map_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::MapType<'c>>,
    ) -> Result<Self::MapTypeRet, Self::Error> {
        todo!()
    }

    type FnTypeRet = TypeId;
    fn visit_function_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FnType<'c>>,
    ) -> Result<Self::TupleTypeRet, Self::Error> {
        let walk::FnType { args, return_ty } = walk::walk_function_type(self, ctx, node)?;

        Ok(self.create_type(
            TypeValue::Fn(FnType { args, return_ty }),
            self.some_source_location(node.location()),
        ))
    }

    type NamedFieldTypeRet = (Option<Identifier>, TypeId);

    fn visit_named_field_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamedFieldTypeEntry<'c>>,
    ) -> Result<Self::NamedFieldTypeRet, Self::Error> {
        let walk::NamedFieldTypeEntry { ty, .. } = walk::walk_named_field_type(self, ctx, node)?;

        Ok((node.name.as_ref().map(|t| t.ident), ty))
    }

    type TypeRet = TypeId;
    fn visit_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Type<'c>>,
    ) -> Result<Self::TypeRet, Self::Error> {
        let ty_id = walk::walk_type_same_children(self, ctx, node)?;
        // self.global_storage.types.add_location(ty_id, self.source_location(node.location()));
        Ok(ty_id)
    }

    type NamedTypeRet = TypeId;
    fn visit_named_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamedType<'c>>,
    ) -> Result<Self::NamedTypeRet, Self::Error> {
        let location = self.source_location(node.location());

        match self.resolve_compound_symbol(&node.name)? {
            (_, SymbolType::Type(ty_id)) => Ok(self.types_mut().duplicate(ty_id, Some(location))),
            (_, SymbolType::TypeDef(_)) => {
                let walk::NamedType { .. } = walk::walk_named_type(self, ctx, node)?;
                // let def = self.type_defs().get(def_id);

                todo!()
                // // @@Todo bounds
                // match &def.kind {
                //     TypeDefValueKind::Enum(EnumDef { generics, .. })
                //     | TypeDefValueKind::Struct(StructDef { generics, .. }) => {
                //         let args_sub = self.unifier().instantiate_vars_list(&generics.params)?;
                //         let instantiated_args = self
                //             .unifier()
                //             .apply_sub_to_list_make_vec(&args_sub, &generics.params)?;

                //         self.unifier().unify_pairs(
                //             type_args.iter().zip(instantiated_args.iter()),
                //             UnifyStrategy::ModifyTarget,
                //         )?;
                //         let ty = self.create_type(
                //             TypeValue::User(UserType {
                //                 def_id,
                //                 args: type_args,
                //             }),
                //             Some(location),
                //         );
                //         Ok(ty)
                //     }
                // }
            }
            _ => Err(TypecheckError::SymbolIsNotAType(Symbol::Compound {
                path: node.name.path(),
                location: Some(location),
            })),
        }
    }

    type TypeFunctionParamRet = TypeId;
    fn visit_type_function_param(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TypeFunctionParam<'c>>,
    ) -> Result<Self::TypeFunctionParamRet, Self::Error> {
        todo!()
    }

    type TypeFunctionRet = TypeId;
    fn visit_type_function(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TypeFunction<'c>>,
    ) -> Result<Self::TypeFunctionRet, Self::Error> {
        todo!()
    }

    type TypeFunctionCallRet = TypeId;
    fn visit_type_function_call(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TypeFunctionCall<'c>>,
    ) -> Result<Self::TypeFunctionCallRet, Self::Error> {
        todo!()
    }

    type RefTypeRet = TypeId;
    fn visit_ref_type(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::RefType<'c>>,
    ) -> Result<Self::RefTypeRet, Self::Error> {
        let walk::RefType { inner, .. } = walk::walk_ref_type(self, ctx, node)?;
        let ty_location = self.source_location(node.location());

        Ok(self.create_type(TypeValue::Ref(RefType { inner }), Some(ty_location)))
    }

    type MergedTypeRet = TypeId;
    fn visit_merged_type(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::MergedType<'c>>,
    ) -> Result<Self::MergedTypeRet, Self::Error> {
        todo!()
    }

    // type TypeVarRet = TypeId;
    // fn visit_type_var(
    //     &mut self,
    //     _ctx: &Self::Ctx,
    //     node: ast::AstNodeRef<ast::TypeVar<'c>>,
    // ) -> Result<Self::TypeVarRet, Self::Error> {
    //     let ty_location = self.some_source_location(node.location());
    //     let var = TypeVar {
    //         name: node.name.ident,
    //     };
    //     if self.tc_state().in_bound_def {
    //         Ok(self.create_type(TypeValue::Var(var), ty_location))
    //     } else {
    //         match self.source_storage.type_vars.find_type_var(var) {
    //             Some((_, TypeVarMode::Bound)) => {
    //                 Ok(self.create_type(TypeValue::Var(var), ty_location))
    //             }
    //             Some((_, TypeVarMode::Substitution(other_id))) => Ok(other_id),
    //             None => Err(TypecheckError::UnresolvedSymbol {
    //                 symbol: Symbol::Single {
    //                     symbol: var.name,
    //                     location: ty_location,
    //                 },
    //                 ancestor: None,
    //             }),
    //         }
    //     }
    // }

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
            .unify_many(entries.iter().copied(), UnifyStrategy::ModifyBoth)?;

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
            .unify_many(entries.iter().copied(), UnifyStrategy::ModifyBoth)?;

        Ok(self.create_set_type(el_ty))
    }

    type TupleLiteralEntryRet = (Option<Identifier>, TypeId);

    fn visit_tuple_literal_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TupleLiteralEntry<'c>>,
    ) -> Result<Self::TupleLiteralEntryRet, Self::Error> {
        todo!()
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
        node: ast::AstNodeRef<ast::StrLiteral>,
    ) -> Result<Self::StrLiteralRet, Self::Error> {
        let ty_location = self.source_location(node.location());

        Ok(self.create_str_type(Some(ty_location)))
    }

    type CharLiteralRet = TypeId;
    fn visit_char_literal(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::CharLiteral>,
    ) -> Result<Self::CharLiteralRet, Self::Error> {
        let ty_location = self.source_location(node.location());

        Ok(self.create_type(TypeValue::Prim(PrimType::Char), Some(ty_location)))
    }

    type FloatLiteralRet = TypeId;
    fn visit_float_literal(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FloatLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error> {
        let ty_location = self.source_location(node.location());

        Ok(self.create_type(TypeValue::Prim(PrimType::F32), Some(ty_location)))
    }

    type BoolLiteralRet = TypeId;
    fn visit_bool_literal(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BoolLiteral>,
    ) -> Result<Self::FloatLiteralRet, Self::Error> {
        let ty_location = self.source_location(node.location());

        Ok(self.create_type(TypeValue::Prim(PrimType::Bool), Some(ty_location)))
    }

    type IntLiteralRet = TypeId;
    fn visit_int_literal(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntLiteral>,
    ) -> Result<Self::IntLiteralRet, Self::Error> {
        let ty_location = self.source_location(node.location());

        Ok(self.create_type(TypeValue::Prim(PrimType::I32), Some(ty_location)))
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

        // Try to combine the entire span of the arguments and types
        let mut location = node.args.location().unwrap_or_else(|| node.location());

        if let Some(return_ty) = &node.return_ty {
            location = location.join(return_ty.location());
        }

        let location = self.source_location(location);

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
                    .unify(body_ty, return_ty, UnifyStrategy::ModifyBoth)?;
            }
        };

        let fn_ty = self.create_type(
            TypeValue::Fn(FnType {
                args: args_ty,
                return_ty,
            }),
            Some(location),
        ); // @@Correctness: this isn't the correct location

        Ok(fn_ty)
    }

    type FunctionDefArgRet = (Option<Identifier>, TypeId);
    fn visit_function_def_arg(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FunctionDefArg<'c>>,
    ) -> Result<Self::FunctionDefArgRet, Self::Error> {
        let ast::Name { ident } = node.name.body();
        let walk::FunctionDefArg { ty, default, .. } =
            walk::walk_function_def_arg(self, ctx, node)?;
        let arg_ty = ty.unwrap_or_else(|| self.create_unknown_type());

        // If a default value for the argument is defined, then we try to unify
        // with the type of the expression for the default argument with the
        // specified argument type (if any)
        if let Some(default_ty) = default {
            self.unifier()
                .unify(arg_ty, default_ty, UnifyStrategy::ModifyBoth)?;
        }

        self.scopes()
            .add_symbol(*ident, SymbolType::Variable(arg_ty));
        Ok((Some(*ident), arg_ty))
    }

    type BlockRet = TypeId;
    fn visit_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Block<'c>>,
    ) -> Result<Self::BlockRet, Self::Error> {
        walk::walk_block_same_children(self, ctx, node)
    }

    type MatchCaseRet = (TypeId, TypeId);
    fn visit_match_case(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MatchCase<'c>>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let walk::MatchCase { pattern, expr } = walk::walk_match_case(self, ctx, node)?;

        // we need to return both the type of the pattern and the type of the
        // expression so that we can verify everything matches...
        Ok((pattern, expr))
    }

    type MatchBlockRet = TypeId;
    fn visit_match_block(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::MatchBlock<'c>>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let walk::MatchBlock { subject, cases } = walk::walk_match_block(self, ctx, node)?;

        // we need to verify that for every case pattern, the type of the subject matches
        // the case...
        for (pat, _) in cases.iter() {
            self.unifier()
                .unify(subject, *pat, UnifyStrategy::CheckOnly)?;
        }

        // we need to verify that all of case branches also return the same type and then finally unify
        // and set the return type of the block as the return ty...
        let general_ty = self
            .unifier()
            .unify_many(cases.iter().map(|case| case.1), UnifyStrategy::ModifyBoth)?;

        Ok(general_ty)
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

        Ok(self.create_type(TypeValue::Prim(PrimType::Void), None))
    }

    type ModBlockRet = TypeId;

    fn visit_mod_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::ModBlock<'c>>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        todo!()
    }

    type ImplBlockRet = TypeId;
    fn visit_impl_block(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::ImplBlock<'c>>,
    ) -> Result<Self::ImplBlockRet, Self::Error> {
        todo!()
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
        Ok(expr.unwrap_or_else(|| self.create_type(TypeValue::Prim(PrimType::Void), None)))
        // @@TODO: use location of the last statement in the block
    }

    type ReturnStatementRet = TypeId;
    fn visit_return_statement(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ReturnStatement<'c>>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        match self.tc_state().func_ret_type {
            Some(ret) => {
                let given_ret = walk::walk_return_statement(self, ctx, node)?
                    .0
                    .unwrap_or_else(|| self.create_type(TypeValue::Prim(PrimType::Void), None));

                self.unifier()
                    .unify(ret, given_ret, UnifyStrategy::ModifyBoth)?;
                self.tc_state().ret_once = true;

                Ok(ret)
            }
            None => Err(TypecheckError::UsingReturnOutsideFunction(
                self.source_location(node.location()),
            )),
        }
    }

    type BreakStatementRet = TypeId;
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
            Ok(self.types_mut().create_void_type())
        }
    }

    type ContinueStatementRet = TypeId;
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
            Ok(self.types_mut().create_void_type())
        }
    }

    type VisibilityRet = ();
    fn visit_visibility_modifier(
        &mut self,
        _: &Self::Ctx,
        _: ast::AstNodeRef<ast::Visibility>,
    ) -> Result<Self::VisibilityRet, Self::Error> {
        todo!()
    }

    type MutabilityRet = ();
    fn visit_mutability_modifier(
        &mut self,
        _: &Self::Ctx,
        _: ast::AstNodeRef<ast::Mutability>,
    ) -> Result<Self::MutabilityRet, Self::Error> {
        todo!()
    }

    type DeclarationRet = TypeId;
    fn visit_declaration(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Declaration<'c>>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        // Ensure that the given pattern for the declaration is irrefutable
        if !is_pattern_irrefutable(node.pattern.body()) {
            let location = self.source_location(node.pattern.location());
            return Err(TypecheckError::RequiresIrrefutablePattern(location));
        }

        // @@Todo: bounds
        let annotation_ty = node
            .ty
            .as_ref()
            .map(|t| self.visit_type(ctx, t.ast_ref()))
            .transpose()?
            .unwrap_or_else(|| self.create_unknown_type());

        let value_ty = node
            .value
            .as_ref()
            .map(|t| self.visit_expression(ctx, t.ast_ref()))
            .transpose()?
            .unwrap_or_else(|| self.create_unknown_type());

        // add type location information on  pattern_ty and annotation_ty
        if let Some(annotation) = &node.body().ty {
            let location = self.source_location(annotation.location());
            self.add_location_to_ty(annotation_ty, location);
        }

        self.unifier()
            .unify(annotation_ty, value_ty, UnifyStrategy::ModifyBoth)?;

        self.tc_state().pattern_hint = Some(value_ty);
        let pattern_ty = self.visit_pattern(ctx, node.pattern.ast_ref())?;
        self.tc_state().pattern_hint = None;

        let pattern_location = self.source_location(node.body().pattern.location());
        self.add_location_to_ty(pattern_ty, pattern_location);

        self.unifier()
            .unify(value_ty, pattern_ty, UnifyStrategy::ModifyBoth)?;

        Ok(self.create_void_type())
    }

    type MergeDeclarationRet = TypeId;

    fn visit_merge_declaration(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::MergeDeclaration<'c>>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        todo!()
    }

    type AssignExpressionRet = TypeId;

    fn visit_assign_expression(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::AssignExpression<'c>>,
    ) -> Result<Self::AssignExpressionRet, Self::Error> {
        let walk::AssignStatement { lhs, rhs } = walk::walk_assign_statement(self, ctx, node)?;

        // @@Correctness: we should use the location of the definition instead of the most
        //                recent assignment.

        // Ensure the the expression on the right hand side matches the type
        // that was found found for the left hand side
        self.unifier().unify(rhs, lhs, UnifyStrategy::CheckOnly)?;
        Ok(self.types_mut().create_void_type())
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

    type StructDefRet = TypeId;
    fn visit_struct_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::StructDef<'c>>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        todo!()
    }

    type EnumDefEntryRet = EnumVariant<'c>;
    fn visit_enum_def_entry(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::EnumDefEntry<'c>>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        let walk::EnumDefEntry { args: data, .. } = walk::walk_enum_def_entry(self, ctx, node)?;

        Ok(EnumVariant {
            name: node.name.ident,
            data,
            location: self.source_location(node.name.location()),
        })
    }

    type EnumDefRet = TypeId;
    fn visit_enum_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::EnumDef<'c>>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        todo!()
    }

    type TraitDefRet = TypeId;
    fn visit_trait_def(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TraitDef<'c>>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        // let bound = self.visit_bound(ctx, node.bound.ast_ref())?;
        // let type_var_bound =
        //     self.type_var_only_bound(&bound, self.source_location(node.bound.location()))?;
        // let scope_key = self
        //     .type_vars_mut()
        //     .enter_bounded_type_var_scope(type_var_bound.iter().copied());
        // let fn_type = self.visit_type(ctx, node.trait_type.ast_ref())?;
        // self.type_vars_mut().exit_type_var_scope(scope_key);

        // // @@Todo trait bounds
        // let trait_id = self
        //     .traits_mut()
        //     .create(bound, TraitBounds::empty(), fn_type);
        // self.scopes()
        //     .add_symbol(node.name.ident, SymbolType::Trait(trait_id));

        Ok(self.types_mut().create_void_type())
    }

    type TraitImplRet = TypeId;

    fn visit_trait_impl(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TraitImpl<'c>>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
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

    // type TraitBoundRet = (TraitId, Vec<TypeId>);
    // fn visit_trait_bound(
    //     &mut self,
    //     ctx: &Self::Ctx,
    //     node: ast::AstNodeRef<ast::TraitBound<'c>>,
    // ) -> Result<Self::TraitBoundRet, Self::Error> {
    // let name_loc = self.source_location(node.name.location());

    // match self.resolve_compound_symbol(&node.name)? {
    //     (_, SymbolType::Trait(trait_id)) => {
    //         let type_args: Vec<_> = node
    //             .type_args
    //             .iter()
    //             .map(|arg| self.visit_type(ctx, arg.ast_ref()))
    //             .collect::<Result<_, _>>()?;
    //         Ok((trait_id, type_args))
    //     }
    //     _ => Err(TypecheckError::SymbolIsNotATrait(Symbol::Compound {
    //         path: node.name.path(),
    //         location: Some(name_loc),
    //     })),
    // }
    // }

    type TypeFunctionDefRet = TypeId;
    fn visit_type_function_def(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TypeFunctionDef<'c>>,
    ) -> Result<Self::TypeFunctionDefRet, Self::Error> {
        self.tc_state().in_bound_def = true;
        let walk::TypeFunctionDef {
            args: _,
            return_ty: _,
            expression,
        } = walk::walk_type_function_def(self, ctx, node)?;
        self.tc_state().in_bound_def = false;

        // @@Todo: bounds
        Ok(expression)
    }

    type TypeFunctionDefArgRet = TypeId;
    fn visit_type_function_def_arg(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TypeFunctionDefArg<'c>>,
    ) -> Result<Self::TypeFunctionDefArgRet, Self::Error> {
        todo!()
    }

    type ConstructorPatternRet = TypeId;
    fn visit_constructor_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ConstructorPattern<'c>>,
    ) -> Result<Self::ConstructorPatternRet, Self::Error> {
        let walk::ConstructorPattern { name: _, args } =
            walk::walk_constructor_pattern(self, ctx, node)?;

        let location = self.source_location(node.location());

        let variant_data_mismatches = |ident, ty_def_location, wanted, given| {
            Err(TypecheckError::EnumVariantArgumentsMismatch {
                variant_name: ident,
                location,
                ty_def_name: ident,
                ty_def_location,
                mismatch: ArgumentLengthMismatch::new(wanted, given),
            })
        };

        match self.resolve_compound_symbol(&node.name)? {
            (ident, SymbolType::EnumVariant(ty_def_id)) => {
                let (variant_id, variant_location) =
                    self.query_type_of_enum_variant(ty_def_id, ident, location)?;
                let variant_type = self.types().get(variant_id);

                // if the variant itself has no arguments and the definition expects no arguments...
                // we don't need to do anything and can just exit early, otherwise we need to unify with
                // the resultant arguments produced from the query...
                match variant_type {
                    TypeValue::Fn(FnType {
                        args: expected,
                        return_ty,
                    }) => {
                        self.unifier().unify_pairs(
                            args.iter()
                                .map(|(_, ty)| ty)
                                .zip(expected.iter().map(|(_, ty)| ty)),
                            UnifyStrategy::CheckOnly,
                        )?;

                        if expected.len() != args.len() {
                            return variant_data_mismatches(
                                ident,
                                Some(variant_location),
                                expected.len(),
                                args.len(),
                            );
                        }

                        Ok(*return_ty)
                    }
                    _ => {
                        if !args.is_empty() {
                            return variant_data_mismatches(
                                ident,
                                Some(variant_location),
                                0,
                                args.len(),
                            );
                        }

                        Ok(variant_id)
                    }
                }
            }
            _ => Err(TypecheckError::SymbolIsNotAEnum(Symbol::Compound {
                path: node.name.path(),
                location: Some(location),
            })),
        }
    }

    // type StructPatternRet = TypeId;
    // fn visit_struct_pattern(
    //     &mut self,
    //     ctx: &Self::Ctx,
    //     node: ast::AstNodeRef<ast::StructPattern<'c>>,
    // ) -> Result<Self::StructPatternRet, Self::Error> {
    //     let location = self.source_location(node.location());

    //     let symbol_res = self.resolve_compound_symbol(&node.name)?;

    //     match symbol_res {
    //         (_, SymbolType::TypeDef(def_id)) => {
    //             let type_def = self.type_defs().get(def_id);
    //             let (ty_id, _) = self.instantiate_type_def_unknown_args(def_id)?;

    //             match &type_def.kind {
    //                 TypeDefValueKind::Struct(struct_def) => self.typecheck_known_struct_pattern(
    //                     ctx,
    //                     node,
    //                     ty_id,
    //                     struct_def,
    //                     type_def.location,
    //                 ),
    //                 _ => Err(TypecheckError::TypeIsNotStruct {
    //                     ty: ty_id,
    //                     location,
    //                     ty_def_location: type_def.location,
    //                 }),
    //             }
    //         }
    //         (_, SymbolType::Type(ty_id)) => {
    //             let ty = self.types().get(ty_id);

    //             match ty {
    //                 TypeValue::User(UserType { def_id, .. }) => {
    //                     let type_def = self.type_defs().get(*def_id);

    //                     match &type_def.kind {
    //                         TypeDefValueKind::Struct(struct_def) => self
    //                             .typecheck_known_struct_pattern(
    //                                 ctx,
    //                                 node,
    //                                 ty_id,
    //                                 struct_def,
    //                                 type_def.location,
    //                             ),
    //                         _ => Err(TypecheckError::TypeIsNotStruct {
    //                             ty: ty_id,
    //                             location,
    //                             ty_def_location: type_def.location,
    //                         }),
    //                     }
    //                 }
    //                 _ => Err(TypecheckError::TypeIsNotStruct {
    //                     ty: ty_id,
    //                     location,
    //                     ty_def_location: None,
    //                 }),
    //             }
    //         }
    //         _ => Err(TypecheckError::SymbolIsNotAType(Symbol::Compound {
    //             path: node.name.path(),
    //             location: Some(location),
    //         })),
    //     }
    // }

    type NamespacePatternRet = TypeId;
    fn visit_namespace_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::NamespacePattern<'c>>,
    ) -> Result<Self::NamespacePatternRet, Self::Error> {
        let location = self.source_location(node.location());

        let pattern_ty = self.create_unknown_type();
        self.add_location_to_ty(pattern_ty, location);

        let subject_ty = self
            .tc_state()
            .pattern_hint
            .unwrap_or_else(|| self.create_unknown_type());
        self.unifier()
            .unify(pattern_ty, subject_ty, UnifyStrategy::ModifyTarget)?;

        match self.types().get(pattern_ty) {
            TypeValue::Namespace(NamespaceType { members, .. }) => {
                // Here we do not use self.visit_destructuring_pattern because namespace patterns
                // support types and traits in addition to variables, whereas the implementation
                // for self.visit_destructuring_pattern does not.
                for field in node.fields.iter() {
                    let location = self.source_location(field.location());
                    match members.resolve_symbol(field.name.ident) {
                        // Only variables are allowed actual pattern destructuring
                        Some(SymbolType::Variable(variable_type_id)) => {
                            let ty = self.visit_pattern(ctx, field.pattern.ast_ref())?;
                            self.unifier().unify(
                                ty,
                                variable_type_id,
                                UnifyStrategy::ModifyTarget,
                            )?;
                        }
                        // Everything else better be just a binding
                        Some(symbol_type) => match field.pattern.body() {
                            ast::Pattern::Binding(BindingPattern { name, .. }) => {
                                self.scopes().add_symbol(name.ident, symbol_type);
                            }
                            _ => {
                                return Err(TypecheckError::DisallowedPatternNonVariable(
                                    Symbol::Single {
                                        symbol: field.name.ident,
                                        location: Some(location),
                                    },
                                    self.source_location(field.pattern.location()),
                                ))
                            }
                        },
                        None => {
                            return Err(TypecheckError::UnresolvedSymbol {
                                symbol: Symbol::Single {
                                    symbol: field.name.ident,
                                    location: Some(location),
                                },
                                ancestor: None,
                            })
                        }
                    }
                }

                Ok(pattern_ty)
            }
            TypeValue::Unknown(_) => Err(TypecheckError::UnresolvedType(pattern_ty)),
            _ => {
                let dummy_namespace_ty = self.create_type(
                    TypeValue::Namespace(NamespaceType {
                        module_id: ModuleId::null(),
                        members: ScopeStack::empty(),
                    }),
                    Some(location),
                );
                Err(TypecheckError::TypeMismatch {
                    given: subject_ty,
                    wanted: dummy_namespace_ty,
                })
            }
        }
    }

    type TuplePatternEntryRet = (Option<Identifier>, TypeId);

    fn visit_tuple_pattern_entry(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::TuplePatternEntry<'c>>,
    ) -> Result<Self::TuplePatternEntryRet, Self::Error> {
        todo!()
    }

    type TuplePatternRet = TypeId;
    fn visit_tuple_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::TuplePattern<'c>>,
    ) -> Result<Self::TuplePatternRet, Self::Error> {
        let walk::TuplePattern { elements } = walk::walk_tuple_pattern(self, ctx, node)?;

        Ok(self.create_tuple_type(elements))
    }

    type ListPatternRet = TypeId;
    fn visit_list_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::ListPattern<'c>>,
    ) -> Result<Self::ListPatternRet, Self::Error> {
        let walk::ListPattern { elements } = walk::walk_list_pattern(self, ctx, node)?;

        let el_ty = self
            .unifier()
            .unify_many(elements.iter().copied(), UnifyStrategy::ModifyBoth)?;

        Ok(self.create_list_type(el_ty))
    }

    type StrLiteralPatternRet = TypeId;
    fn visit_str_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::StrLiteralPattern>,
    ) -> Result<Self::StrLiteralPatternRet, Self::Error> {
        let ty_location = self.source_location(node.location());

        Ok(self.create_str_type(Some(ty_location)))
    }

    type CharLiteralPatternRet = TypeId;
    fn visit_char_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::CharLiteralPattern>,
    ) -> Result<Self::CharLiteralPatternRet, Self::Error> {
        let ty_location = self.source_location(node.location());
        Ok(self.create_type(TypeValue::Prim(PrimType::Char), Some(ty_location)))
    }

    type IntLiteralPatternRet = TypeId;
    fn visit_int_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::IntLiteralPattern>,
    ) -> Result<Self::IntLiteralPatternRet, Self::Error> {
        let ty_location = self.source_location(node.location());

        Ok(self.create_type(TypeValue::Prim(PrimType::I32), Some(ty_location)))
    }

    type FloatLiteralPatternRet = TypeId;
    fn visit_float_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::FloatLiteralPattern>,
    ) -> Result<Self::FloatLiteralPatternRet, Self::Error> {
        let ty_location = self.source_location(node.location());

        Ok(self.create_type(TypeValue::Prim(PrimType::F32), Some(ty_location)))
    }

    type BoolLiteralPatternRet = TypeId;
    fn visit_bool_literal_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::BoolLiteralPattern>,
    ) -> Result<Self::BoolLiteralRet, Self::Error> {
        let ty_location = self.source_location(node.location());

        Ok(self.create_type(TypeValue::Prim(PrimType::Bool), Some(ty_location)))
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
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::OrPattern<'c>>,
    ) -> Result<Self::OrPatternRet, Self::Error> {
        let entries = node
            .variants
            .iter()
            .map(|el| self.visit_pattern(ctx, el.ast_ref()))
            .collect::<Result<Vec<_>, _>>()?;

        // The type should unify to a single type as the or patterns follow the rule that they don't have differing types...
        let general_ty = self
            .unifier()
            .unify_many(entries.iter().copied(), UnifyStrategy::ModifyBoth)?;

        Ok(general_ty)
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
        let location = self.source_location(node.location());

        // we need to resolve the symbol in the current scope and firstly check if it's
        // an enum...
        let ident = node.name.ident;

        match self.scopes().resolve_symbol(ident) {
            Some(SymbolType::EnumVariant(ty_def_id)) => {
                let (variant_id, variant_location) =
                    self.query_type_of_enum_variant(ty_def_id, ident, location)?;

                // This means that the variants mis-match...
                if let TypeValue::Fn(FnType { args, .. }) = self.types().get(variant_id) {
                    return Err(TypecheckError::EnumVariantArgumentsMismatch {
                        variant_name: ident,
                        location,
                        ty_def_name: ident,
                        ty_def_location: Some(variant_location),
                        mismatch: ArgumentLengthMismatch::new(0, args.len()),
                    });
                };

                Ok(variant_id)
            }
            _ => {
                let variable_ty = self.create_unknown_type();

                // @@Correctness, should we add the node into scope if the variable ident is equal to '_' ignore?
                self.scopes()
                    .add_symbol(node.name.ident, SymbolType::Variable(variable_ty));
                Ok(variable_ty)
            }
        }
    }

    type SpreadPatternRet = TypeId;
    fn visit_spread_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::SpreadPattern<'c>>,
    ) -> Result<Self::SpreadPatternRet, Self::Error> {
        todo!()
    }

    type IgnorePatternRet = TypeId;
    fn visit_ignore_pattern(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::IgnorePattern>,
    ) -> Result<Self::IgnorePatternRet, Self::Error> {
        Ok(self.create_unknown_type())
    }

    type DestructuringPatternRet = (Identifier, TypeId, SourceLocation);
    fn visit_destructuring_pattern(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::DestructuringPattern<'c>>,
    ) -> Result<Self::DestructuringPatternRet, Self::Error> {
        let walk::DestructuringPattern {
            name: _,
            pattern: pattern_ty,
        } = walk::walk_destructuring_pattern(self, ctx, node)?;
        let ident = node.name.ident;

        Ok((
            ident,
            pattern_ty,
            self.source_location(node.name.location()),
        ))
    }

    type ModuleRet = TypeId;
    fn visit_module(
        &mut self,
        ctx: &Self::Ctx,
        node: ast::AstNodeRef<ast::Module<'c>>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let walk::Module { contents: _ } = walk::walk_module(self, ctx, node)?;

        let curr_scope = self.scopes().extract_current_scope();
        let members = ScopeStack::with_scopes(self.global_storage, iter::once(curr_scope));

        let namespace_ty = match self.source_id {
            SourceId::Interactive(_) => {
                panic!("Unexpected interactive SourceId when traversing module");
            }
            SourceId::Module(module_id) => self.create_type(
                TypeValue::Namespace(NamespaceType { members, module_id }),
                None,
            ),
        };

        Ok(namespace_ty)
    }

    type FunctionCallArgRet = (Option<Identifier>, TypeId);

    fn visit_function_call_arg(
        &mut self,
        _ctx: &Self::Ctx,
        _node: ast::AstNodeRef<ast::FunctionCallArg<'c>>,
    ) -> Result<Self::FunctionCallArgRet, Self::Error> {
        todo!()
    }
}

impl<'c, 'w, 'g, 'src> SourceTypechecker<'c, 'w, 'g, 'src> {
    // fn typecheck_known_struct_literal(
    //     &mut self,
    //     ctx: &<Self as AstVisitor<'c>>::Ctx,
    //     node: ast::AstNodeRef<ast::StructLiteral<'c>>,
    //     ty_id: TypeId,
    //     StructDef {
    //         name,
    //         fields,
    //         generics: _,
    //     }: &StructDef,
    //     ty_def_location: Option<SourceLocation>,
    // ) -> TypecheckResult<TypeId> {
    //     let walk::StructLiteral {
    //         name: _,
    //         entries,
    //         type_args: _,
    //     } = walk::walk_struct_literal(self, ctx, node)?;

    //     // Make sure all fields are present
    //     let entries_given: HashSet<_> = entries.iter().map(|&(entry_name, _)| entry_name).collect();

    //     // @@Reporting: we could report multiple missing fields here...
    //     for (expected, _) in fields.iter() {
    //         if !entries_given.contains(&expected) {
    //             let name_node = &node.body().name;
    //             let location = self.source_location(name_node.location());

    //             return Err(TypecheckError::MissingStructField {
    //                 ty_def_location,
    //                 ty_def_name: *name,
    //                 field_name: expected,
    //                 location,
    //             });
    //         }
    //     }

    //     // Unify args
    //     for (index, &(entry_name, entry_ty)) in (&entries).iter().enumerate() {
    //         match fields.get_field(entry_name) {
    //             Some(field_ty) => {
    //                 self.unifier()
    //                     .unify(entry_ty, field_ty, UnifyStrategy::ModifyTarget)?
    //             }
    //             None => {
    //                 let entry = node.entries.get(index).unwrap();

    //                 return Err(TypecheckError::UnresolvedStructField {
    //                     ty_def: Symbol::Single {
    //                         symbol: *name,
    //                         location: ty_def_location,
    //                     },
    //                     field: Symbol::Single {
    //                         symbol: entry_name,
    //                         location: self.some_source_location(entry.location()),
    //                     },
    //                 });
    //             }
    //         }
    //     }

    //     Ok(ty_id)
    // }

    // fn typecheck_known_struct_pattern(
    //     &mut self,
    //     ctx: &<Self as AstVisitor<'c>>::Ctx,
    //     node: ast::AstNodeRef<ast::StructPattern<'c>>,
    //     ty_id: TypeId,
    //     StructDef {
    //         name,
    //         fields,
    //         generics: _,
    //     }: &StructDef,
    //     ty_def_location: Option<SourceLocation>,
    // ) -> TypecheckResult<TypeId> {
    //     let walk::StructPattern { name: _, entries } = walk::walk_struct_pattern(self, ctx, node)?;

    //     // @@Cleanup: until we don't introduce a some kind of ignore spread operator
    //     //            that can be used for structs, we essentially implicitly treat as fields
    //     //            that aren't specified in the pattern as being ignored.
    //     //
    //     //            This can be done by de-sugaring the ast into assigning all missing fields of a
    //     //            a struct assigned to an ignore pattern. This current implementation doesn't do
    //     //            that at the moment.
    //     // let entries_given: HashSet<_> = entries.iter().map(|&(entry_name, _)| entry_name).collect();

    //     // Unify args
    //     for &(entry_name, entry_ty, location) in entries.iter() {
    //         match fields.get_field(entry_name) {
    //             Some(field_ty) => {
    //                 self.unifier()
    //                     .unify(entry_ty, field_ty, UnifyStrategy::ModifyTarget)?
    //             }
    //             None => {
    //                 return Err(TypecheckError::UnresolvedStructField {
    //                     ty_def: Symbol::Single {
    //                         symbol: *name,
    //                         location: ty_def_location,
    //                     },
    //                     field: Symbol::Single {
    //                         symbol: entry_name,
    //                         location: Some(location),
    //                     },
    //                 });
    //             }
    //         }
    //     }

    //     // Add all entries to scope
    //     for (ident, type_id, _) in &entries {
    //         self.scopes()
    //             .add_symbol(*ident, SymbolType::Variable(*type_id));
    //     }

    //     Ok(ty_id)
    // }

    fn query_type_of_enum_variant(
        &mut self,
        ty_def_id: TypeDefId,
        ident: Identifier,
        location: SourceLocation,
    ) -> TypecheckResult<(TypeId, SourceLocation)> {
        let ty_def = self.type_defs().get(ty_def_id);

        match &ty_def.kind {
            TypeDefValueKind::Enum(EnumDef {
                variants, generics, ..
            }) => {
                // here we need to find the variant in variants by the node name
                let variant = variants.get_variant(ident).unwrap();
                let sub = self.unifier().instantiate_vars_list(&generics.params)?;

                let enum_ty_args = self
                    .unifier()
                    .apply_sub_to_list_make_row(&sub, &generics.params)?;

                let enum_ty_id = self.types_mut().create(
                    TypeValue::User(UserType {
                        def_id: ty_def_id,
                        args: enum_ty_args,
                    }),
                    Some(location),
                );

                if variant.data.is_empty() {
                    return Ok((enum_ty_id, variant.location));
                };

                let args = self.unifier().apply_sub_to_arg_list_make_row(
                    &sub,
                    variant
                        .data
                        .iter()
                        .map(|ty| (None, *ty))
                        .collect::<Vec<_>>()
                        .as_slice(),
                )?;

                let enum_variant_fn_ty = self.types_mut().create(
                    TypeValue::Fn(FnType {
                        args,
                        return_ty: enum_ty_id,
                    }),
                    Some(location),
                );

                Ok((enum_variant_fn_ty, variant.location))
            }
            TypeDefValueKind::Struct(_) => unreachable!(),
        }
    }

    /// Returns a substitution for the type arguments as well.
    fn _instantiate_type_def_unknown_args(
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
        let instantiated_vars = unifier.apply_sub_to_list_make_row(&vars_sub, &generics.params)?;
        let ty_id = self.create_type(
            TypeValue::User(UserType {
                def_id,
                args: instantiated_vars,
            }),
            None,
        );

        Ok((ty_id, vars_sub))
    }

    fn _type_var_only_bound(
        &self,
        bound: &[TypeId],
        bound_location: SourceLocation,
    ) -> TypecheckResult<Vec<TypeVar>> {
        bound
            .iter()
            .map(|ty_id| match self.types().get(*ty_id) {
                TypeValue::Var(var) => Ok(*var),
                _ => Err(TypecheckError::BoundRequiresStrictlyTypeVars(
                    bound_location,
                )),
            })
            .collect()
    }

    fn visit_trait_variable(
        &mut self,
        ctx: &<Self as AstVisitor<'c>>::Ctx,
        trait_id: TraitId,
        node: ast::AstNodeRef<ast::VariableExpr<'c>>,
        fn_type: Option<TypeId>,
    ) -> TypecheckResult<TypeId> {
        let trt = self.traits().get(trait_id);
        let args: Vec<_> = node
            .type_args
            .iter()
            .map(|a| self.visit_named_field_type(ctx, a.ast_ref()))
            .collect::<Result<_, _>>()?;
        let trt_name_location = self.some_source_location(node.name.location());
        let trt_symbol = || Symbol::Compound {
            location: trt_name_location,
            path: node.name.path(),
        };
        let type_args_location = node.type_args.location().map(|l| self.source_location(l));
        let MatchTraitImplResult {
            sub_from_trait_def, ..
        } = self.trait_helper().find_trait_impl(
            trt,
            &args.iter().map(|ty| ty.1).collect::<Vec<_>>(),
            fn_type,
            trt_symbol,
            type_args_location,
        )?;

        self.unifier().apply_sub(&sub_from_trait_def, trt.fn_type)
    }
}
