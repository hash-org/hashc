use std::collections::HashMap;

use derive_more::From;
use hash_ast::{ast, ast_visitor_mut_self_default_impl, visitor::walk_mut_self};
use hash_source::identifier::Identifier;
use hash_types::new::{
    data::DataDefId,
    defs::DefMemberData,
    environment::{
        context::{Binding, Context, ScopeKind},
        env::AccessToEnv,
    },
    mods::{ModDefId, ModKind},
    scopes::StackId,
    symbols::Symbol,
    terms::TermId,
    trts::TrtDefId,
};

use crate::{
    diagnostics::error::TcError,
    impl_access_to_tc_env,
    new::{
        environment::tc_env::TcEnv,
        ops::{common::CommonOps, AccessToOps},
    },
};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
enum DefId {
    Mod(ModDefId),
    Trt(TrtDefId),
    Data(DataDefId),
    Stack(StackId),
}

pub struct DefMemberFound<'env> {
    pub data: DefMemberData,
    pub origin: ast::AstNodeRef<'env, ast::Declaration>,
}

pub struct ScopeDiscoveryPass<'env> {
    tc_env: &'env TcEnv<'env>,
    name_hint: Option<Symbol>,
    ast_ids_to_term_ids: HashMap<ast::AstNodeId, TermId>,
    def_members_found: HashMap<DefId, Vec<DefMemberFound<'env>>>,
    _ast_ids_to_bindings: HashMap<ast::AstNodeId, Binding>,
}

impl<'env> ScopeDiscoveryPass<'env> {
    pub fn new(tc_env: &'env TcEnv<'env>) -> Self {
        Self {
            tc_env,
            name_hint: None,
            ast_ids_to_term_ids: HashMap::new(),
            def_members_found: HashMap::new(),
            _ast_ids_to_bindings: HashMap::new(),
        }
    }

    fn with_name_hint<T>(&mut self, name_hint: Symbol, mut f: impl FnMut(&mut Self) -> T) -> T {
        self.name_hint = Some(name_hint);
        let result = f(self);
        self.name_hint = None;
        result
    }

    fn _add_def_member(
        &mut self,
        def_id: impl Into<DefId>,
        member: DefMemberData,
        origin: ast::AstNodeRef<'env, ast::Declaration>,
    ) {
        self.def_members_found
            .entry(def_id.into())
            .or_default()
            .push(DefMemberFound { data: member, origin });
    }

    fn get_def_members(&self, def_id: impl Into<DefId>) -> &[DefMemberFound] {
        self.def_members_found.get(&def_id.into()).map(|x| x.as_slice()).unwrap_or(&[])
    }

    fn store_found_def_members(&mut self, def_id: impl Into<DefId> + Copy) {
        let members = self.get_def_members(def_id);
        match def_id.into() {
            DefId::Mod(mod_def_id) => {
                let members_stored =
                    self.mod_ops().create_mod_members(members.iter().map(|members| members.data));
                self.mod_ops().set_mod_def_members(mod_def_id, members_stored);
            }
            DefId::Trt(trt_def_id) => {
                let members_stored =
                    self.trt_ops().create_trt_members(members.iter().map(|members| members.data));
                self.trt_ops().set_trt_def_members(trt_def_id, members_stored);
            }
            DefId::Data(data_def_id) => {
                let members_stored = self.data_ops().create_data_ctors_from_members(
                    data_def_id,
                    members.iter().map(|members| members.data),
                );
                self.data_ops().set_data_def_ctors(data_def_id, members_stored);
            }
            DefId::Stack(stack_id) => {
                let members_stored = self.stack_ops().create_stack_members_from_def_members(
                    stack_id,
                    members.iter().map(|members| {
                        // @@Todo: Here we also have to provide mutability information for the
                        // stack members
                        (false, members.data)
                    }),
                );
                self.stack_ops().set_stack_members(stack_id, members_stored);
            }
        }
    }

    fn take_name_hint_or_create_internal_name(&mut self) -> Symbol {
        self.name_hint.take().unwrap_or_else(|| self.builder().create_internal_symbol())
    }

    /// If the given `expr` is a definition, get its set value from
    /// `ast_ids_to_term_ids`. Otherwise, return `None`
    fn get_value_term_of_def(&mut self, expr: ast::AstNodeRef<ast::Expr>) -> Option<TermId> {
        let get_term_from_ast_node_id = |node_id: ast::AstNodeId| {
            self.ast_ids_to_term_ids
                .get(&node_id)
                .copied()
                .unwrap_or_else(|| unreachable!("found definition without set value"))
        };

        match expr.body() {
            ast::Expr::Block(block) => match block.data.body() {
                ast::Block::Mod(_) | ast::Block::Impl(_) => {
                    Some(get_term_from_ast_node_id(block.data.id()))
                }
                _ => None,
            },
            ast::Expr::StructDef(_)
            | ast::Expr::EnumDef(_)
            | ast::Expr::TraitDef(_)
            | ast::Expr::FnDef(_)
            | ast::Expr::TraitImpl(_) => Some(get_term_from_ast_node_id(expr.id())),
            _ => None,
        }
    }
}

impl_access_to_tc_env!(ScopeDiscoveryPass<'env>);

impl<'env> ast::AstVisitorMutSelf for ScopeDiscoveryPass<'env> {
    type Error = TcError;
    ast_visitor_mut_self_default_impl!(hiding: Declaration, Module, ModBlock);

    type DeclarationRet = ();
    fn visit_declaration(
        &mut self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let make_def_member = |this: &mut Self| {
            let name = match node.pat.body() {
                ast::Pat::Binding(binding) => this.builder().create_symbol(binding.name.ident),
                _ => unreachable!("non-named declaration patterns in constant scopes found after pre-tc semantics"),
            };
            // With the member's name hint, walk the value.
            //
            // If the declaration is in the form `x := mod/trait/struct/enum/impl ...`, then
            // it will use this name hint to declare it.
            this.with_name_hint(name, |this| walk_mut_self::walk_declaration(this, node))?;

            // Get the created value of this term
            let value =
                node.value.as_ref().and_then(|value| this.get_value_term_of_def(value.ast_ref()));

            // Infer the type of the value
            //
            // This will be a hole unless the value is a definition.
            let ty = value
                .and_then(|value| this.infer_ops().infer_ty_of_term(value))
                .unwrap_or_else(|| this.new_ty_hole());

            Ok(DefMemberData { name, ty, value })
        };

        let _member = make_def_member(self)?;
        // self.add_def_member(def_id, member, node.ast_ref());
        todo!()
    }

    type ModuleRet = ();
    fn visit_module(
        &mut self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let source_id = self.current_source_info().source_id;
        let module_name: Identifier = self.source_map().source_name(source_id).into();

        // Create a module definition, with empty members for now.
        let mod_def_id = self.mod_ops().create_mod_def(
            self.builder().create_symbol(module_name),
            // For now, modules have no parameters.
            // @@Future: context
            self.builder().create_def_params([]),
            ModKind::Source(source_id),
            None,
        );

        // Traverse the module
        Context::enter_scope_mut(self, ScopeKind::Mod(mod_def_id), |this| {
            walk_mut_self::walk_module(this, node)
        })?;

        // Get all the members found in the module and add them.
        self.store_found_def_members(mod_def_id);

        Ok(())
    }

    type ModBlockRet = ();
    fn visit_mod_block(
        &mut self,
        node: ast::AstNodeRef<ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        // Get the mod block name from the name hint.
        let mod_block_name = self.take_name_hint_or_create_internal_name();

        // Create a mod block definition, with empty members for now.
        let mod_def_id = self.mod_ops().create_mod_def(
            mod_block_name,
            // @@Todo: params
            self.builder().create_def_params([]),
            ModKind::ModBlock,
            None,
        );

        // Traverse the mod block
        Context::enter_scope_mut(self, ScopeKind::Mod(mod_def_id), |this| {
            walk_mut_self::walk_mod_block(this, node)
        })?;

        // Get all the members found in the module and add them.
        self.store_found_def_members(mod_def_id);

        Ok(())
    }
}
