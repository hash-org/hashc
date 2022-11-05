use std::collections::HashMap;

use hash_ast::{ast, ast_visitor_mut_self_default_impl, visitor::walk_mut_self};
use hash_source::identifier::Identifier;
use hash_types::new::{
    data::{CtorDefData, DataDefId},
    defs::DefMemberData,
    environment::{
        context::{Context, ScopeKind},
        env::AccessToEnv,
    },
    mods::{ModDefId, ModKind},
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

pub struct ScopeDiscoveryPass<'env> {
    tc_env: &'env TcEnv<'env>,
    name_hint: Option<Symbol>,

    ast_ids_to_term_ids: HashMap<ast::AstNodeId, TermId>,

    mod_def_members_found: HashMap<ModDefId, Vec<DefMemberData>>,

    _trt_def_members_found: HashMap<TrtDefId, Vec<DefMemberData>>,

    _data_def_members_found: HashMap<DataDefId, Vec<CtorDefData>>,
}

impl<'env> ScopeDiscoveryPass<'env> {
    pub fn new(tc_env: &'env TcEnv<'env>) -> Self {
        Self {
            tc_env,
            name_hint: None,
            ast_ids_to_term_ids: HashMap::new(),
            mod_def_members_found: HashMap::new(),
            _data_def_members_found: HashMap::new(),
            _trt_def_members_found: HashMap::new(),
        }
    }

    fn with_name_hint<T>(&mut self, name_hint: Symbol, mut f: impl FnMut(&mut Self) -> T) -> T {
        self.name_hint = Some(name_hint);
        let result = f(self);
        self.name_hint = None;
        result
    }

    fn add_mod_def_member(&mut self, mod_def_id: ModDefId, member: DefMemberData) {
        self.mod_def_members_found.entry(mod_def_id).or_default().push(member);
    }

    fn get_mod_def_members(&self, mod_def_id: ModDefId) -> &[DefMemberData] {
        self.mod_def_members_found.get(&mod_def_id).map(|x| x.as_slice()).unwrap_or(&[])
    }

    fn store_found_mod_def_members(&mut self, mod_def_id: ModDefId) {
        let members = self.get_mod_def_members(mod_def_id);
        let members_stored = self.mod_ops().create_mod_members(members.iter().copied());
        self.mod_ops().set_mod_def_members(mod_def_id, members_stored);
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
            // With the member's name hint, walk the value
            this.with_name_hint(name, |this| walk_mut_self::walk_declaration(this, node))?;

            let value =
                node.value.as_ref().and_then(|value| this.get_value_term_of_def(value.ast_ref()));

            Ok(DefMemberData { name, ty: this.new_ty_hole(), value })
        };

        match self.context().get_scope_kind() {
            ScopeKind::Mod(mod_def_id) => {
                // Mod members
                let member = make_def_member(self)?;
                self.add_mod_def_member(mod_def_id, member);
                Ok(())
            }
            ScopeKind::Trt(_) => {
                // Trait members
                Ok(())
            }
            ScopeKind::Stack(_) => {
                // Stack variables
                Ok(())
            }
            ScopeKind::Data(_) => {
                // Constructor
                Ok(())
            }
            ScopeKind::Fn(_) => {
                // Function body
                Ok(())
            }
        }
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
        self.store_found_mod_def_members(mod_def_id);

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
        self.store_found_mod_def_members(mod_def_id);

        Ok(())
    }
}
