// @@Docs
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
    terms::{Term, TermId},
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

/// The ID of some definition.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
enum DefId {
    Mod(ModDefId),
    Trt(TrtDefId),
    Data(DataDefId),
    Stack(StackId),
}

/// A found definition member in a scope.
pub struct DefMemberFound {
    pub data: DefMemberData,
}

/// Pass which discovers scopes in the AST, and adds them to the global context.
/// @@Docs
pub struct ScopeDiscoveryPass<'env> {
    tc_env: &'env TcEnv<'env>,
    name_hint: Option<Symbol>,
    ast_ids_to_term_ids: HashMap<ast::AstNodeId, TermId>,
    def_members_found: HashMap<DefId, Vec<DefMemberFound>>,
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

    /// Run the given closure with the given name hint, resetting it at the end.
    fn with_name_hint<T>(&mut self, name_hint: Symbol, mut f: impl FnMut(&mut Self) -> T) -> T {
        let prev_hint = self.name_hint;
        self.name_hint = Some(name_hint);
        let result = f(self);
        self.name_hint = prev_hint;
        result
    }

    /// Add a found definition member to the current context.
    fn add_def_member(&mut self, def_id: impl Into<DefId>, member: DefMemberData) {
        self.def_members_found.entry(def_id.into()).or_default().push(DefMemberFound {
            data: member, // origin,
        });
    }

    /// Get all the found definition members for a given definition so far.
    fn get_def_members(&self, def_id: impl Into<DefId>) -> &[DefMemberFound] {
        self.def_members_found.get(&def_id.into()).map(|x| x.as_slice()).unwrap_or(&[])
    }

    /// Store all the found definition members in the definition, for the given
    /// definition ID.
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

    /// Take the currently set name hint, or create a new internal name.
    fn take_name_hint_or_create_internal_name(&mut self) -> Symbol {
        self.name_hint.take().unwrap_or_else(|| self.new_fresh_symbol())
    }

    /// Set the inferred term for the given node.
    fn set_term_for_node<T>(&mut self, node: ast::AstNodeRef<T>, term: TermId) {
        self.ast_ids_to_term_ids.insert(node.id(), term);
    }

    /// If the given `expr` is a mod/trait/data definition, get its set value
    /// from `ast_ids_to_term_ids`. Otherwise, return `None`
    fn get_value_term_of_def(&mut self, expr: ast::AstNodeRef<ast::Expr>) -> Option<TermId> {
        let get_term_from_ast_node_id = |node_id: ast::AstNodeId| {
            self.ast_ids_to_term_ids.get(&node_id).copied().expect("Missing definition term")
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
    ast_visitor_mut_self_default_impl!(hiding: Declaration, Module, ModBlock, TraitDef,);

    type DeclarationRet = ();
    fn visit_declaration(
        &mut self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let make_def_member = |this: &mut Self| {
            let name = match node.pat.body() {
                ast::Pat::Binding(binding) => this.new_symbol(binding.name.ident),
                _ => unreachable!("non-named declaration patterns in constant scopes found after pre-tc semantics"),
            };
            // With the member's name hint, walk the value.
            //
            // If the declaration is in the form `x := mod/trait/struct/enum/impl ...`, then
            // it will use this name hint to declare it.
            this.with_name_hint(name, |this| walk_mut_self::walk_declaration(this, node))?;

            // Get the created value of this term
            let value = node.value.as_ref().map(|value| {
                this.get_value_term_of_def(value.ast_ref()).unwrap_or_else(|| this.new_term_hole())
            });

            // Infer the type of the value
            //
            // This will be a hole unless the value is a definition.
            let ty = value
                .map(|value| this.infer_ops().infer_ty_of_term_or_hole(value))
                .unwrap_or_else(|| this.new_ty_hole());

            Ok(DefMemberData { name, ty, value })
        };

        let member = make_def_member(self)?;
        let id: DefId = match self.context().get_scope_kind() {
            ScopeKind::Mod(mod_def_id) => mod_def_id.into(),
            ScopeKind::Trt(trt_def_id) => trt_def_id.into(),
            ScopeKind::Stack(stack_id) => stack_id.into(),
            ScopeKind::Data(data_def_id) => data_def_id.into(),
            ScopeKind::Fn(_) => {
                // Function body, do nothing for now
                return Ok(());
            }
        };
        self.add_def_member(id, member);
        Ok(())
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
            self.new_symbol(module_name),
            // For now, modules have no parameters.
            // @@Future: context
            self.new_empty_def_params(),
            ModKind::Source(source_id),
            None,
        );

        self.set_term_for_node(node, self.new_term(Term::ModDef(mod_def_id)));

        // Traverse the module
        Context::enter_scope_mut(self, ScopeKind::Mod(mod_def_id), |this| {
            walk_mut_self::walk_module(this, node)
        })?;

        // Get all the members found in the module and add them.
        self.store_found_def_members(mod_def_id);

        // For now, print the module
        println!("mod_def_id: {}", self.env().with(mod_def_id));

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
            self.new_empty_def_params(),
            ModKind::ModBlock,
            None,
        );

        self.set_term_for_node(node, self.new_term(Term::ModDef(mod_def_id)));

        // Traverse the mod block
        Context::enter_scope_mut(self, ScopeKind::Mod(mod_def_id), |this| {
            walk_mut_self::walk_mod_block(this, node)
        })?;

        // Get all the members found in the module and add them.
        self.store_found_def_members(mod_def_id);

        Ok(())
    }

    type TraitDefRet = ();

    fn visit_trait_def(
        &mut self,
        node: ast::AstNodeRef<ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        // Get the trait name from the name hint.
        let trt_name = self.take_name_hint_or_create_internal_name();

        // Create a trait block definition, with empty members for now.
        let trt_def_id = self.trt_ops().create_trt_def(
            trt_name,
            // @@Todo: params
            self.new_empty_def_params(),
            self.new_symbol("Self"),
        );

        self.set_term_for_node(node, self.new_term(Term::TrtDef(trt_def_id)));

        // Traverse the trait block
        Context::enter_scope_mut(self, ScopeKind::Trt(trt_def_id), |this| {
            walk_mut_self::walk_trait_def(this, node)
        })?;

        // Get all the members found in the module and add them.
        self.store_found_def_members(trt_def_id);

        Ok(())
    }
}
