// @@Docs
use std::cell::Cell;

use derive_more::From;
use hash_ast::{ast, ast_visitor_default_impl, visitor::AstVisitor};
use hash_types::new::{
    data::DataDefId, defs::DefMemberData, mods::ModDefId, scopes::StackId, symbols::Symbol,
};

use super::pass::AstPass;
use crate::{
    impl_access_to_tc_env,
    new::{diagnostics::error::TcError, environment::tc_env::TcEnv, ops::common::CommonOps},
};

/// The ID of some definition.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
enum DefId {
    Mod(ModDefId),
    Data(DataDefId),
    Stack(StackId),
}

/// A found definition member in a scope.
pub struct DefMemberFound {
    pub data: DefMemberData,
}

/// Pass which discovers scopes in the AST, and adds them to the global context.
/// @@Docs
pub struct ScopeDiscoveryPass<'tc> {
    tc_env: &'tc TcEnv<'tc>,
    _name_hint: Cell<Option<Symbol>>,
}

impl<'tc> AstPass for ScopeDiscoveryPass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        self.visit_body_block(node)
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        self.visit_module(node)
    }
}

impl<'tc> ScopeDiscoveryPass<'tc> {
    pub fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        Self { tc_env, _name_hint: Cell::new(None) }
    }

    /// Run the given closure with the given name hint, resetting it at the end.
    fn _with_name_hint<T>(&self, name_hint: Symbol, mut f: impl FnMut() -> T) -> T {
        let prev_hint = self._name_hint.get();
        self._name_hint.set(Some(name_hint));
        let result = f();
        self._name_hint.set(prev_hint);
        result
    }

    /// Take the currently set name hint, or create a new internal name.
    fn _take_name_hint_or_create_internal_name(&mut self) -> Symbol {
        self._name_hint.take().unwrap_or_else(|| self.new_fresh_symbol())
    }
}

impl_access_to_tc_env!(ScopeDiscoveryPass<'tc>);

impl<'tc> ast::AstVisitor for ScopeDiscoveryPass<'tc> {
    type Error = TcError;
    ast_visitor_default_impl!(hiding: Declaration, Module, ModBlock, TraitDef,);

    type DeclarationRet = ();
    fn visit_declaration(
        &self,
        _node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        todo!()
        // let make_def_member = |this: &Self| {
        //     let name = match node.pat.body() {
        //         ast::Pat::Binding(binding) =>
        // this.new_symbol(binding.name.ident),         _ =>
        // unreachable!("non-named declaration patterns in constant scopes found
        // after pre-tc semantics"),     };
        //     // With the member's name hint, walk the value.
        //     //
        //     // If the declaration is in the form `x :=
        // mod/trait/struct/enum/impl ...`, then     // it will use this
        // name hint to declare it.     this.with_name_hint(name, ||
        // walk_mut_self::walk_declaration(this, node))?;

        //     // Get the created value of this term
        //     let value = node.value.as_ref().map(|value| {
        //         this.get_value_term_of_def(value.ast_ref()).unwrap_or_else(||
        // this.new_term_hole())     });

        //     // Infer the type of the value
        //     //
        //     // This will be a hole unless the value is a definition.
        //     let ty = value
        //         .map(|value|
        // this.infer_ops().infer_ty_of_term_or_hole(value))
        //         .unwrap_or_else(|| this.new_ty_hole());

        //     Ok(DefMemberData { name, ty, value })
        // };

        // let member = make_def_member(self)?;
        // let id: DefId = match self.context().get_scope_kind() {
        //     ScopeKind::Mod(mod_def_id) => mod_def_id.into(),
        //     ScopeKind::Stack(stack_id) => stack_id.into(),
        //     ScopeKind::Data(data_def_id) => data_def_id.into(),
        //     ScopeKind::Fn(_) => {
        //         // Function body, do nothing for now
        //         return Ok(());
        //     }
        // };
        // self.add_def_member(id, member);
        // Ok(())
    }

    type ModuleRet = ();
    fn visit_module(
        &self,
        _node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        todo!()
        // let source_id = self.current_source_info().source_id;
        // let module_name: Identifier =
        // self.source_map().source_name(source_id).into();

        // // Create a module definition, with empty members for now.
        // let mod_def_id = self.mod_ops().create_mod_def(
        //     self.new_symbol(module_name),
        //     // For now, modules have no parameters.
        //     // @@Future: context
        //     self.new_empty_def_params(),
        //     ModKind::Source(source_id),
        //     None,
        // );

        // // Traverse the module
        // self.context().enter_scope(ScopeKind::Mod(mod_def_id), ||
        // walk::walk_module(self, node))?;

        // // Get all the members found in the module and add them.
        // self.store_found_def_members(mod_def_id);

        // // For now, print the module
        // println!("mod_def_id: {}", self.env().with(mod_def_id));

        // Ok(())
    }

    type ModBlockRet = ();
    fn visit_mod_block(
        &self,
        _node: ast::AstNodeRef<ast::ModBlock>,
    ) -> Result<Self::ModBlockRet, Self::Error> {
        todo!()
        // // Get the mod block name from the name hint.
        // let mod_block_name = self.take_name_hint_or_create_internal_name();

        // // Create a mod block definition, with empty members for now.
        // let mod_def_id = self.mod_ops().create_mod_def(
        //     mod_block_name,
        //     // @@Todo: params
        //     self.new_empty_def_params(),
        //     ModKind::ModBlock,
        //     None,
        // );

        // // Traverse the mod block
        // self.context()
        //     .enter_scope(ScopeKind::Mod(mod_def_id), ||
        // walk::walk_mod_block(self, node))?;

        // // Get all the members found in the module and add them.
        // self.store_found_def_members(mod_def_id);

        // Ok(())
    }

    type TraitDefRet = ();

    fn visit_trait_def(
        &self,
        _node: ast::AstNodeRef<ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        todo!()
    }
}
