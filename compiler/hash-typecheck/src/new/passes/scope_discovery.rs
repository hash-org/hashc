use std::collections::HashMap;

use hash_ast::{ast, ast_visitor_mut_self_default_impl, visitor::walk_mut_self};
use hash_source::identifier::Identifier;
use hash_types::new::{
    defs::DefMemberData,
    environment::{
        context::{Context, ScopeKind},
        env::AccessToEnv,
    },
    mods::{ModDefId, ModKind},
};

use crate::{
    diagnostics::error::TcError,
    impl_access_to_tc_env,
    new::{environment::tc_env::TcEnv, ops::AccessToOps},
};

pub struct ScopeDiscoveryPass<'env> {
    tc_env: &'env TcEnv<'env>,
    mod_def_members_found: HashMap<ModDefId, Vec<DefMemberData>>,
}

impl<'env> ScopeDiscoveryPass<'env> {
    pub fn new(tc_env: &'env TcEnv<'env>) -> Self {
        Self { tc_env, mod_def_members_found: Default::default() }
    }
}

impl_access_to_tc_env!(ScopeDiscoveryPass<'env>);

impl<'env> ast::AstVisitorMutSelf for ScopeDiscoveryPass<'env> {
    type Error = TcError;
    ast_visitor_mut_self_default_impl!(hiding: Declaration, Module);

    type DeclarationRet = ();
    fn visit_declaration(
        &mut self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let make_def_member = |this: &mut Self| {
            let name = match node.pat.body() {
                ast::Pat::Binding(binding) => this.builder().create_symbol(binding.name.ident),
                // @@ErrorHandling
                _ => panic!("Invalid declaration pattern"),
            };

            DefMemberData { name, ty: this.ty_ops().new_ty_hole(), value: None }
        };

        match self.context().get_scope_kind() {
            ScopeKind::Mod(mod_def_id) => {
                // Mod members
                let member = make_def_member(self);
                self.mod_def_members_found.entry(mod_def_id).or_default().push(member);
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

        let mod_ops = self.mod_ops();
        let b = self.builder();

        // Create a module definition, with empty members for now.
        let mod_def_id = mod_ops.create_mod_def(
            b.create_symbol(module_name),
            b.create_def_params([]),
            ModKind::Source(source_id),
            None,
        );

        // Traverse the module in the context of the module definition.
        Context::enter_scope_mut(self, ScopeKind::Mod(mod_def_id), |this| {
            walk_mut_self::walk_module(this, node)
        })?;

        // Get all the members found in the module and add them.
        let mod_ops = self.mod_ops();
        let members =
            self.mod_def_members_found.get(&mod_def_id).map(|x| x.as_slice()).unwrap_or(&[]);
        mod_ops
            .set_mod_def_members(mod_def_id, mod_ops.create_mod_members(members.iter().copied()));

        // @@Debugging: Print the module:
        println!("{}", self.env().with(mod_def_id));

        Ok(())
    }
}
