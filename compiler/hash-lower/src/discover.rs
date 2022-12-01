//! Module that implements the [AstVisitor] pattern for the
//! [Builder]. Most of these functions aren't used since the
//! vast majority of the code is working to simplify a particular
//! constant declaration or a function body.

use std::{collections::HashSet, convert::Infallible, mem};

use hash_ast::{
    ast::{self, AstNodeId},
    ast_visitor_mut_self_default_impl,
    origin::BlockOrigin,
    visitor::{walk_mut_self, AstVisitorMutSelf},
};
use hash_ir::{ir::Body, IrStorage};
use hash_pipeline::settings::LoweringSettings;
use hash_source::{
    identifier::{Identifier, IDENTS},
    SourceId, SourceMap,
};
use hash_types::storage::GlobalStorage;

use crate::build::Builder;

/// [Binding]s are used to track what variables a particular declaration  
/// binds. This is needed because declarations can bind multiple variables in
/// a single expression. For example, `let (a, b) = (1, 2);` binds both `a` and
/// `b` to the values `1` and `2` respectively. The [Binding] stores the name
/// that it binds, and an [AstNodeId] which points to which [AstNode] it binds
/// to. The `id` of node is stored so that the [Builder] can later use it to
/// look up which declarations it should and shouldn't attempt to lower.
pub struct Binding {
    /// The name that the binding is specifying
    name: Identifier,

    /// The relevant [AstNodeId] that this binding points too.
    node: AstNodeId,
}

fn extract_binds_from_bind(pat: ast::AstNodeRef<ast::Pat>, binds: &mut Vec<Binding>) {
    match &pat.body() {
        ast::Pat::Binding(ast::BindingPat { name, .. }) => {
            binds.push(Binding { name: name.ident, node: pat.id() });
        }
        ast::Pat::Wild(_) => {
            // @@Weirdness: what should happen to a function body if it bound to
            // a pattern that ignores the result, i.e. `_`? Should we just ignore
            // it, or should we lower the function anyway. This is a weird case,
            // because the function can never be invoked because it is not bound,
            // so should we not do anything here?
            binds.push(Binding { name: IDENTS.underscore, node: pat.id() });
        }
        ast::Pat::Tuple(ast::TuplePat { fields }) => {
            for entry in fields.iter() {
                let ast::TuplePatEntry { name, pat } = entry.body();

                // If the entry has a name, then use it otherwise we traverse
                // down to find more binds. @@Verify: is this checked within the
                // typechecker.
                if let Some(entry_name) = name {
                    binds.push(Binding { name: entry_name.ident, node: entry.id() });
                } else {
                    extract_binds_from_bind(pat.ast_ref(), binds);
                }
            }
        }
        ast::Pat::List(ast::ListPat { fields }) => {
            for entry in fields.iter() {
                extract_binds_from_bind(entry.ast_ref(), binds);
            }
        }
        ast::Pat::Or(ast::OrPat { variants }) => {
            debug_assert!(variants.len() > 1);

            // Look at the left most pattern and extract all of the binds, since
            // we have already checked that each pattern has the same binds
            // present in it.
            extract_binds_from_bind(variants[0].ast_ref(), binds)
        }
        ast::Pat::If(ast::IfPat { pat, .. }) => extract_binds_from_bind(pat.ast_ref(), binds),

        // These never bind anything, so we can just ignore them.
        ast::Pat::Constructor(_)
        | ast::Pat::Access(_)
        | ast::Pat::Module(_)
        | ast::Pat::Spread(_)
        | ast::Pat::Range(_)
        | ast::Pat::Lit(_) => {}
    };
}

/// The [LoweringVisitor] is a struct that is used to implement
/// the discovery process for what needs to be lowered. This is
/// essentially a visitor pattern that will walk through the AST
/// and discover what needs to be lowered.
pub(crate) struct LoweringVisitor<'ir> {
    /// The [GlobalStorage] that is used to provide type
    /// information to the [Builder] whenever it encounters
    /// an item that it needs to lower.
    tcx: &'ir GlobalStorage,

    /// Used to store all of the generated bodies and rvalues.
    storage: &'ir mut IrStorage,

    source_map: &'ir SourceMap,

    /// The [SourceId] of the current source that is being
    /// lowered.
    source_id: SourceId,

    /// The current lowering settings.
    settings: LoweringSettings,

    /// Declaration binds stack, this is used to resolve the name of
    /// the declared function or functions. It is made to be a stack
    /// because a single declaration can bind multiple functions, e.g.
    /// ```ignore
    /// (a, b) := (() => 1, () => 2);
    /// ```
    pub(crate) bind_stack: Vec<Binding>,

    /// Flag denoting whether the current visited function def/constant
    /// block needs to be `dumped`.
    pub(crate) in_dump_ir_directive: bool,

    /// The current scope of the traversal, representing which block the
    /// analyser is walking.
    pub(crate) current_block: BlockOrigin,

    /// All of the bodies that have currently been generated by
    /// visiting the current source.
    pub(crate) bodies: Vec<Body>,

    /// Dead ends that a particular [Builder] should not attempt to traverse
    /// and build IR from. This is needed to avoid trying to lower declarations
    /// that have function declarations in them.
    dead_ends: HashSet<AstNodeId>,
}

impl<'ir> LoweringVisitor<'ir> {
    pub fn new(
        tcx: &'ir GlobalStorage,
        storage: &'ir mut IrStorage,
        source_map: &'ir SourceMap,
        source_id: SourceId,
        settings: LoweringSettings,
    ) -> Self {
        Self {
            settings,
            tcx,
            current_block: BlockOrigin::Const,
            storage,
            source_id,
            source_map,
            in_dump_ir_directive: false,
            bodies: Vec::new(),
            bind_stack: Vec::new(),
            dead_ends: HashSet::new(),
        }
    }

    pub(crate) fn into_bodies(self) -> Vec<Body> {
        self.bodies
    }
}

// @@Temporary: This will only attempt to find top-level definitions that
// need to be lowered. This will include all functions, and their associated
// bodies, as well as all constant declarations.
impl<'a> AstVisitorMutSelf for LoweringVisitor<'a> {
    type Error = Infallible;

    type TraitImplRet = ();

    fn visit_trait_impl(
        &mut self,
        node: ast::AstNodeRef<ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        let old_block_origin = mem::replace(&mut self.current_block, BlockOrigin::Impl);
        let _ = walk_mut_self::walk_trait_impl(self, node);
        self.current_block = old_block_origin;
        Ok(())
    }

    type TraitDefRet = ();

    fn visit_trait_def(
        &mut self,
        node: ast::AstNodeRef<ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let old_block_origin = mem::replace(&mut self.current_block, BlockOrigin::Trait);
        let _ = walk_mut_self::walk_trait_def(self, node);
        self.current_block = old_block_origin;
        Ok(())
    }

    type FnDefRet = ();

    fn visit_fn_def(
        &mut self,
        node: ast::AstNodeRef<ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        // @@Todo: deal with closures, we need to possibly introduce a new Term
        // that denotes whether a particular binding is a closure or not to disambiguate
        // between free and closure declarations within functions.

        // Pop off the top bind from the top of the stack, if no item is present
        // then we should just use `_` (it is an invariant if there is no name when we
        // reach a function definition with no assigned name).
        let binding = self
            .bind_stack
            .pop()
            .unwrap_or_else(|| Binding { name: IDENTS.underscore, node: node.id() });

        // We want to walk the inner part of the function to check
        // if we need to lower anything within the function.
        let _ = walk_mut_self::walk_fn_def(self, node);

        // Create the builder here, and then proceed to emit the generated function
        // body!
        let mut builder = Builder::new(
            binding.name,
            node.into(),
            self.source_id,
            self.tcx,
            self.storage,
            self.source_map,
            &self.dead_ends,
            &self.settings,
        );
        builder.build_fn();

        let mut generated_body = builder.finish();

        // If we are in the `dump_ir` directive, then we need to
        // mark the generated body as needing to be dumped.
        if self.in_dump_ir_directive {
            generated_body.mark_to_dump();
        }

        self.bodies.push(generated_body);

        // We want to clear the dead ends after we have finished lowering the particular
        // function and then add this ID to the dead ends
        self.dead_ends.clear();
        self.dead_ends.insert(binding.node);

        Ok(())
    }

    type ImplDefRet = ();

    fn visit_impl_def(
        &mut self,
        node: ast::AstNodeRef<ast::ImplDef>,
    ) -> Result<Self::ImplDefRet, Self::Error> {
        let old_block_origin = mem::replace(&mut self.current_block, BlockOrigin::Impl);
        let _ = walk_mut_self::walk_impl_def(self, node);
        self.current_block = old_block_origin;
        Ok(())
    }

    type ModuleRet = ();

    fn visit_module(
        &mut self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        self.current_block = BlockOrigin::Root;
        let _ = walk_mut_self::walk_module(self, node);
        Ok(())
    }

    type ExprRet = ();

    fn visit_expr(
        &mut self,
        node: ast::AstNodeRef<ast::Expr>,
    ) -> Result<Self::ExprRet, Self::Error> {
        // We don't walk the inner bodies of traits (unless they have default impls?)
        if !matches!(self.current_block, BlockOrigin::Trait) {
            let _ = walk_mut_self::walk_expr(self, node);
        }

        Ok(())
    }

    type DirectiveExprRet = ();

    fn visit_directive_expr(
        &mut self,
        node: ast::AstNodeRef<ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        // If this directive is a `dump_ir`, then specify that
        // we are currently within a `dump_ir` directive, which
        // will mark the child function definition as needing
        // to be `dumped`.
        let mut old_dump_ir_value = self.in_dump_ir_directive;

        if node.name.is(IDENTS.dump_ir) {
            old_dump_ir_value = mem::replace(&mut self.in_dump_ir_directive, true);
        }

        let _ = walk_mut_self::walk_directive_expr(self, node);

        // Reset the old directive value.
        self.in_dump_ir_directive = old_dump_ir_value;
        Ok(())
    }

    type DeclarationRet = ();

    fn visit_declaration(
        &mut self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        // Here, we need to inspect the declaration and extract all of the binds that
        // it makes. Once this is done, we need to push all of the declarations onto
        // the `bind_stack` in reverse order, since this is how the functions will be
        // traversed.
        let mut binds = Vec::new();
        extract_binds_from_bind(node.pat.ast_ref(), &mut binds);

        self.bind_stack.extend(binds.into_iter().rev());
        let _ = walk_mut_self::walk_declaration(self, node);

        Ok(())
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &mut self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        let old_block_origin = mem::replace(&mut self.current_block, BlockOrigin::Body);

        let _ = walk_mut_self::walk_body_block(self, node);
        self.current_block = old_block_origin;
        Ok(())
    }

    type ModDefRet = ();

    fn visit_mod_def(
        &mut self,
        node: ast::AstNodeRef<ast::ModDef>,
    ) -> Result<Self::ModDefRet, Self::Error> {
        let old_block_origin = mem::replace(&mut self.current_block, BlockOrigin::Mod);
        let _ = walk_mut_self::walk_mod_def(self, node);
        self.current_block = old_block_origin;

        Ok(())
    }

    ast_visitor_mut_self_default_impl!(
        hiding: Expr,
        DirectiveExpr,
        FnDef,
        Declaration,
        BodyBlock,
        TraitDef,
        TraitImpl,
        ModDef,
        ImplDef,
        Module
    );
}
