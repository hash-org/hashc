// //! Module that implements the [AstVisitor] pattern for the
// //! [Builder]. Most of these functions aren't used since the
// //! vast majority of the code is working to simplify a particular
// //! constant declaration or a function body.

// use std::{collections::HashSet, convert::Infallible, mem};

// use hash_ast::{
//     ast, ast_visitor_mut_self_default_impl,
//     origin::BlockOrigin,
//     visitor::{walk_mut_self, AstVisitorMutSelf},
// };
// use hash_ir::{
//     ir::Body,
//     ty::{InstanceId, IrTy},
//     IrCtx,
// };
// use hash_pipeline::settings::CompilerSettings;
// use hash_source::{
//     identifier::{Identifier, IDENTS},
//     SourceId, SourceMap,
// };
// use hash_tir::{scope::ScopeId, storage::TyStorage};
// use hash_utils::store::CloneStore;

// use crate::build::{BuildItem, Builder};

// /// [Binding]s are used to track what variables a particular declaration  
// /// binds. This is needed because declarations can bind multiple variables in
// /// a single expression. For example, `let (a, b) = (1, 2);` binds both `a` and
// /// `b` to the values `1` and `2` respectively. The [Binding] stores the name
// /// that it binds, and an [ast::AstNodeId] which points to which [ast::AstNode]
// /// it binds to. The `id` of node is stored so that the [Builder] can later use
// /// it to look up which declarations it should and shouldn't attempt to lower.
// #[derive(Clone, Copy)]
// pub struct Binding {
//     /// The name that the binding is specifying
//     name: Identifier,

//     /// The relevant [ast::AstNodeId] that this binding points too.
//     node: ast::AstNodeId,
// }

// fn extract_binds_from_bind(pat: ast::AstNodeRef<ast::Pat>, binds: &mut Vec<Binding>) {
//     match &pat.body() {
//         ast::Pat::Binding(ast::BindingPat { name, .. }) => {
//             binds.push(Binding { name: name.ident, node: pat.id() });
//         }
//         ast::Pat::Wild(_) => {
//             // @@Weirdness: what should happen to a function body if it bound to
//             // a pattern that ignores the result, i.e. `_`? Should we just ignore
//             // it, or should we lower the function anyway. This is a weird case,
//             // because the function can never be invoked because it is not bound,
//             // so should we not do anything here?
//             binds.push(Binding { name: IDENTS.underscore, node: pat.id() });
//         }
//         ast::Pat::Tuple(ast::TuplePat { fields, spread }) => {
//             for entry in fields.iter() {
//                 let ast::TuplePatEntry { name, pat } = entry.body();

//                 // If the entry has a name, then use it otherwise we traverse
//                 // down to find more binds. @@Verify: is this checked within the
//                 // typechecker.
//                 if let Some(entry_name) = name {
//                     binds.push(Binding { name: entry_name.ident, node: entry.id() });
//                 } else {
//                     extract_binds_from_bind(pat.ast_ref(), binds);
//                 }
//             }

//             if let Some(spread_pat) = spread && let Some(name) = &spread_pat.name {
//                 binds.push(Binding { name: name.ident, node: spread_pat.id() });
//             }
//         }
//         ast::Pat::Array(ast::ArrayPat { fields, spread }) => {
//             for entry in fields.iter() {
//                 extract_binds_from_bind(entry.ast_ref(), binds);
//             }

//             if let Some(spread_pat) = spread && let Some(name) = &spread_pat.name {
//                 binds.push(Binding { name: name.ident, node: spread_pat.id() });
//             }
//         }
//         ast::Pat::Or(ast::OrPat { variants }) => {
//             debug_assert!(variants.len() > 1);

//             // Look at the left most pattern and extract all of the binds, since
//             // we have already checked that each pattern has the same binds
//             // present in it.
//             extract_binds_from_bind(variants[0].ast_ref(), binds)
//         }
//         ast::Pat::If(ast::IfPat { pat, .. }) => extract_binds_from_bind(pat.ast_ref(), binds),

//         // These never bind anything that we need to track in terms
//         // of item discovery. @@Verify: what happens to constructor patterns here?
//         ast::Pat::Constructor(_)
//         | ast::Pat::Access(_)
//         | ast::Pat::Module(_)
//         | ast::Pat::Range(_)
//         | ast::Pat::Lit(_) => {}
//     };
// }

// bitflags::bitflags! {
//     /// The currently applying directives at the current location within
//     /// the AST.
//     #[derive(Clone, Copy, Debug, PartialEq, Eq)]
//     pub(crate) struct AppliedDirectives: u8 {
//         /// The traversal is currently within a "layout_of" directive.
//         const IN_LAYOUT_OF = 1 << 1;

//         /// The traversal is currently with a "dump_ir" directive.
//         const IN_DUMP_IR = 1 << 2;
//     }
// }

// /// The [LoweringVisitor] is a struct that is used to implement
// /// the discovery process for what needs to be lowered. This is
// /// essentially a visitor pattern that will walk through the AST
// /// and discover what needs to be lowered.
// pub(crate) struct LoweringVisitor<'ir> {
//     /// The [GlobalStorage] that is used to provide type
//     /// information to the [Builder] whenever it encounters
//     /// an item that it needs to lower.
//     tcx: &'ir Env,

//     /// Used to store all of the generated bodies and rvalues.
//     lcx: &'ir mut IrCtx,

//     /// The map of all sources that are currently registered in the
//     /// compiler.
//     source_map: &'ir SourceMap,

//     /// The current scope that the stack, the lowerer is visiting.
//     scope_stack: Vec<ScopeId>,

//     /// The [SourceId] of the current source that is being
//     /// lowered.
//     source_id: SourceId,

//     /// The current lowering settings.
//     settings: &'ir CompilerSettings,

//     /// Declaration binds stack, this is used to resolve the name of
//     /// the declared function or functions. It is made to be a stack
//     /// because a single declaration can bind multiple functions, e.g.
//     /// ```ignore
//     /// (a, b) := (() => 1, () => 2);
//     /// ```
//     pub(crate) bind_stack: Vec<Binding>,

//     /// The current set of directives that are being applied to the
//     /// current position in the AST.
//     pub(crate) applied_directives: AppliedDirectives,

//     /// The current scope of the traversal, representing which block the
//     /// analyser is walking.
//     pub(crate) block_origin: BlockOrigin,

//     /// All of the bodies that have currently been generated by
//     /// visiting the current source.
//     pub(crate) bodies: Vec<Body>,

//     /// If an entry point was specified in this module, then this
//     /// will store the index into the `bodies` vector that points
//     /// to the index of the entry point.
//     entry_point_index: Option<usize>,

//     /// All of the recorded AST ids that have been marked for
//     /// the `#layout_of` directive. This means that once the
//     /// lowering process has finished, these ids will be used
//     /// to query the type layouts.
//     pub(crate) layout_to_generate: Vec<ast::AstNodeId>,

//     /// Dead ends that a particular [Builder] should not attempt to traverse
//     /// and build IR from. This is needed to avoid trying to lower declarations
//     /// that have function declarations in them.
//     dead_ends: HashSet<ast::AstNodeId>,
// }

// impl<'ir> LoweringVisitor<'ir> {
//     pub fn new(
//         tcx: &'ir TyStorage,
//         lcx: &'ir mut IrCtx,
//         source_map: &'ir SourceMap,
//         source_id: SourceId,
//         settings: &'ir CompilerSettings,
//     ) -> Self {
//         Self {
//             settings,
//             tcx,
//             block_origin: BlockOrigin::Const,

//             lcx,
//             source_id,
//             entry_point_index: None,
//             source_map,
//             applied_directives: AppliedDirectives::empty(),
//             layout_to_generate: vec![],
//             scope_stack: vec![],
//             bodies: vec![],
//             bind_stack: vec![],
//             dead_ends: HashSet::new(),
//         }
//     }

//     /// Get the entry point body [InstanceId] if the entry point
//     /// was defined in this module.
//     pub fn entry_point_instance(&self) -> Option<InstanceId> {
//         let entry_point = self.entry_point_index?;

//         let ty = self.bodies[entry_point].info().ty();
//         let IrTy::FnDef { instance, .. } = self.lcx.tys().get(ty) else {
//             panic!("entry point is not a function type")
//         };

//         Some(instance)
//     }

//     /// Function to handle a particular node that introduces a new scope. If the
//     /// node has an associated scope, it is pushed onto the scope stack, and the
//     /// node is walked. Once the node has been walked, the scope is popped off
//     /// the stack.
//     ///
//     /// Additionally, this function deals with the current `block` origin that
//     /// is set every time a new scope is entered. This is used to determine
//     /// whether a particular node is a constant or a function, and whether
//     /// it should be lowered.
//     fn with_scope<F, T>(&mut self, node: ast::AstNodeId, origin: BlockOrigin, f: F) -> T
//     where
//         F: FnOnce(&mut Self) -> T,
//     {
//         let mut pushed_scope = false;

//         if let Some(info) = self.tcx.global.node_info_store.node_info(node) {
//             if let Some(scope) = info.scope {
//                 self.scope_stack.push(scope);
//                 pushed_scope = true;
//             }
//         }

//         let old_block_origin = mem::replace(&mut self.block_origin, origin);
//         let result = f(self);
//         self.block_origin = old_block_origin;

//         if pushed_scope {
//             self.scope_stack.pop();
//         }

//         result
//     }

//     /// Function that allows the [LoweringVisitor] to temporarily apply a set of
//     /// directives to the current position in the AST. This is used to allow
//     /// directives to be applied to a particular node, and then removed once the
//     /// node has been traversed.
//     fn with_directives<F>(&mut self, directives: AppliedDirectives, f: F) -> Result<(), Infallible>
//     where
//         F: FnOnce(&mut Self) -> Result<(), Infallible>,
//     {
//         let old_directives = mem::replace(&mut self.applied_directives, directives);
//         let result = f(self);
//         self.applied_directives = old_directives;

//         result
//     }

//     /// Create the builder here, and then proceed to emit the generated function
//     /// body. This returns the body index at which the generated body is stored.
//     fn build_body<'tcx>(&mut self, binding: Binding, node: impl Into<BuildItem<'tcx>>) -> usize {
//         let mut builder = Builder::new(
//             binding.name,
//             node.into(),
//             self.source_id,
//             self.scope_stack.clone(),
//             &self.tcx.global,
//             self.lcx,
//             self.source_map,
//             &self.dead_ends,
//             self.settings,
//         );

//         builder.build();
//         let mut generated_body = builder.finish();

//         // If we are in the `dump_ir` directive, then we need to
//         // mark the generated body as needing to be dumped.
//         if self.applied_directives.contains(AppliedDirectives::IN_DUMP_IR) {
//             generated_body.mark_to_dump();
//         }

//         self.bodies.push(generated_body);

//         // We want to clear the dead ends after we have finished lowering the particular
//         // function and then add this ID to the dead ends
//         self.dead_ends.clear();
//         self.dead_ends.insert(binding.node);

//         self.bodies.len() - 1
//     }

//     /// Convert the [LoweringVisitor] into the bodies that have been generated.
//     pub(crate) fn into_components(self) -> (Vec<Body>, Vec<ast::AstNodeId>) {
//         (self.bodies, self.layout_to_generate)
//     }
// }

// // impl<'a> AstVisitorMutSelf for LoweringVisitor<'a> {
// //     type Error = Infallible;

// //     type TraitImplRet = ();

// //     fn visit_trait_impl(
// //         &mut self,
// //         node: ast::AstNodeRef<ast::TraitImpl>,
// //     ) -> Result<Self::TraitImplRet, Self::Error> {
// //         self.with_scope(node.id(), BlockOrigin::Impl, |this| {
// //             let _ = walk_mut_self::walk_trait_impl(this, node);
// //             Ok(())
// //         })
// //     }

// //     type TraitDefRet = ();

// //     fn visit_trait_def(
// //         &mut self,
// //         node: ast::AstNodeRef<ast::TraitDef>,
// //     ) -> Result<Self::TraitDefRet, Self::Error> {
// //         self.with_scope(node.id(), BlockOrigin::Trait, |this| {
// //             let _ = walk_mut_self::walk_trait_def(this, node);
// //             Ok(())
// //         })
// //     }

// //     type FnDefRet = ();

// //     fn visit_fn_def(
// //         &mut self,
// //         node: ast::AstNodeRef<ast::FnDef>,
// //     ) -> Result<Self::FnDefRet, Self::Error> {
// //         // @@Todo: deal with closures, we need to possibly introduce a new Term
// //         // that denotes whether a particular binding is a closure or not to disambiguate
// //         // between free and closure declarations within functions.

// //         // Pop off the top bind from the top of the stack, if no item is present
// //         // then we should just use `_` (it is an invariant if there is no name when we
// //         // reach a function definition with no assigned name).
// //         let binding = self
// //             .bind_stack
// //             .pop()
// //             .unwrap_or_else(|| Binding { name: IDENTS.underscore, node: node.id() });

// //         // We want to walk the inner part of the function to check
// //         // if we need to lower anything within the function.
// //         let _ = walk_mut_self::walk_fn_def(self, node);

// //         let index = self.build_body(binding, node);

// //         if self.entry_point_index.is_none() {
// //             if let Some(term) = self.tcx.entry_point_state.def() {
// //                 if let Some(info) = self.tcx.global.node_info_store.node_info(node.id()) {
// //                     if info.term_id() == term {
// //                         self.entry_point_index = Some(index);
// //                     }
// //                 }
// //             }
// //         }

// //         Ok(())
// //     }

// //     type ImplDefRet = ();

// //     fn visit_impl_def(
// //         &mut self,
// //         node: ast::AstNodeRef<ast::ImplDef>,
// //     ) -> Result<Self::ImplDefRet, Self::Error> {
// //         self.with_scope(node.id(), BlockOrigin::Impl, |this| {
// //             let _ = walk_mut_self::walk_impl_def(this, node);
// //             Ok(())
// //         })
// //     }

// //     type ModuleRet = ();

// //     fn visit_module(
// //         &mut self,
// //         node: ast::AstNodeRef<ast::Module>,
// //     ) -> Result<Self::ModuleRet, Self::Error> {
// //         self.with_scope(node.id(), BlockOrigin::Root, |this| {
// //             let _ = walk_mut_self::walk_module(this, node);
// //             Ok(())
// //         })
// //     }

// //     type ExprRet = ();

// //     fn visit_expr(
// //         &mut self,
// //         node: ast::AstNodeRef<ast::Expr>,
// //     ) -> Result<Self::ExprRet, Self::Error> {
// //         // We don't walk the inner bodies of traits (unless they have default impls?)
// //         if !matches!(self.block_origin, BlockOrigin::Trait) {
// //             let _ = walk_mut_self::walk_expr(self, node);
// //         }

// //         Ok(())
// //     }

// //     type DirectiveExprRet = ();

// //     fn visit_directive_expr(
// //         &mut self,
// //         node: ast::AstNodeRef<ast::DirectiveExpr>,
// //     ) -> Result<Self::DirectiveExprRet, Self::Error> {
// //         // If this directive is a `dump_ir`, then specify that
// //         // we are currently within a `dump_ir` directive, which
// //         // will mark the child function definition as needing
// //         // to be `dumped`.

// //         let mut new_applied_directives = self.applied_directives;

// //         for directive in &node.directives {
// //             if directive.is(IDENTS.dump_ir) {
// //                 new_applied_directives.insert(AppliedDirectives::IN_DUMP_IR);
// //             }

// //             if directive.is(IDENTS.layout_of) {
// //                 new_applied_directives.insert(AppliedDirectives::IN_LAYOUT_OF);
// //             }
// //         }

// //         self.with_directives(new_applied_directives, |this| {
// //             let _ = walk_mut_self::walk_directive_expr(this, node)?;
// //             Ok(())
// //         })
// //     }

// //     type DeclarationRet = ();

// //     fn visit_declaration(
// //         &mut self,
// //         node: ast::AstNodeRef<ast::Declaration>,
// //     ) -> Result<Self::DeclarationRet, Self::Error> {
// //         // If we are currently in a `#layout_of` directive, then it means that
// //         // we need to mark this node for layout querying later.
// //         if self.applied_directives.contains(AppliedDirectives::IN_LAYOUT_OF) {
// //             // The right-hand side needs to be a struct/enum definition for
// //             // the layout directive to apply.
// //             if let Some(value) = &node.value {
// //                 if let ast::Expr::StructDef(ast::StructDef { ty_params, .. })
// //                 | ast::Expr::EnumDef(ast::EnumDef { ty_params, .. }) = value.body()
// //                 {
// //                     // @@Future: We don't support layout queries for generic types just yet.
// //                     if ty_params.is_empty() {
// //                         self.layout_to_generate.push(node.id());
// //                     }

// //                     // we can return early here since this is a type definition.
// //                     return Ok(());
// //                 }
// //             }
// //         }

// //         // Here, we need to inspect the declaration and extract all of the binds that
// //         // it makes. Once this is done, we need to push all of the declarations onto
// //         // the `bind_stack` in reverse order, since this is how the functions will be
// //         // traversed.
// //         let mut binds = Vec::new();
// //         extract_binds_from_bind(node.pat.ast_ref(), &mut binds);

// //         // keep a copy of the first bind for later
// //         let first_bind = binds.first().copied();

// //         self.bind_stack.extend(binds.into_iter().rev());
// //         let _ = walk_mut_self::walk_declaration(self, node);

// //         // If this is an expression is within a constant scope (the block origin must
// //         // either constant), and it is not a lambda, then we emit this declaration as a
// //         // constant item.
// //         //
// //         // @@Correctness: properly deal with multiple binds being declared.
// //         if self.block_origin.is_const() {
// //             match &node.body().value {
// //                 Some(expr) if !expr.is_def() && first_bind.is_some() => {
// //                     let binding = first_bind.unwrap();
// //                     self.build_body(binding, expr.ast_ref());
// //                 }
// //                 _ => {}
// //             }
// //         }

// //         Ok(())
// //     }

// //     type BodyBlockRet = ();

// //     fn visit_body_block(
// //         &mut self,
// //         node: ast::AstNodeRef<ast::BodyBlock>,
// //     ) -> Result<Self::BodyBlockRet, Self::Error> {
// //         self.with_scope(node.id(), BlockOrigin::Body, |this| {
// //             let _ = walk_mut_self::walk_body_block(this, node);
// //             Ok(())
// //         })
// //     }

// //     type ModDefRet = ();

// //     fn visit_mod_def(
// //         &mut self,
// //         node: ast::AstNodeRef<ast::ModDef>,
// //     ) -> Result<Self::ModDefRet, Self::Error> {
// //         self.with_scope(node.id(), BlockOrigin::Mod, |this| {
// //             let _ = walk_mut_self::walk_mod_def(this, node);
// //             Ok(())
// //         })
// //     }

// //     ast_visitor_mut_self_default_impl!(
// //         hiding: Expr,
// //         DirectiveExpr,
// //         FnDef,
// //         Declaration,
// //         BodyBlock,
// //         TraitDef,
// //         TraitImpl,
// //         ModDef,
// //         ImplDef,
// //         Module
// //     );
// // }
