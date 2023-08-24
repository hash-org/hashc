//! This defines the Hash AST expansion pass. This pass is responsible for
//! dealing with all macro invocations, and performing various transformations
//! on the AST based on the kind of macro that was invoked. Specifically, this
//! pass will:
//!
//! - Deal with all `#[attr(...)]` invocations which set attributes on their
//!   subjects. The attributes are registered in the `ATTRIBUTE_MAP` which can
//!   then be later accessed by various other passes which need to know about
//!   the attributes.  Dealing with attributes also means that the pass will
//!   check that all applied attributes exist (if not a warning is emitted) and
//!   that they are applied to the correct kind of AST item. However, this pass
//!   is not responsible for checking that a specific kind of attribute has a
//!   sane or valid value, this is up to the pass that is responsible or cares
//!   about the attribute to check.
//!
//! - @@Future: Perform expansions on macro invocations. Depending on whether
//!   this is an AST level macro or a token level macro, the expansion will be
//!   different.

use std::convert::Infallible;

use hash_ast::{
    ast, ast_visitor_mut_self_default_impl,
    visitor::{walk_mut_self, AstVisitorMutSelf},
};
use hash_attrs::{
    attr::{attr_store, Attrs},
    target::AttrTarget,
};
use hash_storage::store::PartialStore;
use hash_utils::{crossbeam_channel::Sender, state::LightState};

use crate::{
    attr::ApplicationTarget,
    diagnostics::{ExpansionDiagnostic, ExpansionDiagnostics},
};

pub struct AstExpander {
    /// The current attribute target.
    pub(crate) target: LightState<ApplicationTarget>,

    /// Any diagnostics that have been emitted during the expansion stage.
    pub diagnostics: ExpansionDiagnostics,
}

impl AstExpander {
    /// Create a new [AstExpander]. Contains the [SourceMap] and the
    /// current id of the source in reference.
    pub fn new() -> Self {
        Self {
            target: LightState::new(ApplicationTarget::default()),
            diagnostics: ExpansionDiagnostics::new(),
        }
    }

    /// Emit all diagnostics that have been collected during the expansion
    /// stage.
    pub(crate) fn emit_diagnostics_to(self, sender: &Sender<ExpansionDiagnostic>) {
        self.diagnostics.errors.into_iter().for_each(|d| sender.send(d.into()).unwrap());
    }
}

impl AstVisitorMutSelf for AstExpander {
    type Error = Infallible;

    ast_visitor_mut_self_default_impl!(hiding:
        ExprMacroInvocation, TyMacroInvocation, PatMacroInvocation,
        ExprArg, TyArg, PatArg, EnumDefEntry, Param, MatchCase,
        MacroInvocations
    );

    type ExprMacroInvocationRet = ();

    fn visit_expr_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::ExprMacroInvocation>,
    ) -> Result<Self::ExprMacroInvocationRet, Self::Error> {
        let target = ApplicationTarget::new(
            AttrTarget::classify_expr(node.subject.body()),
            node.subject.id(),
        );

        self.with_target(target, |this| {
            walk_mut_self::walk_expr_macro_invocation(this, node)?;
            Ok(())
        })
    }

    type TyMacroInvocationRet = ();

    fn visit_ty_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::TyMacroInvocation>,
    ) -> Result<Self::TyMacroInvocationRet, Self::Error> {
        let target = ApplicationTarget::new(AttrTarget::Ty, node.subject.id());
        self.with_target(target, |this| {
            walk_mut_self::walk_ty_macro_invocation(this, node)?;
            Ok(())
        })
    }

    type PatMacroInvocationRet = ();

    fn visit_pat_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::PatMacroInvocation>,
    ) -> Result<Self::PatMacroInvocationRet, Self::Error> {
        let target = ApplicationTarget::new(AttrTarget::Pat, node.subject.id());
        self.with_target(target, |this| {
            walk_mut_self::walk_pat_macro_invocation(this, node)?;
            Ok(())
        })
    }

    type PatArgRet = ();

    fn visit_pat_arg(
        &mut self,
        node: ast::AstNodeRef<ast::PatArg>,
    ) -> Result<Self::PatArgRet, Self::Error> {
        if node.body.macros.as_ref().is_some() {
            let target = ApplicationTarget::new(AttrTarget::Field, node.id());
            self.with_target(target, |this| walk_mut_self::walk_pat_arg(this, node))?;
        } else {
            walk_mut_self::walk_pat_arg(self, node)?;
        }

        Ok(())
    }

    type EnumDefEntryRet = ();

    fn visit_enum_def_entry(
        &mut self,
        node: ast::AstNodeRef<ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        if node.body.macros.as_ref().is_some() {
            let target = ApplicationTarget::new(AttrTarget::EnumVariant, node.id());
            self.with_target(target, |this| walk_mut_self::walk_enum_def_entry(this, node))?;
        } else {
            walk_mut_self::walk_enum_def_entry(self, node)?;
        }

        Ok(())
    }

    type ParamRet = ();

    fn visit_param(
        &mut self,
        node: ast::AstNodeRef<ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error> {
        if node.body.macros.as_ref().is_some() {
            let target = ApplicationTarget::new(AttrTarget::Field, node.id());
            self.with_target(target, |this| walk_mut_self::walk_param(this, node))?;
        } else {
            walk_mut_self::walk_param(self, node)?;
        }

        Ok(())
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &mut self,
        node: ast::AstNodeRef<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        if node.body.macros.as_ref().is_some() {
            let target = ApplicationTarget::new(AttrTarget::MatchCase, node.id());
            self.with_target(target, |this| walk_mut_self::walk_match_case(this, node))?;
        } else {
            walk_mut_self::walk_match_case(self, node)?;
        }

        Ok(())
    }

    type TyArgRet = ();

    fn visit_ty_arg(
        &mut self,
        node: ast::AstNodeRef<ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error> {
        if node.body.macros.as_ref().is_some() {
            let target = ApplicationTarget::new(AttrTarget::TyArg, node.id());
            self.with_target(target, |this| walk_mut_self::walk_ty_arg(this, node))?;
        } else {
            walk_mut_self::walk_ty_arg(self, node)?;
        }

        Ok(())
    }

    type ExprArgRet = ();

    fn visit_expr_arg(
        &mut self,
        node: ast::AstNodeRef<ast::ExprArg>,
    ) -> Result<Self::ExprArgRet, Self::Error> {
        if node.body.macros.as_ref().is_some() {
            let target = ApplicationTarget::new(AttrTarget::Field, node.id());
            self.with_target(target, |this| walk_mut_self::walk_expr_arg(this, node))?;
        } else {
            walk_mut_self::walk_expr_arg(self, node)?;
        }

        Ok(())
    }

    type MacroInvocationsRet = ();

    fn visit_macro_invocations(
        &mut self,
        node: ast::AstNodeRef<ast::MacroInvocations>,
    ) -> Result<Self::MacroInvocationsRet, Self::Error> {
        // If the macro invocation is correct, then we can append
        // all of the attributes that are being applied onto the
        // the target.
        let mut attrs = Attrs::with_capacity(node.body.invocations.len());

        for invocation in node.invocations.iter() {
            if let Some(attr) = self.try_create_attr_from_macro(invocation.ast_ref()) {
                attrs.add_attr(attr);
            }
        }

        attr_store().insert(node.id(), attrs);
        Ok(())
    }

    // type DirectiveExprRet = ();
    // fn visit_directive_expr(
    //     &mut self,
    //     node: hash_ast::ast::AstNodeRef<hash_ast::ast::DirectiveExpr>,
    // ) -> Result<Self::DirectiveExprRet, Self::Error> { let _ =
    //   walk_mut_self::walk_directive_expr(self, node);

    //     let mut write_tree = |index| {
    //         let ast_settings = self.settings.ast_settings();

    //         // We want to get the total span of the subject, so we must
    //         // include the span of the directives that come after the `dump_ast`
    // directive.         let directive_span = if let Some(directive) =
    // node.directives.get(index + 1) {             let directive:
    // &AstNode<Name> = directive; // @@RustBug: for some reason it can't infer the
    // type here, maybe `smallvec`
    // // related?             directive.span().join(node.subject.span())
    //         } else {
    //             node.subject.span()
    //         };

    //         stream_writeln!(
    //             self.stdout,
    //             "AST dump for {}",
    //             self.source_map.fmt_location(directive_span)
    //         );

    //         match ast_settings.dump_mode {
    //             AstDumpMode::Pretty => {
    //                 let mut printer = AstPrinter::new(&mut self.stdout);
    //                 printer.visit_expr(node.subject.ast_ref()).unwrap();

    //                 // @@Hack: terminate the line with a newline.
    //                 stream_writeln!(self.stdout, "");
    //             }
    //             AstDumpMode::Tree => {
    //                 let mut tree =
    // AstTreeGenerator.visit_expr(node.subject.ast_ref()).unwrap();

    //                 // Since this might be a non-singular directive, we also
    // might                 // need to wrap the tree in a any of the directives
    // that were specified                 // after the `dump_ast` directive.
    //                 for directive in node.directives.iter().skip(index + 1).rev()
    // {                     tree = TreeNode::branch(
    //                         format!("directive \"{}\"", directive.ident),
    //                         vec![tree],
    //                     );
    //                 }

    //                 stream_writeln!(
    //                     self.stdout,
    //                     "{}",
    //                     TreeWriter::new_with_config(
    //                         &tree,
    //
    // TreeWriterConfig::from_character_set(self.settings.character_set)
    //                     )
    //                 );
    //             }
    //         }
    //     };

    //     // for the `dump_ast` directive, we essentially "dump" the generated tree
    //     // that the parser created. We emit this tree regardless of whether or
    // not     // there will be errors later on in the compilation stage.
    //     for (index, directive) in node.directives.iter().enumerate() {
    //         if directive.is(IDENTS.dump_ast) {
    //             write_tree(index)
    //         }
    //     }

    //     Ok(())
    // }
}
