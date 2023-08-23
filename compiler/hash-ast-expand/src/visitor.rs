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
#![allow(unused)]

use std::convert::Infallible;

use hash_ast::{
    ast, ast_visitor_mut_self_default_impl,
    tree::AstTreeGenerator,
    visitor::{walk_mut, walk_mut_self, AstVisitor, AstVisitorMutSelf},
};
use hash_attrs::target::AttrTarget;
use hash_fmt::AstPrinter;
use hash_pipeline::{
    interface::CompilerOutputStream,
    settings::{AstDumpMode, CompilerSettings},
};
use hash_source::{identifier::IDENTS, SourceMap};
use hash_utils::{
    state::LightState,
    stream_writeln,
    tree_writing::{TreeNode, TreeWriter, TreeWriterConfig},
};

#[derive(Debug)]
pub struct AstExpander<'s> {
    /// The map of the current workspace sources.
    pub(crate) source_map: &'s SourceMap,

    /// The settings to the AST expansion pass.
    pub(crate) settings: &'s CompilerSettings,

    /// The current attribute target.
    pub(crate) target: LightState<AttrTarget>,

    /// The [CompilerOutputStream] that will be used to dump the AST.
    stdout: CompilerOutputStream,
}

impl<'s> AstExpander<'s> {
    /// Create a new [AstDesugaring]. Contains the [SourceMap] and the
    /// current id of the source in reference.
    pub fn new(
        source_map: &'s SourceMap,
        settings: &'s CompilerSettings,
        stdout: CompilerOutputStream,
    ) -> Self {
        Self { source_map, settings, stdout, target: LightState::new(AttrTarget::ModDef) }
    }

    pub fn with_target<T>(&mut self, target: AttrTarget, f: impl FnOnce(&mut Self) -> T) -> T {
        let old = self.target.swap(target);
        let result = f(self);
        self.target.swap(old);
        result
    }

    /// Check a macro attribute invocation based on the kind of macro that was
    /// invoked.
    pub fn check_macro_invocation(
        &mut self,
        node: &ast::MacroInvocation,
    ) -> Result<(), Infallible> {
        Ok(())
    }
}

impl<'s> AstVisitorMutSelf for AstExpander<'s> {
    type Error = Infallible;

    ast_visitor_mut_self_default_impl!(hiding:
        ExprMacroInvocation, TyMacroInvocation, PatMacroInvocation,
        ExprArg, TyArg, PatArg, EnumDefEntry, Param, MatchCase,
        MacroInvocation
    );

    type ExprMacroInvocationRet = ();

    fn visit_expr_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::ExprMacroInvocation>,
    ) -> Result<Self::ExprMacroInvocationRet, Self::Error> {
        self.with_target(AttrTarget::classify_expr(node.subject.body()), |this| {
            walk_mut_self::walk_expr_macro_invocation(this, node);
            Ok(())
        })
    }

    type TyMacroInvocationRet = ();

    fn visit_ty_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::TyMacroInvocation>,
    ) -> Result<Self::TyMacroInvocationRet, Self::Error> {
        self.with_target(AttrTarget::Ty, |this| {
            walk_mut_self::walk_ty_macro_invocation(this, node)?;
            Ok(())
        })
    }

    type PatMacroInvocationRet = ();

    fn visit_pat_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::PatMacroInvocation>,
    ) -> Result<Self::PatMacroInvocationRet, Self::Error> {
        self.with_target(AttrTarget::Pat, |this| {
            walk_mut_self::walk_pat_macro_invocation(this, node)?;
            Ok(())
        })
    }

    type PatArgRet = ();

    fn visit_pat_arg(
        &mut self,
        node: ast::AstNodeRef<ast::PatArg>,
    ) -> Result<Self::PatArgRet, Self::Error> {
        if let Some(macros) = node.body.macros.as_ref() {
            self.with_target(AttrTarget::Field, |this| walk_mut_self::walk_pat_arg(this, node))?;
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
        if let Some(macros) = node.body.macros.as_ref() {
            self.with_target(AttrTarget::EnumVariant, |this| {
                walk_mut_self::walk_enum_def_entry(this, node)
            })?;
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
        if let Some(macros) = node.body.macros.as_ref() {
            self.with_target(AttrTarget::Field, |this| walk_mut_self::walk_param(this, node))?;
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
        if let Some(macros) = node.body.macros.as_ref() {
            self.with_target(AttrTarget::MatchCase, |this| {
                walk_mut_self::walk_match_case(this, node)
            })?;
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
        if let Some(macros) = node.body.macros.as_ref() {
            self.with_target(AttrTarget::TyArg, |this| walk_mut_self::walk_ty_arg(this, node))?;
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
        if let Some(macros) = node.body.macros.as_ref() {
            self.with_target(AttrTarget::Field, |this| walk_mut_self::walk_expr_arg(this, node))?;
        } else {
            walk_mut_self::walk_expr_arg(self, node)?;
        }

        Ok(())
    }

    type MacroInvocationRet = ();

    fn visit_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::MacroInvocation>,
    ) -> Result<Self::MacroInvocationRet, Self::Error> {
        self.check_macro_invocation(node.body())
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
