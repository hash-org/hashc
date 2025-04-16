//! This defines the Hash AST expansion pass. This pass is responsible for
//! dealing with all macro invocations, and performing various transformations
//! on the AST based on the kind of macro that was invoked. Specifically, this
//! pass will:
//!
//! - Deal with all `#[...]` invocations which set attributes on their subjects.
//!   The attributes are registered in the [`attr_store()`] which can then be
//!   later accessed by various other passes which need to know about the
//!   attributes.  Dealing with attributes also means that the pass will check
//!   that all applied attributes exist (if not a warning is emitted) and that
//!   they are applied to the correct kind of AST item. However, this pass is
//!   not responsible for checking that a specific kind of attribute has a sane
//!   or valid value, this is up to the pass that is responsible or cares about
//!   the attribute to check.
//!
//! - @@Future: Perform expansions on macro invocations. Depending on whether
//!   this is an AST level macro or a token level macro, the expansion will be
//!   different.

use std::convert::Infallible;

use hash_ast::{
    ast, ast_visitor_mut_self_default_impl,
    visitor::{AstVisitorMutSelf, walk_mut_self},
};
use hash_ast_utils::attr::AttrNode;
use hash_attrs::checks::AttrChecker;
use hash_pipeline::settings::CompilerSettings;
use hash_reporting::diagnostic::DiagnosticsMut;
use hash_source::SourceId;
use hash_target::data_layout::TargetDataLayout;
use hash_utils::crossbeam_channel::Sender;

use crate::diagnostics::{
    ExpansionDiagnostic, ExpansionDiagnostics, error::ExpansionError, warning::ExpansionWarning,
};

pub struct AstExpander<'ctx> {
    /// An attribute checker, used to check that attributes are being applied
    /// correctly. This is for checks that are more specific to the context
    /// of the attribute, and not just the attribute itself.
    pub checker: AttrChecker<'ctx>,

    /// A reference to the compiler settings.
    pub settings: &'ctx CompilerSettings,

    /// Any diagnostics that have been emitted during the expansion stage.
    pub(crate) diagnostics: ExpansionDiagnostics,
}

impl<'ctx> AstExpander<'ctx> {
    /// Create a new [AstExpander]. Contains the [SourceMap] and the
    /// current id of the source in reference.
    pub fn new(
        id: SourceId,
        settings: &'ctx CompilerSettings,
        data_layout: &'ctx TargetDataLayout,
    ) -> Self {
        Self {
            settings,
            diagnostics: ExpansionDiagnostics::new(),
            checker: AttrChecker::new(id, data_layout),
        }
    }

    pub(crate) fn add_error(&mut self, error: impl Into<ExpansionError>) {
        self.diagnostics.store.add_error(error.into());
    }

    pub(crate) fn add_warning(&mut self, warning: impl Into<ExpansionWarning>) {
        self.diagnostics.store.add_warning(warning.into());
    }

    /// Emit all diagnostics that have been collected during the expansion
    /// stage.
    pub(crate) fn emit_diagnostics_to(self, sender: &Sender<ExpansionDiagnostic>) {
        self.diagnostics.store.warnings.into_iter().for_each(|d| sender.send(d.into()).unwrap());
        self.diagnostics.store.errors.into_iter().for_each(|d| sender.send(d.into()).unwrap());
    }
}

impl AstVisitorMutSelf for AstExpander<'_> {
    type Error = Infallible;

    ast_visitor_mut_self_default_impl!(hiding:
        ExprMacroInvocation, TyMacroInvocation, PatMacroInvocation,
        ExprArg, TyArg, PatArg, EnumDefEntry, Param, MatchCase, Module
    );

    type ExprMacroInvocationRet = ();

    fn visit_expr_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::ExprMacroInvocation>,
    ) -> Result<Self::ExprMacroInvocationRet, Self::Error> {
        let target = AttrNode::from_expr(node.subject.ast_ref());
        self.check_macro_invocations(node.macros.ast_ref(), target);

        walk_mut_self::walk_expr_macro_invocation(self, node)?;
        Ok(())
    }

    type TyMacroInvocationRet = ();

    fn visit_ty_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::TyMacroInvocation>,
    ) -> Result<Self::TyMacroInvocationRet, Self::Error> {
        self.check_macro_invocations(node.macros.ast_ref(), node.subject.ast_ref().into());

        walk_mut_self::walk_ty_macro_invocation(self, node)?;
        Ok(())
    }

    type PatMacroInvocationRet = ();

    fn visit_pat_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::PatMacroInvocation>,
    ) -> Result<Self::PatMacroInvocationRet, Self::Error> {
        self.check_macro_invocations(node.macros.ast_ref(), node.subject.ast_ref().into());

        walk_mut_self::walk_pat_macro_invocation(self, node)?;
        Ok(())
    }

    type PatArgRet = ();

    fn visit_pat_arg(
        &mut self,
        node: ast::AstNodeRef<ast::PatArg>,
    ) -> Result<Self::PatArgRet, Self::Error> {
        if let Some(macros) = node.body.macros.as_ref() {
            self.check_macro_invocations(macros.ast_ref(), node.into());
        }

        walk_mut_self::walk_pat_arg(self, node)?;
        Ok(())
    }

    type EnumDefEntryRet = ();

    fn visit_enum_def_entry(
        &mut self,
        node: ast::AstNodeRef<ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        if let Some(macros) = node.body.macros.as_ref() {
            self.check_macro_invocations(macros.ast_ref(), node.into());
        }

        walk_mut_self::walk_enum_def_entry(self, node)?;
        Ok(())
    }

    type ParamRet = ();

    fn visit_param(
        &mut self,
        node: ast::AstNodeRef<ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error> {
        if let Some(macros) = node.body.macros.as_ref() {
            self.check_macro_invocations(macros.ast_ref(), node.into());
        }

        walk_mut_self::walk_param(self, node)?;
        Ok(())
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &mut self,
        node: ast::AstNodeRef<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        if let Some(macros) = node.body.macros.as_ref() {
            self.check_macro_invocations(macros.ast_ref(), node.into());
        }

        walk_mut_self::walk_match_case(self, node)?;
        Ok(())
    }

    type TyArgRet = ();

    fn visit_ty_arg(
        &mut self,
        node: ast::AstNodeRef<ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error> {
        if let Some(macros) = node.body.macros.as_ref() {
            self.check_macro_invocations(macros.ast_ref(), node.into());
        }

        walk_mut_self::walk_ty_arg(self, node)?;
        Ok(())
    }

    type ExprArgRet = ();

    fn visit_expr_arg(
        &mut self,
        node: ast::AstNodeRef<ast::ExprArg>,
    ) -> Result<Self::ExprArgRet, Self::Error> {
        if let Some(macros) = node.body.macros.as_ref() {
            self.check_macro_invocations(macros.ast_ref(), node.into());
        }
        walk_mut_self::walk_expr_arg(self, node)?;
        Ok(())
    }

    type ModuleRet = ();

    fn visit_module(
        &mut self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        self.check_macro_invocations(node.macros.ast_ref(), node.into());
        Ok(())
    }
}
