//! The Hash formatter is a pretty printer for the Hash AST, it is used to
//! format the AST into a human readable format.
mod collection;
mod config;
mod state;

use collection::CollectionPrintingOptions;
use config::AstPrintingConfig;
use hash_ast::{
    ast::{self, walk_mut_self, AstVisitorMutSelf, ParamOrigin},
    ast_visitor_mut_self_default_impl,
};
use hash_token::{delimiter::Delimiter, FloatLitKind, IntLitKind};
use state::AstPrinterState;

/// The AST printer, this is just a container to store the [AstPrintingConfig]
/// and implement the traversal for the AST pretty printing.
pub struct AstPrettyPrinter<'ast, T> {
    /// Output stream to write the AST to.
    fmt: &'ast mut T,

    /// The current state of the printer.
    state: AstPrinterState,

    /// Any specifics about how the AST should be printed
    config: AstPrintingConfig,
}

impl<'ast, T> AstPrettyPrinter<'ast, T>
where
    T: std::io::Write,
{
    /// Create a new AST printer with a default [AstPrintingConfig].
    pub fn new(fmt: &'ast mut T) -> Self {
        Self {
            fmt,
            config: AstPrintingConfig { indentation: 4, max_width: 80 },
            state: AstPrinterState::default(),
        }
    }

    fn increment_indentation(&mut self) {
        self.state.indentation += self.config.indentation;
    }

    fn decrement_indentation(&mut self) {
        self.state.indentation -= self.config.indentation;
    }

    /// Write a string to the output stream.
    fn write(&mut self, contents: impl AsRef<str>) -> std::io::Result<()> {
        self.state.width += contents.as_ref().len() as u32;
        write!(self.fmt, "{}", contents.as_ref())
    }

    /// Write a line with applied indentation.
    fn terminate_line(&mut self, line: impl ToString) -> std::io::Result<()> {
        self.state.width = 0;
        writeln!(self.fmt, "{}", line.to_string())
    }

    fn indent(&mut self) -> std::io::Result<()> {
        let indentation = " ".repeat(self.state.indentation as usize);
        self.write(indentation)
    }
}

impl<'ast, T> AstVisitorMutSelf for AstPrettyPrinter<'ast, T>
where
    T: std::io::Write,
{
    type Error = std::io::Error;

    type ModuleRet = ();

    fn visit_module(
        &mut self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let ast::Module { contents, macros } = node.body();

        // Re-arrange the macros to be at the top.
        self.visit_macro_invocations(macros.ast_ref())?;

        for item in contents.iter() {
            self.visit_expr(item.ast_ref())?;
            self.terminate_line("\n")?;
        }

        Ok(())
    }
    type AccessPatRet = ();

    fn visit_access_pat(
        &mut self,
        node: ast::AstNodeRef<ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        let ast::AccessPat { subject, property } = node.body();

        self.visit_pat(subject.ast_ref())?;
        self.write("::")?;
        self.visit_name(property.ast_ref())
    }

    type TyFnCallRet = ();

    fn visit_ty_fn_call(
        &mut self,
        node: ast::AstNodeRef<ast::TyFnCall>,
    ) -> Result<Self::TyFnCallRet, Self::Error> {
        let ast::TyFnCall { subject, args } = node.body();

        self.visit_expr(subject.ast_ref())?;

        let opts = CollectionPrintingOptions::delimited(Delimiter::Angle, ", ");
        self.print_separated_collection(args, opts, |this, arg| this.visit_ty_arg(arg))
    }

    type IfPatRet = ();

    fn visit_if_pat(
        &mut self,
        node: ast::AstNodeRef<ast::IfPat>,
    ) -> Result<Self::IfPatRet, Self::Error> {
        let ast::IfPat { pat, condition } = node.body();

        self.visit_pat(pat.ast_ref())?;
        self.write(" if ")?;
        self.visit_expr(condition.ast_ref())
    }

    type DeclarationRet = ();

    fn visit_declaration(
        &mut self,
        node: ast::AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let ast::Declaration { pat, ty, value } = node.body();

        self.visit_pat(pat.ast_ref())?;

        // If there is a type on the declaration, then we need to
        // print `:` and the type.
        self.write(" :")?;
        if let Some(ty) = ty {
            self.write(" ")?;
            self.visit_ty(ty.ast_ref())?;
        }

        // Visit the expression
        if let Some(value) = value {
            if ty.is_some() {
                self.write(" ")?;
            }

            self.write("= ")?;
            self.visit_expr(value.ast_ref())
        } else {
            self.write(";")
        }
    }

    type EnumDefEntryRet = ();

    fn visit_enum_def_entry(
        &mut self,
        node: ast::AstNodeRef<ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        let ast::EnumDefEntry { name, fields, ty, macros } = node.body();

        // We have to visit the macro args first...
        if let Some(macros) = macros {
            self.visit_macro_invocations(macros.ast_ref())?;
            self.terminate_line("")?;
        }

        self.visit_name(name.ast_ref())?;

        if let Some(params) = fields {
            self.visit_params(params.ast_ref())?;
        }

        if let Some(ty) = ty {
            self.write(": ")?;
            self.visit_ty(ty.ast_ref())?;
        }

        Ok(())
    }

    type WhileLoopBlockRet = ();

    fn visit_while_loop_block(
        &mut self,
        node: ast::AstNodeRef<ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        let ast::WhileLoopBlock { condition, while_body } = node.body();

        self.write("while ")?;
        self.visit_expr(condition.ast_ref())?;
        self.write(" ")?;
        self.visit_block(while_body.ast_ref())
    }

    type IfBlockRet = ();

    fn visit_if_block(
        &mut self,
        node: ast::AstNodeRef<ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        let ast::IfBlock { clauses, otherwise } = node.body();

        let opts = CollectionPrintingOptions::separated(" else ");
        self.print_separated_collection(clauses, opts, |this, clause| {
            this.visit_if_clause(clause)
        })?;

        if let Some(otherwise) = otherwise {
            self.write(" else ")?;
            self.visit_block(otherwise.ast_ref())?;
        }

        Ok(())
    }

    type ExprRet = ();

    fn visit_expr(
        &mut self,
        node: ast::AstNodeRef<ast::Expr>,
    ) -> Result<Self::ExprRet, Self::Error> {
        let _ = walk_mut_self::walk_expr(self, node)?;

        // @@Todo: deal with line breaks, etc.

        Ok(())
    }

    type ExprArgRet = ();

    fn visit_expr_arg(
        &mut self,
        node: ast::AstNodeRef<ast::ExprArg>,
    ) -> Result<Self::ExprArgRet, Self::Error> {
        let ast::ExprArg { name, value, macros } = node.body();

        // We have to visit the macro args first...
        if let Some(macros) = macros {
            self.visit_macro_invocations(macros.ast_ref())?;
        }

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;
            self.write(" = ")?;
        }

        self.visit_expr(value.ast_ref())
    }

    type IndexExprRet = ();

    fn visit_index_expr(
        &mut self,
        node: ast::AstNodeRef<ast::IndexExpr>,
    ) -> Result<Self::IndexExprRet, Self::Error> {
        let ast::IndexExpr { subject, index_expr } = node.body();
        self.visit_expr(subject.ast_ref())?;

        self.write("[")?;
        self.visit_expr(index_expr.ast_ref())?;
        self.write("]")
    }

    type TupleLitEntryRet = ();

    fn visit_tuple_lit_entry(
        &mut self,
        node: ast::AstNodeRef<ast::TupleLitEntry>,
    ) -> Result<Self::TupleLitEntryRet, Self::Error> {
        let ast::TupleLitEntry { name, ty, value } = node.body();

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;

            if ty.is_some() {
                self.write(": ")?;
            } else {
                self.write(" = ")?;
            }
        }

        if let Some(ty) = ty {
            self.visit_ty(ty.ast_ref())?;
            self.write(" = ")?;
        }

        self.visit_expr(value.ast_ref())
    }

    type UnsafeExprRet = ();

    fn visit_unsafe_expr(
        &mut self,
        node: ast::AstNodeRef<ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error> {
        let ast::UnsafeExpr { data } = node.body();
        self.write("unsafe ")?;
        self.visit_expr(data.ast_ref())
    }

    type EnumDefRet = ();

    fn visit_enum_def(
        &mut self,
        node: ast::AstNodeRef<ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let ast::EnumDef { ty_params, entries } = node.body();

        self.write("enum")?;

        if let Some(ty_params) = ty_params {
            self.visit_ty_params(ty_params.ast_ref())?;
        }

        let mut opts = CollectionPrintingOptions::delimited(Delimiter::Paren, ", ");
        opts.indented();

        self.print_separated_collection(entries, opts, |this, entry| {
            this.visit_enum_def_entry(entry)
        })?;

        Ok(())
    }

    type TyFnTyRet = ();

    fn visit_ty_fn_ty(
        &mut self,
        node: ast::AstNodeRef<ast::TyFnTy>,
    ) -> Result<Self::TyFnTyRet, Self::Error> {
        let ast::TyFnTy { params, return_ty } = node.body();

        self.visit_ty_params(params.ast_ref())?;
        self.write(" -> ")?;
        self.visit_ty(return_ty.ast_ref())
    }

    type UnaryExprRet = ();

    fn visit_unary_expr(
        &mut self,
        node: ast::AstNodeRef<ast::UnaryExpr>,
    ) -> Result<Self::UnaryExprRet, Self::Error> {
        let ast::UnaryExpr { operator, expr } = node.body();

        self.write(format!("{}", operator.body()))?;
        self.visit_expr(expr.ast_ref())
    }

    type StructDefRet = ();

    fn visit_struct_def(
        &mut self,
        node: ast::AstNodeRef<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let ast::StructDef { ty_params, fields } = node.body();

        self.write("struct")?;
        if let Some(ty_params) = ty_params {
            self.visit_ty_params(ty_params.ast_ref())?;
        }

        self.visit_params(fields.ast_ref())
    }

    type PropertyKindRet = ();

    fn visit_property_kind(
        &mut self,
        node: ast::AstNodeRef<ast::PropertyKind>,
    ) -> Result<Self::PropertyKindRet, Self::Error> {
        match node.body() {
            ast::PropertyKind::NamedField(name) => self.write(format!("{}", name)),
            ast::PropertyKind::NumericField(field) => self.write(format!("{}", field)),
        }
    }

    type TupleTyRet = ();

    fn visit_tuple_ty(
        &mut self,
        node: ast::AstNodeRef<ast::TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        let ast::TupleTy { entries } = node.body();
        self.visit_params(entries.ast_ref())
    }

    type ContinueStatementRet = ();

    fn visit_continue_statement(
        &mut self,
        _: ast::AstNodeRef<ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        self.write("continue")
    }

    type StrLitRet = ();

    fn visit_str_lit(
        &mut self,
        node: ast::AstNodeRef<ast::StrLit>,
    ) -> Result<Self::StrLitRet, Self::Error> {
        self.write(format!("{:?}", node.body.data))
    }

    type TraitImplRet = ();

    fn visit_trait_impl(
        &mut self,
        node: ast::AstNodeRef<ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        let ast::TraitImpl { ty, trait_body } = node.body();

        self.write("impl ")?;
        self.visit_ty(ty.ast_ref())?;
        self.write(" ")?;

        let mut opts = CollectionPrintingOptions::delimited(Delimiter::Bracket, ", ");
        opts.indented().terminating_delimiters();

        self.print_separated_collection(trait_body, opts, |this, item| this.visit_expr(item))
    }

    type ReturnStatementRet = ();

    fn visit_return_statement(
        &mut self,
        node: ast::AstNodeRef<ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        let ast::ReturnStatement { expr } = node.body();

        self.write("return")?;

        if let Some(expr) = expr {
            self.write(" ")?;
            self.visit_expr(expr.ast_ref())?;
        }

        Ok(())
    }

    type TyExprRet = ();

    fn visit_ty_expr(
        &mut self,
        node: ast::AstNodeRef<ast::TyExpr>,
    ) -> Result<Self::TyExprRet, Self::Error> {
        let ast::TyExpr { ty } = node.body();
        self.visit_ty(ty.ast_ref())
    }

    type TuplePatRet = ();

    fn visit_tuple_pat(
        &mut self,
        node: ast::AstNodeRef<ast::TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        let ast::TuplePat { fields, spread } = node.body();

        self.write("(")?;
        self.print_pattern_collection(fields, spread, |this, field| this.visit_pat_arg(field))?;
        self.write(")")
    }

    type ParamsRet = ();
    fn visit_params(
        &mut self,
        node: ast::AstNodeRef<ast::Params>,
    ) -> Result<Self::TyParamsRet, Self::Error> {
        let ast::Params { params, origin } = node.body();

        // Return early if no params are specified.
        if params.is_empty() {
            return Ok(());
        }

        let mut opts = CollectionPrintingOptions::delimited(Delimiter::Paren, ", ");

        // @@HardCoded: Struct definition fields are indented.
        if *origin == ParamOrigin::Struct {
            opts.indented();
        }

        self.print_separated_collection(params, opts, |this, param| this.visit_param(param))
    }

    type ParamRet = ();

    fn visit_param(
        &mut self,
        node: ast::AstNodeRef<ast::Param>,
    ) -> Result<Self::ParamRet, Self::Error> {
        let ast::Param { name, ty, default, .. } = node.body();

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;
        }

        if let Some(ty) = ty {
            if name.is_some() {
                self.write(": ")?;
            }

            self.visit_ty(ty.ast_ref())?;
        }

        if let Some(default) = default {
            self.write(" = ")?;
            self.visit_expr(default.ast_ref())?;
        }

        Ok(())
    }

    type TyParamRet = ();

    fn visit_ty_param(
        &mut self,
        node: ast::AstNodeRef<ast::TyParam>,
    ) -> Result<Self::ParamRet, Self::Error> {
        let ast::TyParam { name, ty, default, .. } = node.body();

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;
        }

        if let Some(ty) = ty {
            if name.is_some() {
                self.write(": ")?;
            }

            self.visit_ty(ty.ast_ref())?;
        }

        if let Some(default) = default {
            self.write(" = ")?;
            self.visit_ty(default.ast_ref())?;
        }

        Ok(())
    }

    type TyParamsRet = ();
    fn visit_ty_params(
        &mut self,
        node: ast::AstNodeRef<ast::TyParams>,
    ) -> Result<Self::TyParamsRet, Self::Error> {
        let ast::TyParams { params, .. } = node.body();

        // Return early if no params are specified.
        if params.is_empty() {
            return Ok(());
        }

        let opts = CollectionPrintingOptions::delimited(Delimiter::Angle, ", ");

        self.print_separated_collection(params, opts, |this, param| this.visit_ty_param(param))
    }

    type ArrayTyRet = ();

    fn visit_array_ty(
        &mut self,
        node: ast::AstNodeRef<ast::ArrayTy>,
    ) -> Result<Self::ArrayTyRet, Self::Error> {
        let ast::ArrayTy { len, inner } = node.body();

        self.write("[")?;
        self.visit_ty(inner.ast_ref())?;

        if let Some(len) = len {
            self.write("; ")?;
            self.visit_expr(len.ast_ref())?;
        }

        self.write("]")
    }

    type NamedTyRet = ();

    fn visit_named_ty(
        &mut self,
        node: ast::AstNodeRef<ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        self.visit_name(node.body().name.ast_ref())
    }

    type BoolLitRet = ();

    fn visit_bool_lit(
        &mut self,
        node: ast::AstNodeRef<ast::BoolLit>,
    ) -> Result<Self::BoolLitRet, Self::Error> {
        self.write(format!("{}", node.body().data))
    }

    type AssignOpExprRet = ();

    fn visit_assign_op_expr(
        &mut self,
        node: ast::AstNodeRef<ast::AssignOpExpr>,
    ) -> Result<Self::AssignOpExprRet, Self::Error> {
        let ast::AssignOpExpr { lhs, operator, rhs } = node.body();

        self.visit_expr(lhs.ast_ref())?;
        self.write(format!(" {}= ", operator.body()))?;
        self.visit_expr(rhs.ast_ref())
    }

    type NameRet = ();

    fn visit_name(
        &mut self,
        node: ast::AstNodeRef<ast::Name>,
    ) -> Result<Self::NameRet, Self::Error> {
        self.write(format!("{}", node.body.ident))
    }

    type TyArgRet = ();

    fn visit_ty_arg(
        &mut self,
        node: ast::AstNodeRef<ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error> {
        let ast::TyArg { name, ty, macros } = node.body();

        // We have to visit the macro args first...
        if let Some(macros) = macros {
            self.visit_macro_invocations(macros.ast_ref())?;
        }

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;
            self.write(": ")?;
        }

        self.visit_ty(ty.ast_ref())
    }

    type AssignExprRet = ();

    fn visit_assign_expr(
        &mut self,
        node: ast::AstNodeRef<ast::AssignExpr>,
    ) -> Result<Self::AssignExprRet, Self::Error> {
        let ast::AssignExpr { lhs, rhs } = node.body();

        self.visit_expr(lhs.ast_ref())?;
        self.write(" = ")?;
        self.visit_expr(rhs.ast_ref())
    }

    type RangePatRet = ();

    fn visit_range_pat(
        &mut self,
        node: ast::AstNodeRef<ast::RangePat>,
    ) -> Result<Self::RangePatRet, Self::Error> {
        let ast::RangePat { end, lo, hi } = node.body();

        if let Some(lo) = lo {
            self.visit_lit(lo.ast_ref())?;
        }

        self.write(format!("{}", end))?;

        if let Some(hi) = hi {
            self.visit_lit(hi.ast_ref())?;
        }

        Ok(())
    }

    type DerefExprRet = ();

    fn visit_deref_expr(
        &mut self,
        node: ast::AstNodeRef<ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let ast::DerefExpr { data } = node.body();
        self.write("*")?;
        self.visit_expr(data.ast_ref())
    }

    type IntLitRet = ();

    fn visit_int_lit(
        &mut self,
        node: ast::AstNodeRef<ast::IntLit>,
    ) -> Result<Self::IntLitRet, Self::Error> {
        // We have to write the hunk, but without any spaces.
        // @@AddHunks

        if matches!(node.body.kind, IntLitKind::Suffixed(_)) {
            self.write(format!("_{}", node.body.kind))?;
        }

        Ok(())
    }

    type ArrayPatRet = ();

    fn visit_array_pat(
        &mut self,
        node: ast::AstNodeRef<ast::ArrayPat>,
    ) -> Result<Self::ArrayPatRet, Self::Error> {
        let ast::ArrayPat { fields, spread } = node.body();

        self.write("[")?;
        self.print_pattern_collection(fields, spread, |this, pat| this.visit_pat(pat))?;
        self.write("]")?;

        Ok(())
    }

    type TyFnDefRet = ();

    fn visit_ty_fn_def(
        &mut self,
        node: ast::AstNodeRef<ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let ast::TyFnDef { params, return_ty, ty_fn_body } = node.body();

        self.visit_ty_params(params.ast_ref())?;

        if let Some(ty) = return_ty {
            self.write(" -> ")?;
            self.visit_ty(ty.ast_ref())?;
        }

        self.write(" => ")?;
        self.visit_expr(ty_fn_body.ast_ref())
    }

    type ArrayLitRet = ();

    fn visit_array_lit(
        &mut self,
        node: ast::AstNodeRef<ast::ArrayLit>,
    ) -> Result<Self::ArrayLitRet, Self::Error> {
        let ast::ArrayLit { elements } = node.body();

        let opts = CollectionPrintingOptions::delimited(Delimiter::Bracket, ", ");
        self.print_separated_collection(elements, opts, |this, item| this.visit_expr(item))
    }

    type CastExprRet = ();

    fn visit_cast_expr(
        &mut self,
        node: ast::AstNodeRef<ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        let ast::CastExpr { ty, expr } = node.body();
        self.visit_expr(expr.ast_ref())?;
        self.write(" as ")?;
        self.visit_ty(ty.ast_ref())
    }

    type IfClauseRet = ();

    fn visit_if_clause(
        &mut self,
        node: ast::AstNodeRef<ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        let ast::IfClause { condition, if_body } = node.body();

        self.write("if ")?;
        self.visit_expr(condition.ast_ref())?;
        self.write(" ")?;
        self.visit_block(if_body.ast_ref())
    }

    type BindingPatRet = ();

    fn visit_binding_pat(
        &mut self,
        node: ast::AstNodeRef<ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        let ast::BindingPat { name, visibility, mutability } = node.body();

        if let Some(value) = visibility && *value.body() == ast::Visibility::Public {
            self.write("pub ")?;
        }

        if let Some(value) = mutability && *value.body() == ast::Mutability::Mutable  {
            self.write("mut ")?;
        }

        self.write(format!("{}", name.body()))?;

        Ok(())
    }

    type FnDefRet = ();

    fn visit_fn_def(
        &mut self,
        node: ast::AstNodeRef<ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        let ast::FnDef { params, return_ty, fn_body } = node.body();

        self.visit_params(params.ast_ref())?;

        if let Some(return_ty) = return_ty {
            self.write(" -> ")?;
            self.visit_ty(return_ty.ast_ref())?;
        }

        self.write(" => ")?;
        self.visit_expr(fn_body.ast_ref())
    }

    type ImportExprRet = ();

    fn visit_import_expr(
        &mut self,
        node: ast::AstNodeRef<ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        self.write(format!("import(\"{}\")", node.body.data.path))
    }

    type TupleLitRet = ();

    fn visit_tuple_lit(
        &mut self,
        node: ast::AstNodeRef<ast::TupleLit>,
    ) -> Result<Self::TupleLitRet, Self::Error> {
        let ast::TupleLit { elements } = node.body();

        let opts = CollectionPrintingOptions::delimited(Delimiter::Paren, ", ");
        self.print_separated_collection(elements, opts, |this, entry| {
            this.visit_tuple_lit_entry(entry)
        })
    }

    type FnTyRet = ();

    fn visit_fn_ty(
        &mut self,
        node: ast::AstNodeRef<ast::FnTy>,
    ) -> Result<Self::FnTyRet, Self::Error> {
        let ast::FnTy { params, return_ty } = node.body();

        self.visit_params(params.ast_ref())?;
        self.write(" -> ")?;
        self.visit_ty(return_ty.ast_ref())
    }

    type SpreadPatRet = ();

    fn visit_spread_pat(
        &mut self,
        node: ast::AstNodeRef<ast::SpreadPat>,
    ) -> Result<Self::SpreadPatRet, Self::Error> {
        self.write("...")?;

        if let Some(name) = node.body().name.as_ref() {
            self.visit_name(name.ast_ref())?;
        }

        Ok(())
    }

    type MergeDeclarationRet = ();

    fn visit_merge_declaration(
        &mut self,
        node: ast::AstNodeRef<ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        let ast::MergeDeclaration { decl, value } = node.body();

        self.visit_expr(decl.ast_ref())?;
        self.write(" ~= ")?;
        self.visit_expr(value.ast_ref())
    }

    type ConstructorCallExprRet = ();

    fn visit_constructor_call_expr(
        &mut self,
        node: ast::AstNodeRef<ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        let ast::ConstructorCallExpr { subject, args } = node.body();

        self.visit_expr(subject.ast_ref())?;

        let opts = CollectionPrintingOptions::delimited(Delimiter::Paren, ", ");
        self.print_separated_collection(args, opts, |this, arg| this.visit_expr_arg(arg))
    }

    type ConstructorPatRet = ();

    fn visit_constructor_pat(
        &mut self,
        node: ast::AstNodeRef<ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        let ast::ConstructorPat { subject, fields, spread } = node.body();
        let spread_pos = spread.as_ref().map(|s| s.body().position);

        self.visit_pat(subject.ast_ref())?;

        if fields.len() > 0 || spread_pos.is_some() {
            let opts = CollectionPrintingOptions::delimited(Delimiter::Paren, ", ");
            self.print_separated_collection(fields, opts, |this, field| this.visit_pat_arg(field))?;
        }

        Ok(())
    }

    type MergeTyRet = ();

    fn visit_merge_ty(
        &mut self,
        node: ast::AstNodeRef<ast::MergeTy>,
    ) -> Result<Self::MergeTyRet, Self::Error> {
        let ast::MergeTy { lhs, rhs } = node.body();

        // @@Todo: deal with wrapping here if needed
        self.visit_ty(lhs.ast_ref())?;
        self.write(" ~ ")?;
        self.visit_ty(rhs.ast_ref())
    }

    type ModulePatEntryRet = ();

    fn visit_module_pat_entry(
        &mut self,
        node: ast::AstNodeRef<ast::ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error> {
        let ast::ModulePatEntry { name, pat } = node.body();

        self.visit_name(name.ast_ref())?;
        self.write(": ")?;
        self.visit_pat(pat.ast_ref())
    }

    type ExprTyRet = ();

    fn visit_expr_ty(
        &mut self,
        node: ast::AstNodeRef<ast::ExprTy>,
    ) -> Result<Self::ExprTyRet, Self::Error> {
        self.write("type ")?;
        self.visit_expr(node.body().expr.ast_ref())
    }

    type RefTyRet = ();

    fn visit_ref_ty(
        &mut self,
        node: ast::AstNodeRef<ast::RefTy>,
    ) -> Result<Self::RefTyRet, Self::Error> {
        let ast::RefTy { mutability, kind, inner } = node.body();

        self.write("&")?;

        if let Some(ref_kind) = kind && *ref_kind.body() == ast::RefKind::Raw {
            self.write("raw ")?;
        }

        if let Some(mutability) = mutability {
            self.write(format!("{} ", mutability.body()))?;
        }

        self.visit_ty(inner.ast_ref())
    }

    type AccessTyRet = ();

    fn visit_access_ty(
        &mut self,
        node: ast::AstNodeRef<ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        let ast::AccessTy { subject, property } = node.body();

        self.visit_ty(subject.ast_ref())?;
        self.write("::")?;
        self.visit_name(property.ast_ref())
    }

    type TraitDefRet = ();

    fn visit_trait_def(
        &mut self,
        node: ast::AstNodeRef<ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let ast::TraitDef { ty_params, members } = node.body();

        self.write("trait")?;

        if let Some(ty_params) = ty_params {
            self.visit_ty_params(ty_params.ast_ref())?;
        }

        let mut opts = CollectionPrintingOptions::delimited(Delimiter::Brace, "\n");
        opts.indented().per_line().terminating_delimiters();

        self.print_separated_collection(members, opts, |this, member| this.visit_expr(member))
    }

    type ModulePatRet = ();

    fn visit_module_pat(
        &mut self,
        node: ast::AstNodeRef<ast::ModulePat>,
    ) -> Result<Self::ModulePatRet, Self::Error> {
        let ast::ModulePat { fields } = node.body();
        let opts = CollectionPrintingOptions::delimited(Delimiter::Brace, ", ");

        self.print_separated_collection(fields, opts, |this, field| {
            this.visit_module_pat_entry(field)
        })
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &mut self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        // For the block, we have to first terminate the line with `:`, increase
        // the indentation, and close the block
        let ast::BodyBlock { statements, expr } = node.body();

        self.increment_indentation();
        self.terminate_line("{")?;

        // Visit every statement in the block.
        for statement in statements.iter() {
            self.indent()?;
            self.visit_expr(statement.ast_ref())?;
            self.terminate_line("")?;
        }

        if let Some(tail) = expr {
            self.indent()?;
            self.visit_expr(tail.ast_ref())?;
            self.terminate_line("")?;
        }

        self.decrement_indentation();
        self.indent()?;
        self.write("}")
    }

    type CharLitRet = ();

    fn visit_char_lit(
        &mut self,
        node: ast::AstNodeRef<ast::CharLit>,
    ) -> Result<Self::CharLitRet, Self::Error> {
        self.write(format!("'{}'", node.body.data))
    }

    type WildPatRet = ();

    fn visit_wild_pat(
        &mut self,
        _: ast::AstNodeRef<ast::WildPat>,
    ) -> Result<Self::WildPatRet, Self::Error> {
        self.write("_")
    }

    type ModDefRet = ();

    fn visit_mod_def(
        &mut self,
        node: ast::AstNodeRef<ast::ModDef>,
    ) -> Result<Self::ModDefRet, Self::Error> {
        let ast::ModDef { ty_params, block } = node.body();

        self.write("mod")?;

        if let Some(ty_params) = ty_params {
            self.visit_ty_params(ty_params.ast_ref())?;
        }

        self.write(" ")?;
        self.visit_body_block(block.ast_ref())
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &mut self,
        node: ast::AstNodeRef<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let ast::MatchCase { pat, expr, macros } = node.body();

        // We have to visit the macro args first...
        if let Some(macros) = macros {
            self.visit_macro_invocations(macros.ast_ref())?;
        }

        self.visit_pat(pat.ast_ref())?;
        self.write(" => ")?;

        self.visit_expr(expr.ast_ref())
    }

    type FloatLitRet = ();

    fn visit_float_lit(
        &mut self,
        node: ast::AstNodeRef<ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error> {
        // We have to write the hunk, but without any spaces.
        // @@AddHunks

        if matches!(node.body.kind, FloatLitKind::Suffixed(_)) {
            self.write(format!("_{}", node.body.kind))?;
        }

        Ok(())
    }

    type PatArgRet = ();

    fn visit_pat_arg(
        &mut self,
        node: ast::AstNodeRef<ast::PatArg>,
    ) -> Result<Self::PatArgRet, Self::Error> {
        let ast::PatArg { name, pat, macros } = node.body();

        // We have to visit the macro args first...
        if let Some(macros) = macros {
            self.visit_macro_invocations(macros.ast_ref())?;
        }

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;
            self.write(": ")?;
        }

        self.visit_pat(pat.ast_ref())
    }

    type MatchBlockRet = ();

    fn visit_match_block(
        &mut self,
        node: ast::AstNodeRef<ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let ast::MatchBlock { subject, cases, .. } = node.body();

        self.write("match ")?;
        self.visit_expr(subject.ast_ref())?;
        self.write(" ")?;

        let mut opts = CollectionPrintingOptions::delimited(Delimiter::Brace, ", ");
        opts.per_line().terminating_delimiters().indented();

        self.print_separated_collection(cases, opts, |this, case| this.visit_match_case(case))
    }

    type AccessExprRet = ();

    fn visit_access_expr(
        &mut self,
        node: ast::AstNodeRef<ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        let ast::AccessExpr { subject, property, kind } = node.body();
        self.visit_expr(subject.ast_ref())?;

        match kind {
            ast::AccessKind::Namespace => self.write("::")?,
            ast::AccessKind::Property => self.write(".")?,
        }

        self.visit_property_kind(property.ast_ref())
    }

    type BinaryExprRet = ();

    fn visit_binary_expr(
        &mut self,
        node: ast::AstNodeRef<ast::BinaryExpr>,
    ) -> Result<Self::BinaryExprRet, Self::Error> {
        let ast::BinaryExpr { lhs, rhs, operator } = node.body();

        self.visit_expr(lhs.ast_ref())?;

        // @@Todo: consider line breaks here.
        self.write(format!(" {} ", operator.body()))?;
        self.visit_expr(rhs.ast_ref())
    }

    type ImplDefRet = ();

    fn visit_impl_def(
        &mut self,
        node: ast::AstNodeRef<ast::ImplDef>,
    ) -> Result<Self::ImplDefRet, Self::Error> {
        let ast::ImplDef { ty_params, block } = node.body();

        self.write("impl")?;

        if let Some(ty_params) = ty_params {
            self.visit_ty_params(ty_params.ast_ref())?;
        }

        self.write(" ")?;
        self.visit_body_block(block.ast_ref())
    }

    type LoopBlockRet = ();

    fn visit_loop_block(
        &mut self,
        node: ast::AstNodeRef<ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        self.write("loop ")?;
        self.visit_block(node.body().contents.ast_ref())
    }

    type UnionTyRet = ();

    fn visit_union_ty(
        &mut self,
        node: ast::AstNodeRef<ast::UnionTy>,
    ) -> Result<Self::UnionTyRet, Self::Error> {
        let ast::UnionTy { lhs, rhs } = node.body();
        self.visit_ty(lhs.ast_ref())?;
        self.write(" | ")?;
        self.visit_ty(rhs.ast_ref())
    }

    type ForLoopBlockRet = ();

    fn visit_for_loop_block(
        &mut self,
        node: ast::AstNodeRef<ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        let ast::ForLoopBlock { pat, iterator, for_body } = node.body();

        self.write("for ")?;
        self.visit_pat(pat.ast_ref())?;
        self.write(" in ")?;
        self.visit_expr(iterator.ast_ref())?;
        self.write(" ")?;
        self.visit_block(for_body.ast_ref())
    }

    type BreakStatementRet = ();

    fn visit_break_statement(
        &mut self,
        _: ast::AstNodeRef<ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        self.write("break")
    }

    type OrPatRet = ();

    fn visit_or_pat(
        &mut self,
        node: ast::AstNodeRef<ast::OrPat>,
    ) -> Result<Self::OrPatRet, Self::Error> {
        let ast::OrPat { variants } = node.body();

        let opts = CollectionPrintingOptions::separated(" | ");
        self.print_separated_collection(variants, opts, |this, variant| this.visit_pat(variant))?;

        Ok(())
    }

    type RefExprRet = ();

    fn visit_ref_expr(
        &mut self,
        node: ast::AstNodeRef<ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let ast::RefExpr { inner_expr, kind, mutability } = node.body();
        self.write("&")?;

        if *kind == ast::RefKind::Raw {
            self.write("raw ")?;
        }

        if let Some(value) = mutability && *value.body() == ast::Mutability::Mutable {
            self.write("mut ")?;
        }

        self.visit_expr(inner_expr.ast_ref())
    }

    type MacroInvocationArgRet = ();

    fn visit_macro_invocation_arg(
        &mut self,
        node: ast::AstNodeRef<ast::MacroInvocationArg>,
    ) -> Result<Self::MacroInvocationArgRet, Self::Error> {
        let ast::MacroInvocationArg { name, value } = node.body();

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;
            self.write(" = ")?;
        }

        self.visit_expr(value.ast_ref())
    }

    type MacroInvocationArgsRet = ();

    fn visit_macro_invocation_args(
        &mut self,
        node: ast::AstNodeRef<ast::MacroInvocationArgs>,
    ) -> Result<Self::MacroInvocationArgsRet, Self::Error> {
        let ast::MacroInvocationArgs { args } = node.body();

        // This shouldn't really happen, but in case it does, we can just return
        // early.
        if args.is_empty() {
            return Ok(());
        }

        let opts = CollectionPrintingOptions::delimited(Delimiter::Paren, ", ");
        self.print_separated_collection(args, opts, |this, arg| {
            this.visit_macro_invocation_arg(arg)
        })
    }

    type MacroInvocationRet = ();

    fn visit_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::MacroInvocation>,
    ) -> Result<Self::MacroInvocationRet, Self::Error> {
        let ast::MacroInvocation { name, args } = node.body();

        self.visit_name(name.ast_ref())?;

        if let Some(args) = args {
            self.visit_macro_invocation_args(args.ast_ref())?;
        }

        Ok(())
    }

    type MacroInvocationsRet = ();

    fn visit_macro_invocations(
        &mut self,
        node: ast::AstNodeRef<ast::MacroInvocations>,
    ) -> Result<Self::MacroInvocationsRet, Self::Error> {
        let ast::MacroInvocations { invocations } = node.body();

        // This shouldn't really happen, but in case it does, we can just return
        // early.
        if invocations.is_empty() {
            return Ok(());
        }

        // Start of the
        self.write("#")?;

        if invocations.len() == 1 && invocations[0].args.is_none() {
            return self.visit_name(invocations[0].name.ast_ref());
        }

        let opts = CollectionPrintingOptions::delimited(Delimiter::Bracket, ", ");
        self.print_separated_collection(invocations, opts, |this, arg| {
            this.visit_macro_invocation(arg)
        })
    }

    type TyMacroInvocationRet = ();

    fn visit_ty_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::TyMacroInvocation>,
    ) -> Result<Self::TyMacroInvocationRet, Self::Error> {
        let ast::TyMacroInvocation { subject, macros } = node.body();

        if !macros.is_empty() {
            self.visit_macro_invocations(macros.ast_ref())?;
        }

        self.visit_ty(subject.ast_ref())
    }

    type PatMacroInvocationRet = ();

    fn visit_pat_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::PatMacroInvocation>,
    ) -> Result<Self::PatMacroInvocationRet, Self::Error> {
        let ast::PatMacroInvocation { subject, macros } = node.body();

        if !macros.is_empty() {
            self.visit_macro_invocations(macros.ast_ref())?;
        }

        self.visit_pat(subject.ast_ref())
    }

    type ExprMacroInvocationRet = ();

    fn visit_expr_macro_invocation(
        &mut self,
        node: ast::AstNodeRef<ast::ExprMacroInvocation>,
    ) -> Result<Self::ExprMacroInvocationRet, Self::Error> {
        let ast::ExprMacroInvocation { subject, macros } = node.body();

        if !macros.is_empty() {
            self.visit_macro_invocations(macros.ast_ref())?;
            self.terminate_line("")?;
        }

        self.visit_expr(subject.ast_ref())
    }

    ast_visitor_mut_self_default_impl!(
        Ty,
        Pat,
        Visibility,
        AccessKind,
        Mutability,
        RefKind,
        UnOp,
        BinOp,
        Lit,
        LitPat,
        LitExpr,
        BlockExpr,
        VariableExpr,
        Block,
        Import,
    );
}
