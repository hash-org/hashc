#![feature(let_chains)]

use hash_ast::{
    ast::{self, walk_mut_self, AstNodeRef, AstNodes, AstVisitorMutSelf, RefKind},
    ast_visitor_mut_self_default_impl,
};
use hash_utils::state::LightState;

/// All configuration details for printing the AST, i.e. information about
/// how much indentation to use, adding semi colons, respecting spans, etc.
#[derive(Debug, Clone, Copy)]
pub struct AstPrintingConfig {
    /// The number of spaces to use when indenting various AST constructs.
    pub indentation: u8,
}

/// The AST printer, this is just a container to store the [AstPrintingConfig]
/// and implement the traversal for the AST pretty printing.
pub struct AstPrinter<'ast, T> {
    /// The current amount of indentation that needs to be
    /// used to print the current line.

    /// Output stream to write the AST to.
    fmt: &'ast mut T,

    /// The current level of the indentation.
    indentation: u8,

    /// If the traversal is currently within a declaration.
    in_declaration: LightState<bool>,

    /// If the traversal is currently within a match case, this only
    /// applies to the top-level expressions within a match case.
    in_match_case: LightState<bool>,

    /// If the traversal is currently within a body block, this only
    /// applies to the top-level expressions within a body block.
    in_body_block: LightState<bool>,

    /// Any specifics about how the AST should be printed
    config: AstPrintingConfig,
}

impl<'ast, T> AstPrinter<'ast, T>
where
    T: std::io::Write,
{
    /// Create a new AST printer with a default [AstPrintingConfig].
    pub fn new(fmt: &'ast mut T) -> Self {
        Self {
            fmt,
            indentation: 0,
            config: AstPrintingConfig { indentation: 4 },
            in_declaration: LightState::new(false),
            in_match_case: LightState::new(false),
            in_body_block: LightState::new(false),
        }
    }

    fn write_indent(&mut self) -> std::io::Result<()> {
        let indentation = " ".repeat(self.indentation as usize);
        write!(self.fmt, "{}", indentation)
    }

    /// Write a line with applied indentation.
    fn write_line(&mut self, line: impl ToString) -> std::io::Result<()> {
        self.write_indent()?;
        writeln!(self.fmt, "{}", line.to_string())
    }

    fn print_separated_collection<'k, N>(
        &mut self,
        collection: &'k AstNodes<N>,
        separator: &str,
        mut print_item: impl FnMut(&mut Self, AstNodeRef<'k, N>) -> std::io::Result<()>,
    ) -> std::io::Result<()> {
        //

        for (i, item) in collection.iter().enumerate() {
            print_item(self, item.ast_ref())?;
            if i != collection.len() - 1 { self.write_line(separator) } else { Ok(()) }?;
        }

        Ok(())
    }

    fn print_pattern_collection<'k, N>(
        &mut self,
        collection: &'k ast::AstNodes<N>,
        spread: &'k Option<ast::AstNode<ast::SpreadPat>>,
        mut print_item: impl FnMut(&mut Self, AstNodeRef<'k, N>) -> std::io::Result<()>,
    ) -> std::io::Result<()> {
        //
        let spread_pos = spread.as_ref().map(|s| s.body().position);

        for (i, item) in collection.iter().enumerate() {
            if i > 0 {
                write!(self.fmt, ", ")?;
            }

            // For the spread pattern, we just insert it into the location that it needs to
            // be in.
            if let Some(pos) = spread_pos && pos == i {
                self.visit_spread_pat(spread.as_ref().unwrap().ast_ref())?;

                if i != collection.len() - 1 {
                    write!(self.fmt, ", ")?;
                }
            }

            print_item(self, item.ast_ref())?;
        }

        Ok(())
    }

    fn enter_declaration<U>(&mut self, mut f: impl FnMut(&mut Self) -> U) -> U {
        self.in_declaration.set(true);
        let result = f(self);
        self.in_declaration.set(false);
        result
    }

    fn with_match_case<U>(&mut self, value: bool, mut f: impl FnMut(&mut Self) -> U) -> U {
        let old = self.in_match_case.get();
        self.in_match_case.set(value);
        let result = f(self);
        self.in_match_case.set(old);
        result
    }
}

impl<'ast, T> AstVisitorMutSelf for AstPrinter<'ast, T>
where
    T: std::io::Write,
{
    type Error = std::io::Error;

    type ModuleRet = ();

    fn visit_module(
        &mut self,
        node: AstNodeRef<ast::Module>,
    ) -> Result<Self::ModuleRet, Self::Error> {
        let ast::Module { contents } = node.body();

        for item in contents.iter() {
            self.visit_expr(item.ast_ref())?;
        }

        Ok(())
    }
    type AccessPatRet = ();

    fn visit_access_pat(
        &mut self,
        node: AstNodeRef<ast::AccessPat>,
    ) -> Result<Self::AccessPatRet, Self::Error> {
        let ast::AccessPat { subject, property } = node.body();

        self.visit_pat(subject.ast_ref())?;
        write!(self.fmt, "::")?;
        self.visit_name(property.ast_ref())
    }

    type TyFnCallRet = ();

    fn visit_ty_fn_call(
        &mut self,
        node: AstNodeRef<ast::TyFnCall>,
    ) -> Result<Self::TyFnCallRet, Self::Error> {
        let ast::TyFnCall { subject, args } = node.body();

        self.visit_expr(subject.ast_ref())?;
        write!(self.fmt, "<")?;
        self.print_separated_collection(args, ",", |this, arg| this.visit_ty_arg(arg))?;
        write!(self.fmt, ">")
    }

    type IfPatRet = ();

    fn visit_if_pat(
        &mut self,
        node: AstNodeRef<ast::IfPat>,
    ) -> Result<Self::IfPatRet, Self::Error> {
        let ast::IfPat { pat, condition } = node.body();

        self.visit_pat(pat.ast_ref())?;
        write!(self.fmt, " if ")?;
        self.visit_expr(condition.ast_ref())
    }

    type DeclarationRet = ();

    fn visit_declaration(
        &mut self,
        node: AstNodeRef<ast::Declaration>,
    ) -> Result<Self::DeclarationRet, Self::Error> {
        let ast::Declaration { pat, ty, value } = node.body();

        self.visit_pat(pat.ast_ref())?;

        // If there is a type on the declaration, then we need to
        // print `:` and the type.
        write!(self.fmt, " :")?;
        if let Some(ty) = ty {
            write!(self.fmt, " ")?;
            self.visit_ty(ty.ast_ref())?;
        }

        // Visit the expression
        if let Some(value) = value {
            if ty.is_some() {
                write!(self.fmt, " ")?;
            }

            write!(self.fmt, "= ")?;
            self.enter_declaration(|this| this.visit_expr(value.ast_ref()))?;
        } else {
            write!(self.fmt, ";")?;
        }

        // Only terminate the line if we are not in a body block.
        if !self.in_body_block.get() {
            writeln!(self.fmt)?;
        }

        Ok(())
    }

    type EnumDefEntryRet = ();

    fn visit_enum_def_entry(
        &mut self,
        node: AstNodeRef<ast::EnumDefEntry>,
    ) -> Result<Self::EnumDefEntryRet, Self::Error> {
        let ast::EnumDefEntry { name, fields, ty } = node.body();

        self.visit_name(name.ast_ref())?;

        if fields.len() > 0 {
            write!(self.fmt, "(")?;
            self.print_separated_collection(fields, ",", |this, field| this.visit_param(field))?;
            write!(self.fmt, ")")?;
        }

        if let Some(ty) = ty {
            write!(self.fmt, ": ")?;
            self.visit_ty(ty.ast_ref())?;
        }

        Ok(())
    }

    type WhileLoopBlockRet = ();

    fn visit_while_loop_block(
        &mut self,
        node: AstNodeRef<ast::WhileLoopBlock>,
    ) -> Result<Self::WhileLoopBlockRet, Self::Error> {
        let ast::WhileLoopBlock { condition, while_body } = node.body();

        write!(self.fmt, "while ")?;
        self.visit_expr(condition.ast_ref())?;
        write!(self.fmt, " ")?;
        self.visit_block(while_body.ast_ref())
    }

    type IfBlockRet = ();

    fn visit_if_block(
        &mut self,
        node: AstNodeRef<ast::IfBlock>,
    ) -> Result<Self::IfBlockRet, Self::Error> {
        let ast::IfBlock { clauses, otherwise } = node.body();

        self.print_separated_collection(clauses, " else", |this, clause| {
            this.visit_if_clause(clause)
        })?;

        if let Some(otherwise) = otherwise {
            write!(self.fmt, " else ")?;
            self.visit_block(otherwise.ast_ref())?;
        }

        Ok(())
    }

    type ExprRet = ();

    fn visit_expr(&mut self, node: AstNodeRef<ast::Expr>) -> Result<Self::ExprRet, Self::Error> {
        let _ = walk_mut_self::walk_expr(self, node)?;

        // @@Todo: deal with line breaks, etc.

        Ok(())
    }

    type ConstructorCallArgRet = ();

    fn visit_constructor_call_arg(
        &mut self,
        node: AstNodeRef<ast::ConstructorCallArg>,
    ) -> Result<Self::ConstructorCallArgRet, Self::Error> {
        let ast::ConstructorCallArg { name, value } = node.body();

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;
            write!(self.fmt, " = ")?;
        }

        self.visit_expr(value.ast_ref())
    }

    type IndexExprRet = ();

    fn visit_index_expr(
        &mut self,
        node: AstNodeRef<ast::IndexExpr>,
    ) -> Result<Self::IndexExprRet, Self::Error> {
        let ast::IndexExpr { subject, index_expr } = node.body();
        self.visit_expr(subject.ast_ref())?;

        write!(self.fmt, "[")?;

        // @@Todo: specify that we are inside an expression here?
        self.visit_expr(index_expr.ast_ref())?;
        write!(self.fmt, "]")
    }

    type TupleLitEntryRet = ();

    fn visit_tuple_lit_entry(
        &mut self,
        node: AstNodeRef<ast::TupleLitEntry>,
    ) -> Result<Self::TupleLitEntryRet, Self::Error> {
        let ast::TupleLitEntry { name, ty, value } = node.body();

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;

            if ty.is_some() {
                write!(self.fmt, ": ")?;
            } else {
                write!(self.fmt, " = ")?;
            }
        }

        if let Some(ty) = ty {
            self.visit_ty(ty.ast_ref())?;
            write!(self.fmt, " = ")?;
        }

        self.visit_expr(value.ast_ref())
    }

    type UnsafeExprRet = ();

    fn visit_unsafe_expr(
        &mut self,
        node: AstNodeRef<ast::UnsafeExpr>,
    ) -> Result<Self::UnsafeExprRet, Self::Error> {
        let ast::UnsafeExpr { data } = node.body();
        write!(self.fmt, "unsafe ")?;
        self.visit_expr(data.ast_ref())
    }

    type EnumDefRet = ();

    fn visit_enum_def(
        &mut self,
        node: AstNodeRef<ast::EnumDef>,
    ) -> Result<Self::EnumDefRet, Self::Error> {
        let ast::EnumDef { ty_params, entries } = node.body();

        write!(self.fmt, "enum")?;

        if ty_params.len() > 0 {
            write!(self.fmt, "<")?;
            self.print_separated_collection(ty_params, ",", |this, field| this.visit_param(field))?;
            write!(self.fmt, ">")?;
        }

        writeln!(self.fmt, "(")?;
        self.indentation += self.config.indentation;
        self.print_separated_collection(entries, ",", |this, entry| {
            this.visit_enum_def_entry(entry)
        })?;

        self.indentation -= self.config.indentation;
        writeln!(self.fmt, ")")
    }

    type TyFnRet = ();

    fn visit_ty_fn(&mut self, node: AstNodeRef<ast::TyFn>) -> Result<Self::TyFnRet, Self::Error> {
        let ast::TyFn { params, return_ty } = node.body();

        write!(self.fmt, "<")?;
        self.print_separated_collection(params, ",", |this, field| this.visit_param(field))?;
        write!(self.fmt, "> -> ")?;
        self.visit_ty(return_ty.ast_ref())
    }

    type UnaryExprRet = ();

    fn visit_unary_expr(
        &mut self,
        node: AstNodeRef<ast::UnaryExpr>,
    ) -> Result<Self::UnaryExprRet, Self::Error> {
        let ast::UnaryExpr { operator, expr } = node.body();

        write!(self.fmt, "{}", operator.body())?;
        self.visit_expr(expr.ast_ref())
    }

    type StructDefRet = ();

    fn visit_struct_def(
        &mut self,
        node: AstNodeRef<ast::StructDef>,
    ) -> Result<Self::StructDefRet, Self::Error> {
        let ast::StructDef { ty_params, fields } = node.body();

        write!(self.fmt, "struct")?;

        if ty_params.len() > 0 {
            write!(self.fmt, "<")?;
            self.print_separated_collection(ty_params, ",", |this, param| this.visit_param(param))?;

            write!(self.fmt, ">")?;
        }

        // @@Refactor this out into a separate function which deals with collections
        // that can print separators and properly wrap everything.
        writeln!(self.fmt, "(")?;
        self.indentation += self.config.indentation;
        self.print_separated_collection(fields, ",", |this, field| this.visit_param(field))?;

        self.indentation -= self.config.indentation;
        writeln!(self.fmt, ")")
    }

    type PropertyKindRet = ();

    fn visit_property_kind(
        &mut self,
        node: AstNodeRef<ast::PropertyKind>,
    ) -> Result<Self::PropertyKindRet, Self::Error> {
        match node.body() {
            ast::PropertyKind::NamedField(name) => write!(self.fmt, "{}", name),
            ast::PropertyKind::NumericField(field) => write!(self.fmt, "{}", field),
        }
    }

    type TupleTyRet = ();

    fn visit_tuple_ty(
        &mut self,
        node: AstNodeRef<ast::TupleTy>,
    ) -> Result<Self::TupleTyRet, Self::Error> {
        let ast::TupleTy { entries } = node.body();

        write!(self.fmt, "(")?;
        self.print_separated_collection(entries, ",", |this, arg| this.visit_ty_arg(arg))?;
        write!(self.fmt, ")")
    }

    type ContinueStatementRet = ();

    fn visit_continue_statement(
        &mut self,
        _: AstNodeRef<ast::ContinueStatement>,
    ) -> Result<Self::ContinueStatementRet, Self::Error> {
        write!(self.fmt, "continue")
    }

    type StrLitRet = ();

    fn visit_str_lit(
        &mut self,
        node: AstNodeRef<ast::StrLit>,
    ) -> Result<Self::StrLitRet, Self::Error> {
        write!(self.fmt, "{:?}", node.body.data)
    }

    type TraitImplRet = ();

    fn visit_trait_impl(
        &mut self,
        node: AstNodeRef<ast::TraitImpl>,
    ) -> Result<Self::TraitImplRet, Self::Error> {
        let ast::TraitImpl { ty, trait_body } = node.body();

        write!(self.fmt, "impl ")?;
        self.visit_ty(ty.ast_ref())?;

        self.indentation += self.config.indentation;

        writeln!(self.fmt, " {{")?;
        self.print_separated_collection(trait_body, ",", |this, item| this.visit_expr(item))?;
        self.write_line("}")
    }

    type ReturnStatementRet = ();

    fn visit_return_statement(
        &mut self,
        node: AstNodeRef<ast::ReturnStatement>,
    ) -> Result<Self::ReturnStatementRet, Self::Error> {
        let ast::ReturnStatement { expr } = node.body();

        write!(self.fmt, "return")?;

        if let Some(expr) = expr {
            write!(self.fmt, " ")?;
            self.visit_expr(expr.ast_ref())?;
        }

        Ok(())
    }

    type TyExprRet = ();

    fn visit_ty_expr(
        &mut self,
        node: AstNodeRef<ast::TyExpr>,
    ) -> Result<Self::TyExprRet, Self::Error> {
        let ast::TyExpr { ty } = node.body();
        self.visit_ty(ty.ast_ref())
    }

    type TuplePatRet = ();

    fn visit_tuple_pat(
        &mut self,
        node: AstNodeRef<ast::TuplePat>,
    ) -> Result<Self::TuplePatRet, Self::Error> {
        let ast::TuplePat { fields, spread } = node.body();

        write!(self.fmt, "(")?;
        self.print_pattern_collection(fields, spread, |this, field| {
            this.visit_tuple_pat_entry(field)
        })?;
        write!(self.fmt, ")")
    }

    type ParamRet = ();

    fn visit_param(&mut self, node: AstNodeRef<ast::Param>) -> Result<Self::ParamRet, Self::Error> {
        let ast::Param { name, ty, default, .. } = node.body();

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;
        }

        if let Some(ty) = ty {
            if name.is_some() {
                write!(self.fmt, ": ")?;
            }

            self.visit_ty(ty.ast_ref())?;
        }

        if let Some(default) = default {
            write!(self.fmt, " = ")?;
            self.visit_expr(default.ast_ref())?;
        }

        Ok(())
    }

    type ArrayTyRet = ();

    fn visit_array_ty(
        &mut self,
        node: AstNodeRef<ast::ArrayTy>,
    ) -> Result<Self::ArrayTyRet, Self::Error> {
        let ast::ArrayTy { len, inner } = node.body();

        write!(self.fmt, "[")?;
        self.visit_ty(inner.ast_ref())?;

        if let Some(len) = len {
            write!(self.fmt, "; ")?;
            self.visit_expr(len.ast_ref())?;
        }

        write!(self.fmt, "]")
    }

    type NamedTyRet = ();

    fn visit_named_ty(
        &mut self,
        node: AstNodeRef<ast::NamedTy>,
    ) -> Result<Self::NamedTyRet, Self::Error> {
        self.visit_name(node.body().name.ast_ref())
    }

    type BoolLitRet = ();

    fn visit_bool_lit(
        &mut self,
        node: AstNodeRef<ast::BoolLit>,
    ) -> Result<Self::BoolLitRet, Self::Error> {
        write!(self.fmt, "{}", node.body().data)
    }

    type AssignOpExprRet = ();

    fn visit_assign_op_expr(
        &mut self,
        node: AstNodeRef<ast::AssignOpExpr>,
    ) -> Result<Self::AssignOpExprRet, Self::Error> {
        let ast::AssignOpExpr { lhs, operator, rhs } = node.body();

        self.visit_expr(lhs.ast_ref())?;
        write!(self.fmt, " {}= ", operator.body())?;
        self.visit_expr(rhs.ast_ref())
    }

    type NameRet = ();

    fn visit_name(&mut self, node: AstNodeRef<ast::Name>) -> Result<Self::NameRet, Self::Error> {
        write!(self.fmt, "{}", node.body.ident)
    }

    type TyArgRet = ();

    fn visit_ty_arg(
        &mut self,
        node: AstNodeRef<ast::TyArg>,
    ) -> Result<Self::TyArgRet, Self::Error> {
        let ast::TyArg { name, ty } = node.body();

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;
            write!(self.fmt, ": ")?;
        }

        self.visit_ty(ty.ast_ref())
    }

    type DirectiveExprRet = ();

    fn visit_directive_expr(
        &mut self,
        node: AstNodeRef<ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let ast::DirectiveExpr { directives, subject } = node.body();

        for directive in directives {
            write!(self.fmt, "#")?;
            self.visit_name(directive.ast_ref())?;
            write!(self.fmt, " ")?;
        }

        self.visit_expr(subject.ast_ref())
    }

    type AssignExprRet = ();

    fn visit_assign_expr(
        &mut self,
        node: AstNodeRef<ast::AssignExpr>,
    ) -> Result<Self::AssignExprRet, Self::Error> {
        let ast::AssignExpr { lhs, rhs } = node.body();

        self.visit_expr(lhs.ast_ref())?;
        write!(self.fmt, " = ")?;
        self.visit_expr(rhs.ast_ref())
    }

    type RangePatRet = ();

    fn visit_range_pat(
        &mut self,
        node: AstNodeRef<ast::RangePat>,
    ) -> Result<Self::RangePatRet, Self::Error> {
        let ast::RangePat { end, lo, hi } = node.body();

        self.visit_lit(lo.ast_ref())?;
        write!(self.fmt, "{}", end)?;
        self.visit_lit(hi.ast_ref())
    }

    type DerefExprRet = ();

    fn visit_deref_expr(
        &mut self,
        node: AstNodeRef<ast::DerefExpr>,
    ) -> Result<Self::DerefExprRet, Self::Error> {
        let ast::DerefExpr { data } = node.body();
        write!(self.fmt, "*")?;
        self.visit_expr(data.ast_ref())
    }

    type IntLitRet = ();

    fn visit_int_lit(
        &mut self,
        node: AstNodeRef<ast::IntLit>,
    ) -> Result<Self::IntLitRet, Self::Error> {
        write!(self.fmt, "{}", node.body.value)
    }

    type ArrayPatRet = ();

    fn visit_array_pat(
        &mut self,
        node: AstNodeRef<ast::ArrayPat>,
    ) -> Result<Self::ArrayPatRet, Self::Error> {
        let ast::ArrayPat { fields, spread } = node.body();

        write!(self.fmt, "[")?;
        self.print_pattern_collection(fields, spread, |this, pat| this.visit_pat(pat))?;
        write!(self.fmt, "]")?;

        Ok(())
    }

    type TyFnDefRet = ();

    fn visit_ty_fn_def(
        &mut self,
        node: AstNodeRef<ast::TyFnDef>,
    ) -> Result<Self::TyFnDefRet, Self::Error> {
        let ast::TyFnDef { params, return_ty, ty_fn_body } = node.body();

        write!(self.fmt, "<")?;
        self.print_separated_collection(params, ",", |this, param| this.visit_param(param))?;

        write!(self.fmt, ">")?;

        if let Some(ty) = return_ty {
            write!(self.fmt, " -> ")?;
            self.visit_ty(ty.ast_ref())?;
        }

        write!(self.fmt, " => ")?;
        self.visit_expr(ty_fn_body.ast_ref())
    }

    type ArrayLitRet = ();

    fn visit_array_lit(
        &mut self,
        node: AstNodeRef<ast::ArrayLit>,
    ) -> Result<Self::ArrayLitRet, Self::Error> {
        let ast::ArrayLit { elements } = node.body();

        write!(self.fmt, "[")?;
        self.print_separated_collection(elements, ",", |this, item| this.visit_expr(item))?;
        write!(self.fmt, "]")
    }

    type CastExprRet = ();

    fn visit_cast_expr(
        &mut self,
        node: AstNodeRef<ast::CastExpr>,
    ) -> Result<Self::CastExprRet, Self::Error> {
        let ast::CastExpr { ty, expr } = node.body();
        self.visit_expr(expr.ast_ref())?;
        write!(self.fmt, " as ")?;
        self.visit_ty(ty.ast_ref())
    }

    type IfClauseRet = ();

    fn visit_if_clause(
        &mut self,
        node: AstNodeRef<ast::IfClause>,
    ) -> Result<Self::IfClauseRet, Self::Error> {
        let ast::IfClause { condition, if_body } = node.body();

        write!(self.fmt, "if ")?;
        self.visit_expr(condition.ast_ref())?;
        write!(self.fmt, " ")?;
        self.visit_block(if_body.ast_ref())
    }

    type BindingPatRet = ();

    fn visit_binding_pat(
        &mut self,
        node: AstNodeRef<ast::BindingPat>,
    ) -> Result<Self::BindingPatRet, Self::Error> {
        let ast::BindingPat { name, visibility, mutability } = node.body();

        if let Some(visibility) = visibility {
            write!(self.fmt, "{} ", visibility.body())?;
        }

        if let Some(mutability) = mutability {
            write!(self.fmt, "{} ", mutability.body())?;
        }

        write!(self.fmt, "{}", name.body())?;

        Ok(())
    }

    type FnDefRet = ();

    fn visit_fn_def(
        &mut self,
        node: AstNodeRef<ast::FnDef>,
    ) -> Result<Self::FnDefRet, Self::Error> {
        let ast::FnDef { params, return_ty, fn_body } = node.body();

        write!(self.fmt, "(")?;
        self.print_separated_collection(params, ",", |this, param| this.visit_param(param))?;
        write!(self.fmt, ")")?;

        if let Some(return_ty) = return_ty {
            write!(self.fmt, " -> ")?;
            self.visit_ty(return_ty.ast_ref())?;
        }

        write!(self.fmt, " => ")?;
        self.visit_expr(fn_body.ast_ref())
    }

    type ImportExprRet = ();

    fn visit_import_expr(
        &mut self,
        node: AstNodeRef<ast::ImportExpr>,
    ) -> Result<Self::ImportExprRet, Self::Error> {
        write!(self.fmt, "import(\"{}\")", node.body.data.path)
    }

    type TupleLitRet = ();

    fn visit_tuple_lit(
        &mut self,
        node: AstNodeRef<ast::TupleLit>,
    ) -> Result<Self::TupleLitRet, Self::Error> {
        let ast::TupleLit { elements } = node.body();

        write!(self.fmt, "(")?;
        self.print_separated_collection(elements, ",", |this, entry| {
            this.visit_tuple_lit_entry(entry)
        })?;
        write!(self.fmt, ")")
    }

    type FnTyRet = ();

    fn visit_fn_ty(&mut self, node: AstNodeRef<ast::FnTy>) -> Result<Self::FnTyRet, Self::Error> {
        let ast::FnTy { params, return_ty } = node.body();

        write!(self.fmt, "(")?;
        self.print_separated_collection(params, ",", |this, param| this.visit_ty_arg(param))?;
        write!(self.fmt, ") -> ")?;
        self.visit_ty(return_ty.ast_ref())
    }

    type SpreadPatRet = ();

    fn visit_spread_pat(
        &mut self,
        node: AstNodeRef<ast::SpreadPat>,
    ) -> Result<Self::SpreadPatRet, Self::Error> {
        write!(self.fmt, "...")?;

        if let Some(name) = node.body().name.as_ref() {
            self.visit_name(name.ast_ref())?;
        }

        Ok(())
    }

    type MergeDeclarationRet = ();

    fn visit_merge_declaration(
        &mut self,
        node: AstNodeRef<ast::MergeDeclaration>,
    ) -> Result<Self::MergeDeclarationRet, Self::Error> {
        let ast::MergeDeclaration { decl, value } = node.body();

        self.visit_expr(decl.ast_ref())?;
        write!(self.fmt, " ~= ")?;
        self.visit_expr(value.ast_ref())
    }

    type ConstructorCallExprRet = ();

    fn visit_constructor_call_expr(
        &mut self,
        node: AstNodeRef<ast::ConstructorCallExpr>,
    ) -> Result<Self::ConstructorCallExprRet, Self::Error> {
        let ast::ConstructorCallExpr { subject, args } = node.body();

        self.visit_expr(subject.ast_ref())?;

        write!(self.fmt, "(")?;
        self.print_separated_collection(args, ",", |this, arg| {
            this.visit_constructor_call_arg(arg)
        })?;
        write!(self.fmt, ")")
    }

    type ConstructorPatRet = ();

    fn visit_constructor_pat(
        &mut self,
        node: AstNodeRef<ast::ConstructorPat>,
    ) -> Result<Self::ConstructorPatRet, Self::Error> {
        let ast::ConstructorPat { subject, fields, spread } = node.body();
        let spread_pos = spread.as_ref().map(|s| s.body().position);

        self.visit_pat(subject.ast_ref())?;

        if fields.len() > 0 || spread_pos.is_some() {
            write!(self.fmt, "(")?;
            self.print_separated_collection(fields, ",", |this, field| {
                this.visit_tuple_pat_entry(field)
            })?;
            write!(self.fmt, ")")?;
        }

        Ok(())
    }

    type MergeTyRet = ();

    fn visit_merge_ty(
        &mut self,
        node: AstNodeRef<ast::MergeTy>,
    ) -> Result<Self::MergeTyRet, Self::Error> {
        let ast::MergeTy { lhs, rhs } = node.body();

        // @@Todo: deal with wrapping here if needed
        self.visit_ty(lhs.ast_ref())?;
        write!(self.fmt, " ~ ")?;
        self.visit_ty(rhs.ast_ref())
    }

    type ModulePatEntryRet = ();

    fn visit_module_pat_entry(
        &mut self,
        node: AstNodeRef<ast::ModulePatEntry>,
    ) -> Result<Self::ModulePatEntryRet, Self::Error> {
        let ast::ModulePatEntry { name, pat } = node.body();

        self.visit_name(name.ast_ref())?;
        write!(self.fmt, ": ")?;
        self.visit_pat(pat.ast_ref())
    }

    type ExprTyRet = ();

    fn visit_expr_ty(
        &mut self,
        node: AstNodeRef<ast::ExprTy>,
    ) -> Result<Self::ExprTyRet, Self::Error> {
        write!(self.fmt, "type ")?;
        self.visit_expr(node.body().expr.ast_ref())
    }

    type RefTyRet = ();

    fn visit_ref_ty(
        &mut self,
        node: AstNodeRef<ast::RefTy>,
    ) -> Result<Self::RefTyRet, Self::Error> {
        let ast::RefTy { mutability, kind, inner } = node.body();

        write!(self.fmt, "&")?;

        if let Some(ref_kind) = kind && *ref_kind.body() == RefKind::Raw {
            write!(self.fmt, "raw ")?;
        }

        if let Some(mutability) = mutability {
            write!(self.fmt, "{} ", mutability.body())?;
        }

        self.visit_ty(inner.ast_ref())
    }

    type AccessTyRet = ();

    fn visit_access_ty(
        &mut self,
        node: AstNodeRef<ast::AccessTy>,
    ) -> Result<Self::AccessTyRet, Self::Error> {
        let ast::AccessTy { subject, property } = node.body();

        self.visit_ty(subject.ast_ref())?;
        write!(self.fmt, "::")?;
        self.visit_name(property.ast_ref())
    }

    type TraitDefRet = ();

    fn visit_trait_def(
        &mut self,
        node: AstNodeRef<ast::TraitDef>,
    ) -> Result<Self::TraitDefRet, Self::Error> {
        let ast::TraitDef { ty_params, members } = node.body();

        write!(self.fmt, "trait")?;
        if ty_params.len() > 0 {
            write!(self.fmt, "<")?;
            self.print_separated_collection(ty_params, ",", |this, param| this.visit_param(param))?;
            write!(self.fmt, ">")?;
        }

        writeln!(self.fmt, " {{")?;
        self.indentation += self.config.indentation;

        // @@Todo: specify that it is a trait impl here, so we should indent?
        for member in members.iter() {
            self.visit_expr(member.ast_ref())?;
        }

        self.indentation -= self.config.indentation;
        self.write_line("}")
    }

    type ModulePatRet = ();

    fn visit_module_pat(
        &mut self,
        node: AstNodeRef<ast::ModulePat>,
    ) -> Result<Self::ModulePatRet, Self::Error> {
        let ast::ModulePat { fields } = node.body();

        write!(self.fmt, "{{")?;
        self.print_separated_collection(fields, ",", |this, field| {
            this.visit_module_pat_entry(field)
        })?;
        write!(self.fmt, "}}")
    }

    type BodyBlockRet = ();

    fn visit_body_block(
        &mut self,
        node: AstNodeRef<ast::BodyBlock>,
    ) -> Result<Self::BodyBlockRet, Self::Error> {
        // For the block, we have to first terminate the line with `:`, increase
        // the indentation, and close the block
        let ast::BodyBlock { statements, expr } = node.body();

        self.indentation += self.config.indentation;

        let old_body_block = self.in_body_block.get();
        self.in_body_block.set(true);

        writeln!(self.fmt, "{{")?;

        self.with_match_case(false, |this| -> Result<(), Self::Error> {
            // Visit every statement in the block.
            for statement in statements.iter() {
                this.write_indent()?;
                this.visit_expr(statement.ast_ref())?;
                writeln!(this.fmt)?;
            }

            if let Some(tail) = expr {
                this.write_indent()?;
                this.visit_expr(tail.ast_ref())?;
                writeln!(this.fmt)?;
            }

            Ok(())
        })?;

        self.indentation -= self.config.indentation;
        self.in_body_block.set(old_body_block);

        self.write_indent()?;
        write!(self.fmt, "}}")?;

        if !self.in_match_case.get() {
            self.write_line("")?;
        }

        Ok(())
    }

    type CharLitRet = ();

    fn visit_char_lit(
        &mut self,
        node: AstNodeRef<ast::CharLit>,
    ) -> Result<Self::CharLitRet, Self::Error> {
        write!(self.fmt, "'{}'", node.body.data)
    }

    type WildPatRet = ();

    fn visit_wild_pat(
        &mut self,
        _: AstNodeRef<ast::WildPat>,
    ) -> Result<Self::WildPatRet, Self::Error> {
        write!(self.fmt, "_")
    }

    type ModDefRet = ();

    fn visit_mod_def(
        &mut self,
        node: AstNodeRef<ast::ModDef>,
    ) -> Result<Self::ModDefRet, Self::Error> {
        let ast::ModDef { ty_params, block } = node.body();

        write!(self.fmt, "mod")?;

        if !ty_params.is_empty() {
            write!(self.fmt, "<")?;
            self.print_separated_collection(ty_params, ",", |this, param| this.visit_param(param))?;
            write!(self.fmt, ">")?;
        }

        write!(self.fmt, " ")?;
        self.visit_body_block(block.ast_ref())
    }

    type MatchCaseRet = ();

    fn visit_match_case(
        &mut self,
        node: AstNodeRef<ast::MatchCase>,
    ) -> Result<Self::MatchCaseRet, Self::Error> {
        let ast::MatchCase { pat, expr } = node.body();
        self.visit_pat(pat.ast_ref())?;
        write!(self.fmt, " => ")?;

        self.with_match_case(true, |this| this.visit_expr(expr.ast_ref()))
    }

    type FloatLitRet = ();

    fn visit_float_lit(
        &mut self,
        node: AstNodeRef<ast::FloatLit>,
    ) -> Result<Self::FloatLitRet, Self::Error> {
        write!(self.fmt, "{}", node.body.value)
    }

    type TuplePatEntryRet = ();

    fn visit_tuple_pat_entry(
        &mut self,
        node: AstNodeRef<ast::TuplePatEntry>,
    ) -> Result<Self::TuplePatEntryRet, Self::Error> {
        let ast::TuplePatEntry { name, pat } = node.body();

        if let Some(name) = name {
            self.visit_name(name.ast_ref())?;
            write!(self.fmt, ": ")?;
        }

        self.visit_pat(pat.ast_ref())
    }

    type MatchBlockRet = ();

    fn visit_match_block(
        &mut self,
        node: AstNodeRef<ast::MatchBlock>,
    ) -> Result<Self::MatchBlockRet, Self::Error> {
        let ast::MatchBlock { subject, cases, .. } = node.body();

        write!(self.fmt, "match ")?;
        self.visit_expr(subject.ast_ref())?;

        self.indentation += self.config.indentation;
        writeln!(self.fmt, " {{")?;
        self.print_separated_collection(cases, ",", |this, case| this.visit_match_case(case))?;

        self.indentation -= self.config.indentation;
        self.write_line("}")
    }

    type AccessExprRet = ();

    fn visit_access_expr(
        &mut self,
        node: AstNodeRef<ast::AccessExpr>,
    ) -> Result<Self::AccessExprRet, Self::Error> {
        let ast::AccessExpr { subject, property, kind } = node.body();
        self.visit_expr(subject.ast_ref())?;

        match kind {
            ast::AccessKind::Namespace => write!(self.fmt, "::")?,
            ast::AccessKind::Property => write!(self.fmt, ".")?,
        }

        self.visit_property_kind(property.ast_ref())
    }

    type BinaryExprRet = ();

    fn visit_binary_expr(
        &mut self,
        node: AstNodeRef<ast::BinaryExpr>,
    ) -> Result<Self::BinaryExprRet, Self::Error> {
        let ast::BinaryExpr { lhs, rhs, operator } = node.body();

        self.visit_expr(lhs.ast_ref())?;

        // @@Todo: consider line breaks here.
        write!(self.fmt, " {} ", operator.body())?;
        self.visit_expr(rhs.ast_ref())
    }

    type ImplDefRet = ();

    fn visit_impl_def(
        &mut self,
        node: AstNodeRef<ast::ImplDef>,
    ) -> Result<Self::ImplDefRet, Self::Error> {
        let ast::ImplDef { ty_params, block } = node.body();

        write!(self.fmt, "impl")?;

        if !ty_params.is_empty() {
            write!(self.fmt, "<")?;
            self.print_separated_collection(ty_params, ",", |this, param| this.visit_param(param))?;
            write!(self.fmt, ">")?;
        }

        write!(self.fmt, " ")?;
        self.visit_body_block(block.ast_ref())
    }

    type LoopBlockRet = ();

    fn visit_loop_block(
        &mut self,
        node: AstNodeRef<ast::LoopBlock>,
    ) -> Result<Self::LoopBlockRet, Self::Error> {
        write!(self.fmt, "loop ")?;
        self.visit_block(node.body().contents.ast_ref())
    }

    type UnionTyRet = ();

    fn visit_union_ty(
        &mut self,
        node: AstNodeRef<ast::UnionTy>,
    ) -> Result<Self::UnionTyRet, Self::Error> {
        let ast::UnionTy { lhs, rhs } = node.body();
        self.visit_ty(lhs.ast_ref())?;
        write!(self.fmt, " | ")?;
        self.visit_ty(rhs.ast_ref())
    }

    type ForLoopBlockRet = ();

    fn visit_for_loop_block(
        &mut self,
        node: AstNodeRef<ast::ForLoopBlock>,
    ) -> Result<Self::ForLoopBlockRet, Self::Error> {
        let ast::ForLoopBlock { pat, iterator, for_body } = node.body();

        write!(self.fmt, "for ")?;
        self.visit_pat(pat.ast_ref())?;
        write!(self.fmt, " in ")?;
        self.visit_expr(iterator.ast_ref())?;
        write!(self.fmt, " ")?;
        self.visit_block(for_body.ast_ref())
    }

    type BreakStatementRet = ();

    fn visit_break_statement(
        &mut self,
        _: AstNodeRef<ast::BreakStatement>,
    ) -> Result<Self::BreakStatementRet, Self::Error> {
        write!(self.fmt, "break")
    }

    type OrPatRet = ();

    fn visit_or_pat(
        &mut self,
        node: AstNodeRef<ast::OrPat>,
    ) -> Result<Self::OrPatRet, Self::Error> {
        let ast::OrPat { variants } = node.body();

        self.print_separated_collection(variants, " |", |this, variant| this.visit_pat(variant))?;

        Ok(())
    }

    type RefExprRet = ();

    fn visit_ref_expr(
        &mut self,
        node: AstNodeRef<ast::RefExpr>,
    ) -> Result<Self::RefExprRet, Self::Error> {
        let ast::RefExpr { inner_expr, kind, mutability } = node.body();
        write!(self.fmt, "&")?;

        if *kind == RefKind::Raw {
            write!(self.fmt, "raw ")?;
        }

        if let Some(mutability) = mutability {
            write!(self.fmt, "{} ", mutability.body())?;
        }

        self.visit_expr(inner_expr.ast_ref())
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
