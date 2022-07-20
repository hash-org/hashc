//! Contains utilities to format types for displaying in error messages and
//! debug output.

use crate::storage::{
    primitives::{
        AccessOp, ArgsId, EnumDef, Level0Term, Level1Term, Level2Term, Level3Term, LitTerm,
        MemberData, ModDefId, ModDefOrigin, ModPat, Mutability, NominalDef, NominalDefId, ParamsId,
        Pat, PatId, PatParamsId, ScopeId, StructDef, Sub, SubSubject, Term, TermId, TrtDefId,
        UnresolvedTerm, Visibility,
    },
    GlobalStorage,
};
use core::fmt;
use std::{cell::Cell, fmt::Display, rc::Rc};

// Contains various options regarding the formatting of terms.
#[derive(Debug, Clone)]
pub struct TcFormatOpts {
    /// Out parameter for whether the term is atomic.
    pub is_atomic: Rc<Cell<bool>>,
    /// Parameter for whether to always expand terms.
    pub expand: bool,
}

impl Default for TcFormatOpts {
    fn default() -> Self {
        Self { is_atomic: Rc::new(Cell::new(false)), expand: false }
    }
}

/// Contains methods to format terms like types, traits, values etc.
///
/// It needs access to [GlobalStorage] in order to resolve nested structures of
/// types/traits/etc.
///
/// Some methods take an `is_atomic` parameter, which is an "out" parameter that
/// is set to `true` when the output is atomic (i.e. does not need to be put in
/// parentheses). For example:
///
/// `(A, B, C)`: atomic
/// `(A) -> B`: not atomic
/// `A ~ B`: not atomic
/// `C`: atomic
pub struct TcFormatter<'gs> {
    global_storage: &'gs GlobalStorage,
}

impl<'gs> TcFormatter<'gs> {
    pub fn new(global_storage: &'gs GlobalStorage) -> Self {
        Self { global_storage }
    }

    /// Format the given substitution with the given formatter.
    pub fn fmt_sub(&self, f: &mut fmt::Formatter, sub: &Sub) -> fmt::Result {
        for (subject, target) in sub.pairs() {
            match subject {
                SubSubject::Unresolved(unresolved) => {
                    self.fmt_unresolved(f, &unresolved)?;
                }
            };
            write!(f, " -> {}", target.for_formatting(self.global_storage))?;
        }
        Ok(())
    }

    /// Format the given scope with the given formatter.
    pub fn fmt_scope(&self, f: &mut fmt::Formatter, scope_id: ScopeId) -> fmt::Result {
        let scope = self.global_storage.scope_store.get(scope_id);

        let scope_value_fmt_opts = TcFormatOpts { expand: true, ..TcFormatOpts::default() };

        for member in scope.iter() {
            let mutability = match member.mutability {
                Mutability::Mutable => "mut ",
                Mutability::Immutable => "",
            };
            let visibility = match member.visibility {
                Visibility::Public => "pub ",
                Visibility::Private => "priv ",
            };
            let name = member.name;

            match member.data {
                MemberData::Uninitialised { ty } => {
                    writeln!(
                        f,
                        "{}{}{}: {};",
                        mutability,
                        visibility,
                        name,
                        ty.for_formatting(self.global_storage)
                    )?;
                }
                MemberData::InitialisedWithTy { ty, value } => {
                    writeln!(
                        f,
                        "{}{}{}: {} = {};",
                        mutability,
                        visibility,
                        name,
                        ty.for_formatting(self.global_storage),
                        value.for_formatting_with_opts(
                            self.global_storage,
                            scope_value_fmt_opts.clone()
                        ),
                    )?;
                }
                MemberData::InitialisedWithInferredTy { value } => {
                    writeln!(
                        f,
                        "{}{}{} := {};",
                        mutability,
                        visibility,
                        name,
                        value.for_formatting_with_opts(
                            self.global_storage,
                            scope_value_fmt_opts.clone()
                        ),
                    )?;
                }
            }
        }
        Ok(())
    }

    /// Format the given [Params] with the given formatter.
    pub fn fmt_params(&self, f: &mut fmt::Formatter, params_id: ParamsId) -> fmt::Result {
        let params = self.global_storage.params_store.get(params_id);

        for (i, param) in params.positional().iter().enumerate() {
            match param.name {
                Some(param_name) => {
                    write!(f, "{}: {}", param_name, param.ty.for_formatting(self.global_storage))?;
                }
                None => {
                    self.fmt_term(f, param.ty, TcFormatOpts::default())?;
                }
            }
            if i != params.positional().len() - 1 {
                write!(f, ", ")?;
            }
        }

        Ok(())
    }

    /// Format the given [Args] with the given formatter.
    pub fn fmt_args(&self, f: &mut fmt::Formatter, args_id: ArgsId) -> fmt::Result {
        let args = self.global_storage.args_store.get(args_id);

        for (i, arg) in args.positional().iter().enumerate() {
            match arg.name {
                Some(arg_name) => {
                    write!(f, "{} = {}", arg_name, arg.value.for_formatting(self.global_storage))?;
                }
                None => {
                    self.fmt_term(f, arg.value, TcFormatOpts::default())?;
                }
            }
            if i != args.positional().len() - 1 {
                write!(f, ", ")?;
            }
        }

        Ok(())
    }

    /// Format the [TrtDef](crate::storage::primitives::TrtDef) indexed by the
    /// given [TrtDefId] with the given formatter.
    pub fn fmt_trt_def(
        &self,
        f: &mut fmt::Formatter,
        trt_def_id: TrtDefId,
        opts: TcFormatOpts,
    ) -> fmt::Result {
        match self.global_storage.trt_def_store.get(trt_def_id).name {
            Some(name) if !opts.expand => {
                write!(f, "{}", name)
            }
            _ => {
                write!(f, "trait {{..}}")
            }
        }
    }

    /// Format a level 2 term.
    pub fn fmt_level0_term(
        &self,
        f: &mut fmt::Formatter,
        term: &Level0Term,
        opts: TcFormatOpts,
    ) -> fmt::Result {
        match term {
            Level0Term::Rt(ty_id) => {
                opts.is_atomic.set(true);
                write!(f, "{{value {}}}", ty_id.for_formatting(self.global_storage))
            }
            Level0Term::FnLit(fn_lit) => {
                opts.is_atomic.set(true);
                write!(
                    f,
                    "{} => {}",
                    fn_lit.fn_ty.for_formatting(self.global_storage),
                    fn_lit.return_value.for_formatting(self.global_storage),
                )
            }
            Level0Term::EnumVariant(enum_variant) => {
                opts.is_atomic.set(true);
                write!(
                    f,
                    "{}::{}",
                    enum_variant.enum_def_id.for_formatting(self.global_storage),
                    enum_variant.variant_name,
                )
            }
            Level0Term::FnCall(fn_call) => {
                opts.is_atomic.set(true);
                self.fmt_term_as_single(f, fn_call.subject, TcFormatOpts::default())?;
                write!(f, "({})", fn_call.args.for_formatting(self.global_storage))?;
                Ok(())
            }
            Level0Term::Lit(lit_term) => {
                opts.is_atomic.set(true);
                match lit_term {
                    LitTerm::Str(str) => {
                        write!(f, "\"{}\"", str)
                    }
                    LitTerm::Int(int) => {
                        write!(f, "{}", int)
                    }
                    LitTerm::Char(char) => {
                        write!(f, "\'{}\'", char)
                    }
                }
            }
            Level0Term::Tuple(tuple_lit) => {
                opts.is_atomic.set(true);
                write!(f, "({})", tuple_lit.members.for_formatting(self.global_storage))
            }
        }
    }

    /// Format a level 1 term.
    pub fn fmt_level1_term(
        &self,
        f: &mut fmt::Formatter,
        term: &Level1Term,
        opts: TcFormatOpts,
    ) -> fmt::Result {
        match term {
            Level1Term::ModDef(mod_def_id) => self.fmt_mod_def(f, *mod_def_id, opts),
            Level1Term::NominalDef(nominal_def_id) => {
                self.fmt_nominal_def(f, *nominal_def_id, opts)
            }
            Level1Term::Tuple(tuple) => {
                opts.is_atomic.set(true);
                write!(f, "(")?;
                self.fmt_params(f, tuple.members)?;
                write!(f, ")")?;
                Ok(())
            }
            Level1Term::Fn(fn_term) => {
                opts.is_atomic.set(false);
                write!(f, "(")?;
                self.fmt_params(f, fn_term.params)?;
                write!(f, ") -> ")?;
                self.fmt_term(f, fn_term.return_ty, opts)?;
                Ok(())
            }
        }
    }

    /// Format a level 2 term.
    pub fn fmt_level2_term(
        &self,
        f: &mut fmt::Formatter,
        term: &Level2Term,
        opts: TcFormatOpts,
    ) -> fmt::Result {
        opts.is_atomic.set(true);
        match term {
            Level2Term::Trt(trt_def_id) => self.fmt_trt_def(f, *trt_def_id, opts),
            Level2Term::AnyTy => {
                write!(f, "AnyType")
            }
        }
    }

    /// Format a level 3 term.
    pub fn fmt_level3_term(
        &self,
        f: &mut fmt::Formatter,
        term: &Level3Term,
        opts: TcFormatOpts,
    ) -> fmt::Result {
        opts.is_atomic.set(true);
        match term {
            Level3Term::TrtKind => write!(f, "Trait"),
        }
    }

    pub fn fmt_term_as_single(
        &self,
        f: &mut fmt::Formatter,
        term_id: TermId,
        opts: TcFormatOpts,
    ) -> fmt::Result {
        let term_fmt =
            format!("{}", term_id.for_formatting_with_opts(self.global_storage, opts.clone()));
        if !opts.is_atomic.get() {
            write!(f, "(")?;
        }
        write!(f, "{}", term_fmt)?;
        if !opts.is_atomic.get() {
            write!(f, ")")?;
        }
        Ok(())
    }

    /// Format the [Term] indexed by the given [TermId] with the given
    /// formatter.
    pub fn fmt_term(
        &self,
        f: &mut fmt::Formatter,
        term_id: TermId,
        opts: TcFormatOpts,
    ) -> fmt::Result {
        match self.global_storage.term_store.get(term_id) {
            Term::Access(access_term) => {
                opts.is_atomic.set(true);
                self.fmt_term_as_single(f, access_term.subject, opts)?;
                let op = match access_term.op {
                    AccessOp::Namespace => "::",
                    AccessOp::Property => ".",
                };
                write!(f, "{}{}", op, access_term.name)?;
                Ok(())
            }
            Term::Var(var) => {
                opts.is_atomic.set(true);
                write!(f, "{}", var.name)
            }
            Term::Merge(terms) => {
                opts.is_atomic.set(false);
                for (i, term_id) in terms.iter().enumerate() {
                    self.fmt_term_as_single(f, *term_id, opts.clone())?;
                    if i != terms.len() - 1 {
                        write!(f, " ~ ")?;
                    }
                }
                Ok(())
            }
            Term::Union(terms) => {
                if terms.is_empty() {
                    opts.is_atomic.set(true);
                    write!(f, "never")?;
                    Ok(())
                } else {
                    opts.is_atomic.set(false);
                    for (i, term_id) in terms.iter().enumerate() {
                        self.fmt_term_as_single(f, *term_id, opts.clone())?;
                        if i != terms.len() - 1 {
                            write!(f, " | ")?;
                        }
                    }
                    Ok(())
                }
            }
            Term::TyFn(ty_fn) => {
                match ty_fn.name {
                    Some(name) if !opts.expand => {
                        opts.is_atomic.set(true);
                        write!(f, "{}", name)?;
                        Ok(())
                    }
                    _ => {
                        opts.is_atomic.set(false);
                        write!(f, "<")?;
                        self.fmt_params(f, ty_fn.general_params)?;
                        write!(f, "> -> ")?;
                        self.fmt_term(f, ty_fn.general_return_ty, opts.clone())?;

                        if let Some(case) = ty_fn.cases.first() {
                            write!(f, " => ")?;
                            self.fmt_term(f, case.return_value, opts)?;
                        }

                        // We assume only the first case is the base one
                        // @@TODO: refine this to show all cases
                        Ok(())
                    }
                }
            }
            Term::TyFnTy(ty_fn_ty) => {
                opts.is_atomic.set(false);
                write!(f, "<")?;
                self.fmt_params(f, ty_fn_ty.params)?;
                write!(f, "> -> ")?;
                self.fmt_term(f, ty_fn_ty.return_ty, opts)?;
                Ok(())
            }
            Term::TyFnCall(app_ty_fn) => {
                opts.is_atomic.set(true);
                self.fmt_term_as_single(f, app_ty_fn.subject, opts)?;
                write!(f, "<")?;
                self.fmt_args(f, app_ty_fn.args)?;
                write!(f, ">")?;
                Ok(())
            }
            Term::Unresolved(unresolved_term) => self.fmt_unresolved(f, unresolved_term),
            Term::SetBound(set_bound) => {
                opts.is_atomic.set(false);
                self.fmt_term_as_single(f, set_bound.term, opts.clone())?;

                let members = &self.global_storage.scope_store.get(set_bound.scope).members;
                write!(f, " where ")?;
                for (i, member) in members.iter().enumerate() {
                    write!(f, "{} = ", member.name)?;
                    self.fmt_term_as_single(f, member.data.value().unwrap(), opts.clone())?;
                    if i != members.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                Ok(())
            }
            Term::Level3(term) => self.fmt_level3_term(f, term, opts),
            Term::Level2(term) => self.fmt_level2_term(f, term, opts),
            Term::Level1(term) => self.fmt_level1_term(f, term, opts),
            Term::Level0(term) => self.fmt_level0_term(f, term, opts),
            Term::Root => {
                opts.is_atomic.set(true);
                write!(f, "Root")
            }
            Term::TyOf(term) => {
                write!(
                    f,
                    "typeof({})",
                    term.for_formatting_with_opts(
                        self.global_storage,
                        TcFormatOpts { expand: opts.expand, ..TcFormatOpts::default() }
                    )
                )
            }
            Term::ScopeVar(var) => {
                opts.is_atomic.set(true);
                write!(f, "{}", var.name)
            }
        }
    }

    /// Format a [Term::Unresolved], printing its resolution ID.
    pub fn fmt_unresolved(
        &self,
        f: &mut fmt::Formatter,
        UnresolvedTerm { resolution_id }: &UnresolvedTerm,
    ) -> fmt::Result {
        write!(f, "U_{}", resolution_id)
    }

    /// Format a [NominalDef] indexed by the given [NominalDefId].
    pub fn fmt_nominal_def(
        &self,
        f: &mut fmt::Formatter,
        nominal_def_id: NominalDefId,
        opts: TcFormatOpts,
    ) -> fmt::Result {
        opts.is_atomic.set(true);
        match self.global_storage.nominal_def_store.get(nominal_def_id) {
            NominalDef::Struct(StructDef { name: Some(name), .. })
            | NominalDef::Enum(EnumDef { name: Some(name), .. })
                if !opts.expand =>
            {
                write!(f, "{}", name)
            }
            // @@Future: we can actually print out the location of these definitions, which might
            // help with debugging.
            // Perhaps also we can have a flag to print out all the members.
            NominalDef::Struct(_) => {
                write!(f, "struct(..)")
            }
            NominalDef::Enum(_) => {
                write!(f, "enum(..)")
            }
        }
    }

    /// Format a [ModDef](crate::storage::primitives::ModDef) indexed by the
    /// given [ModDefId].
    pub fn fmt_mod_def(
        &self,
        f: &mut fmt::Formatter,
        mod_def_id: ModDefId,
        opts: TcFormatOpts,
    ) -> fmt::Result {
        let mod_def = self.global_storage.mod_def_store.get(mod_def_id);
        match mod_def.name {
            Some(name) if !opts.expand => {
                opts.is_atomic.set(true);
                write!(f, "{}", name)
            }
            _ => match mod_def.origin {
                ModDefOrigin::TrtImpl(trt_def_id) => {
                    opts.is_atomic.set(false);
                    write!(f, "impl {} {{..}}", trt_def_id.for_formatting(self.global_storage))
                }
                ModDefOrigin::AnonImpl => {
                    opts.is_atomic.set(false);
                    write!(f, "impl {{..}}")
                }
                ModDefOrigin::Mod => {
                    opts.is_atomic.set(false);
                    write!(f, "mod {{..}}")
                }
                ModDefOrigin::Source(_) => {
                    opts.is_atomic.set(true);
                    // @@TODO: show the source path
                    write!(f, "source(..)")
                }
            },
        }
    }

    /// Format the given [PatParams] with the given formatter.
    pub fn fmt_pat_params(
        &self,
        f: &mut fmt::Formatter,
        pat_params_id: PatParamsId,
    ) -> fmt::Result {
        let pat_params = self.global_storage.pat_params_store.get(pat_params_id);

        for (i, param) in pat_params.positional().iter().enumerate() {
            match param.name {
                Some(param_name) => {
                    write!(
                        f,
                        "{} = {}",
                        param_name,
                        param.pat.for_formatting(self.global_storage)
                    )?;
                }
                None => {
                    self.fmt_pat(f, param.pat, TcFormatOpts::default())?;
                }
            }
            if i != pat_params.positional().len() - 1 {
                write!(f, ", ")?;
            }
        }

        Ok(())
    }

    pub fn fmt_pat_as_single(
        &self,
        f: &mut fmt::Formatter,
        pat: PatId,
        opts: TcFormatOpts,
    ) -> fmt::Result {
        let pat_fmt =
            format!("{}", pat.for_formatting_with_opts(self.global_storage, opts.clone()));
        if !opts.is_atomic.get() {
            write!(f, "(")?;
        }
        write!(f, "{}", pat_fmt)?;
        if !opts.is_atomic.get() {
            write!(f, ")")?;
        }
        Ok(())
    }

    /// Format a [Pat](crate::storage::primitives::Pat) indexed by the
    /// given [PatId].
    pub fn fmt_pat(&self, f: &mut fmt::Formatter, pat: PatId, opts: TcFormatOpts) -> fmt::Result {
        let pat = self.global_storage.pat_store.get(pat);
        match pat {
            Pat::Binding(binding) => {
                let mutability = match binding.mutability {
                    Mutability::Mutable => "mut ",
                    Mutability::Immutable => "",
                };
                let visibility = match binding.visibility {
                    Visibility::Public => "pub ",
                    Visibility::Private => "priv ",
                };
                let name = binding.name;
                opts.is_atomic.set(false);
                write!(f, "{}{}{}", visibility, mutability, name)
            }
            Pat::Lit(lit_term) => self.fmt_term(f, *lit_term, opts),
            Pat::Tuple(tuple_pat) => {
                opts.is_atomic.set(true);
                write!(f, "({})", tuple_pat.for_formatting(self.global_storage))
            }
            Pat::Constructor(constructor_pat) => {
                opts.is_atomic.set(true);
                self.fmt_term_as_single(f, constructor_pat.subject, opts)?;
                if let Some(params) = constructor_pat.params {
                    write!(f, "({})", params.for_formatting(self.global_storage))?;
                }
                Ok(())
            }
            Pat::Or(pats) => {
                if pats.is_empty() {
                    opts.is_atomic.set(true);
                    write!(f, "{{empty or pattern}}")?;
                    Ok(())
                } else {
                    opts.is_atomic.set(false);
                    for (i, pat_id) in pats.iter().enumerate() {
                        self.fmt_pat_as_single(f, *pat_id, opts.clone())?;
                        if i != pats.len() - 1 {
                            write!(f, " | ")?;
                        }
                    }
                    Ok(())
                }
            }
            Pat::If(if_pat) => {
                opts.is_atomic.set(false);
                self.fmt_pat_as_single(f, if_pat.pat, opts.clone())?;
                write!(f, " if ",)?;
                self.fmt_term_as_single(f, if_pat.condition, opts)?;
                Ok(())
            }
            Pat::Ignore => {
                write!(f, "_")
            }
            Pat::Mod(ModPat { members }) => {
                opts.is_atomic.set(true);
                let pat_params = self.global_storage.pat_params_store.get(*members);

                write!(f, "{{ ")?;
                for (i, param) in pat_params.positional().iter().enumerate() {
                    match param.name {
                        Some(param_name) => {
                            write!(
                                f,
                                "{} as {}",
                                param_name,
                                param.pat.for_formatting(self.global_storage)
                            )?;
                        }
                        None => {
                            self.fmt_pat(f, param.pat, TcFormatOpts::default())?;
                        }
                    }
                    if i != pat_params.positional().len() - 1 {
                        write!(f, "; ")?;
                    }
                }
                write!(f, " }}")?;

                Ok(())
            }
        }
    }
}

/// Wraps a type `T` in a structure that contains information to be able to
/// format `T` using [TcFormatter].
///
/// This can wrap any type, but only types that have corresponding `fmt_*`
/// methods in [TcFormatter] are useful with it.
pub struct ForFormatting<'gs, T> {
    pub t: T,
    pub global_storage: &'gs GlobalStorage,
    pub opts: TcFormatOpts,
}

/// Convenience trait to create a `ForFormatting<T>` given a `T`.
pub trait PrepareForFormatting: Sized {
    /// Create a `ForFormatting<T>` given a `T`.
    fn for_formatting(self, global_storage: &GlobalStorage) -> ForFormatting<Self> {
        ForFormatting { t: self, global_storage, opts: TcFormatOpts::default() }
    }

    /// Create a `ForFormatting<T>` given a `T`, and provide an out parameter
    /// for the `is_atomic` check.
    fn for_formatting_with_opts(
        self,
        global_storage: &GlobalStorage,
        opts: TcFormatOpts,
    ) -> ForFormatting<Self> {
        ForFormatting { t: self, global_storage, opts }
    }
}

impl<T: PrepareForFormatting> PrepareForFormatting for Option<T> {}
impl PrepareForFormatting for TermId {}
impl PrepareForFormatting for TrtDefId {}
impl PrepareForFormatting for ModDefId {}
impl PrepareForFormatting for NominalDefId {}
impl PrepareForFormatting for ParamsId {}
impl PrepareForFormatting for ArgsId {}
impl PrepareForFormatting for ScopeId {}
impl PrepareForFormatting for PatParamsId {}
impl PrepareForFormatting for PatId {}
impl PrepareForFormatting for &Sub {}

// Convenience implementations of Display for the types that implement
// PrepareForFormatting:

impl fmt::Display for ForFormatting<'_, TermId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_term(f, self.t, self.opts.clone())
    }
}

impl fmt::Display for ForFormatting<'_, TrtDefId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_trt_def(f, self.t, self.opts.clone())
    }
}

impl fmt::Display for ForFormatting<'_, ModDefId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_mod_def(f, self.t, self.opts.clone())
    }
}

impl fmt::Display for ForFormatting<'_, NominalDefId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_nominal_def(f, self.t, self.opts.clone())
    }
}

impl fmt::Display for ForFormatting<'_, ParamsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_params(f, self.t)
    }
}

impl fmt::Display for ForFormatting<'_, PatParamsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_pat_params(f, self.t)
    }
}

impl fmt::Display for ForFormatting<'_, PatId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_pat(f, self.t, self.opts.clone())
    }
}

impl fmt::Display for ForFormatting<'_, ArgsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_args(f, self.t)
    }
}

impl fmt::Display for ForFormatting<'_, ScopeId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_scope(f, self.t)
    }
}

impl fmt::Display for ForFormatting<'_, &Sub> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_sub(f, self.t)
    }
}

impl<'gs, T: PrepareForFormatting + Clone> fmt::Display for ForFormatting<'gs, Option<T>>
where
    ForFormatting<'gs, T>: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.t.as_ref() {
            Some(t) => {
                write!(
                    f,
                    "Some({})",
                    t.clone().for_formatting_with_opts(self.global_storage, self.opts.clone())
                )
            }
            None => {
                write!(f, "None")
            }
        }
    }
}
