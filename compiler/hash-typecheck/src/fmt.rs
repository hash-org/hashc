//! Contains utilities to format types for displaying in error messages and debug output.
use crate::storage::{
    primitives::{
        Args, EnumDef, Level0Term, Level1Term, Level2Term, Level3Term, ModDefId, ModDefOrigin,
        NominalDef, NominalDefId, Params, StructDef, SubSubject, Term, TermId, TrtDefId,
        UnresolvedTerm,
    },
    GlobalStorage,
};
use core::fmt;
use std::cell::Cell;

/// Contains methods to format terms like types, traits, values etc.
///
/// It needs access to [GlobalStorage] in order to resolve nested structures of types/traits/etc.
///
/// Some methods take an `is_atomic` parameter, which is an "out" parameter that is set to `true`
/// when the output is atomic (i.e. does not need to be put in parentheses). For example:
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

    /// Format the given [Params] with the given formatter.
    pub fn fmt_params(&self, f: &mut fmt::Formatter, params: &Params) -> fmt::Result {
        for (i, param) in params.positional().iter().enumerate() {
            match param.name {
                Some(param_name) => {
                    write!(
                        f,
                        "{}: {}",
                        param_name,
                        param.ty.for_formatting(self.global_storage)
                    )?;
                }
                None => {
                    self.fmt_term(f, param.ty, &Cell::new(false))?;
                }
            }
            if i != params.positional().len() - 1 {
                write!(f, ", ")?;
            }
        }

        Ok(())
    }

    /// Format the given [Args] with the given formatter.
    pub fn fmt_args(&self, f: &mut fmt::Formatter, args: &Args) -> fmt::Result {
        for (i, arg) in args.positional().iter().enumerate() {
            match arg.name {
                Some(arg_name) => {
                    write!(
                        f,
                        "{} = {}",
                        arg_name,
                        arg.value.for_formatting(self.global_storage)
                    )?;
                }
                None => {
                    self.fmt_term(f, arg.value, &Cell::new(false))?;
                }
            }
            if i != args.positional().len() - 1 {
                write!(f, ", ")?;
            }
        }

        Ok(())
    }

    /// Format the [TrtDef](crate::storage::primitives::TrtDef) indexed by the given [TrtDefId]
    /// with the given formatter.
    pub fn fmt_trt_def(&self, f: &mut fmt::Formatter, trt_def_id: TrtDefId) -> fmt::Result {
        match self.global_storage.trt_def_store.get(trt_def_id).name {
            Some(name) => {
                write!(f, "{}", name)
            }
            None => {
                write!(f, "trait(..)")
            }
        }
    }

    /// Format a level 2 term.
    pub fn fmt_level0_term(
        &self,
        f: &mut fmt::Formatter,
        term: &Level0Term,
        is_atomic: &Cell<bool>,
    ) -> fmt::Result {
        match term {
            Level0Term::Rt(ty_id) => {
                is_atomic.set(true);
                write!(
                    f,
                    "{{runtime value of type {}}}",
                    ty_id.for_formatting(self.global_storage)
                )
            }
            Level0Term::FnLit(fn_lit) => {
                is_atomic.set(true);
                write!(
                    f,
                    "{{function literal of type {}}}",
                    fn_lit.fn_ty.for_formatting(self.global_storage)
                )
            }
            Level0Term::EnumVariant(enum_variant) => {
                is_atomic.set(true);
                write!(
                    f,
                    "{{enum variant '{}' of {}}}",
                    enum_variant.variant_name,
                    enum_variant.enum_def_id.for_formatting(self.global_storage)
                )
            }
        }
    }

    /// Format a level 1 term.
    pub fn fmt_level1_term(
        &self,
        f: &mut fmt::Formatter,
        term: &Level1Term,
        is_atomic: &Cell<bool>,
    ) -> fmt::Result {
        match term {
            Level1Term::ModDef(mod_def_id) => self.fmt_mod_def(f, *mod_def_id, is_atomic),
            Level1Term::NominalDef(nominal_def_id) => {
                self.fmt_nominal_def(f, *nominal_def_id, is_atomic)
            }
            Level1Term::Tuple(tuple) => {
                is_atomic.set(true);
                write!(f, "(")?;
                self.fmt_params(f, &tuple.members)?;
                write!(f, ")")?;
                Ok(())
            }
            Level1Term::Fn(fn_term) => {
                is_atomic.set(false);
                write!(f, "(")?;
                self.fmt_params(f, &fn_term.params)?;
                write!(f, ") -> ")?;
                self.fmt_term(f, fn_term.return_ty, &Cell::new(false))?;
                Ok(())
            }
        }
    }

    /// Format a level 2 term.
    pub fn fmt_level2_term(
        &self,
        f: &mut fmt::Formatter,
        term: &Level2Term,
        is_atomic: &Cell<bool>,
    ) -> fmt::Result {
        is_atomic.set(true);
        match term {
            Level2Term::Trt(trt_def_id) => self.fmt_trt_def(f, *trt_def_id),
            Level2Term::AnyTy => {
                write!(f, "Type")
            }
        }
    }

    /// Format a level 3 term.
    pub fn fmt_level3_term(
        &self,
        f: &mut fmt::Formatter,
        term: &Level3Term,
        is_atomic: &Cell<bool>,
    ) -> fmt::Result {
        is_atomic.set(true);
        match term {
            Level3Term::TrtKind => write!(f, "Trait"),
        }
    }

    pub fn fmt_term_as_single(&self, f: &mut fmt::Formatter, term_id: TermId) -> fmt::Result {
        let term_is_atomic = Cell::new(false);
        let term_fmt = format!(
            "{}",
            term_id.for_formatting_with_atomic_flag(self.global_storage, &term_is_atomic)
        );
        if !term_is_atomic.get() {
            write!(f, "(")?;
        }
        write!(f, "{}", term_fmt)?;
        if !term_is_atomic.get() {
            write!(f, ")")?;
        }
        Ok(())
    }

    /// Format the [Term] indexed by the given [TermId] with the given formatter.
    pub fn fmt_term(
        &self,
        f: &mut fmt::Formatter,
        term_id: TermId,
        is_atomic: &Cell<bool>,
    ) -> fmt::Result {
        match self.global_storage.term_store.get(term_id) {
            Term::Access(access_term) => {
                is_atomic.set(true);
                self.fmt_term_as_single(f, access_term.subject)?;
                write!(f, "::{}", access_term.name)?;
                Ok(())
            }
            Term::Var(var) => {
                write!(f, "{}", var.name)
            }
            Term::Merge(terms) => {
                is_atomic.set(false);
                for (i, term_id) in terms.iter().enumerate() {
                    self.fmt_term_as_single(f, *term_id)?;
                    if i != terms.len() - 1 {
                        write!(f, " ~ ")?;
                    }
                }
                Ok(())
            }
            Term::TyFn(ty_fn) => {
                match ty_fn.name {
                    Some(name) => {
                        is_atomic.set(true);
                        write!(f, "{}", name)?;
                        Ok(())
                    }
                    None => {
                        is_atomic.set(false);
                        write!(f, "<")?;
                        self.fmt_params(f, &ty_fn.general_params)?;
                        write!(f, "> -> ")?;
                        self.fmt_term(f, ty_fn.general_return_ty, &Cell::new(false))?;

                        if let Some(case) = ty_fn.cases.first() {
                            write!(f, " => ")?;
                            let is_atomic = Cell::new(false);
                            self.fmt_term(f, case.return_value, &is_atomic)?;
                        }

                        // We assume only the first case is the base one
                        // @@TODO: refine this to show all cases
                        Ok(())
                    }
                }
            }
            Term::TyFnTy(ty_fn_ty) => {
                is_atomic.set(false);
                write!(f, "<")?;
                self.fmt_params(f, &ty_fn_ty.params)?;
                write!(f, "> -> ")?;
                self.fmt_term(f, ty_fn_ty.return_ty, &Cell::new(false))?;
                Ok(())
            }
            Term::AppTyFn(app_ty_fn) => {
                self.fmt_term_as_single(f, app_ty_fn.subject)?;
                write!(f, "<")?;
                self.fmt_args(f, &app_ty_fn.args)?;
                write!(f, ">")?;
                Ok(())
            }
            Term::Unresolved(unresolved_term) => self.fmt_unresolved(f, unresolved_term),
            Term::AppSub(app_sub) => {
                write!(f, "[")?;
                let pairs = app_sub.sub.pairs().collect::<Vec<_>>();
                for (i, (from, to)) in pairs.iter().enumerate() {
                    self.fmt_term_as_single(f, *to)?;
                    write!(f, "/")?;
                    match from {
                        SubSubject::Var(var) => write!(f, "{}", var.name)?,
                        SubSubject::Unresolved(unresolved) => self.fmt_unresolved(f, unresolved)?,
                    }

                    if i != pairs.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]")?;
                self.fmt_term_as_single(f, app_sub.term)?;
                Ok(())
            }
            Term::Level3(term) => self.fmt_level3_term(f, term, is_atomic),
            Term::Level2(term) => self.fmt_level2_term(f, term, is_atomic),
            Term::Level1(term) => self.fmt_level1_term(f, term, is_atomic),
            Term::Level0(term) => self.fmt_level0_term(f, term, is_atomic),
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
        is_atomic: &Cell<bool>,
    ) -> fmt::Result {
        is_atomic.set(true);
        match self.global_storage.nominal_def_store.get(nominal_def_id) {
            NominalDef::Struct(StructDef {
                name: Some(name), ..
            })
            | NominalDef::Enum(EnumDef {
                name: Some(name), ..
            }) => {
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

    /// Format a [ModDef](crate::storage::primitives::ModDef) indexed by the given [ModDefId].
    pub fn fmt_mod_def(
        &self,
        f: &mut fmt::Formatter,
        mod_def_id: ModDefId,
        is_atomic: &Cell<bool>,
    ) -> fmt::Result {
        let mod_def = self.global_storage.mod_def_store.get(mod_def_id);
        match mod_def.name {
            Some(name) => {
                is_atomic.set(true);
                write!(f, "{}", name)
            }
            None => match mod_def.origin {
                ModDefOrigin::TrtImpl(trt_def_id) => {
                    is_atomic.set(false);
                    write!(
                        f,
                        "impl {} {{..}}",
                        trt_def_id.for_formatting(self.global_storage)
                    )
                }
                ModDefOrigin::AnonImpl => {
                    is_atomic.set(false);
                    write!(f, "impl {{..}}")
                }
                ModDefOrigin::Mod => {
                    is_atomic.set(false);
                    write!(f, "mod {{..}}")
                }
                ModDefOrigin::Source(_) => {
                    is_atomic.set(true);
                    // @@TODO: show the source path
                    write!(f, "source(..)")
                }
            },
        }
    }
}

/// Wraps a type `T` in a structure that contains information to be able to format `T` using
/// [TcFormatter].
///
/// This can wrap any type, but only types that have corresponding `fmt_*` methods in
/// [TcFormatter] are useful with it.
pub struct ForFormatting<'gs, 'a, T> {
    pub t: T,
    pub global_storage: &'gs GlobalStorage,
    pub is_atomic: Option<&'a Cell<bool>>,
}

/// Convenience trait to create a `ForFormatting<T>` given a `T`.
pub trait PrepareForFormatting: Sized {
    /// Create a `ForFormatting<T>` given a `T`.
    fn for_formatting<'gs>(
        self,
        global_storage: &'gs GlobalStorage,
    ) -> ForFormatting<'gs, '_, Self> {
        ForFormatting {
            t: self,
            global_storage,
            is_atomic: None,
        }
    }

    /// Create a `ForFormatting<T>` given a `T`, and provide an out parameter for the `is_atomic`
    /// check.
    fn for_formatting_with_atomic_flag<'gs, 'a>(
        self,
        global_storage: &'gs GlobalStorage,
        is_atomic: &'a Cell<bool>,
    ) -> ForFormatting<'gs, 'a, Self> {
        ForFormatting {
            t: self,
            global_storage,
            is_atomic: Some(is_atomic),
        }
    }
}

impl PrepareForFormatting for TermId {}
impl PrepareForFormatting for TrtDefId {}
impl PrepareForFormatting for ModDefId {}
impl PrepareForFormatting for NominalDefId {}

// Convenience implementations of Display for the types that implement PrepareForFormatting:

impl fmt::Display for ForFormatting<'_, '_, TermId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_term(
            f,
            self.t,
            self.is_atomic.unwrap_or(&Cell::new(false)),
        )
    }
}

impl fmt::Display for ForFormatting<'_, '_, TrtDefId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_trt_def(f, self.t)
    }
}

impl fmt::Display for ForFormatting<'_, '_, ModDefId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_mod_def(
            f,
            self.t,
            self.is_atomic.unwrap_or(&Cell::new(false)),
        )
    }
}

impl fmt::Display for ForFormatting<'_, '_, NominalDefId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_nominal_def(
            f,
            self.t,
            self.is_atomic.unwrap_or(&Cell::new(false)),
        )
    }
}
