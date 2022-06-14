//! Contains utilities to format types for displaying in error messages and debug output.
use crate::storage::{
    primitives::{
        AppTyFn, Args, EnumDef, FnTy, ModDefId, ModDefOrigin, NominalDef, NominalDefId, Params,
        StructDef, TrtDefId, TupleTy, Ty, TyFnTy, TyFnValue, TyId, UnresolvedTy, Value, ValueId,
    },
    GlobalStorage,
};
use core::fmt;
use std::cell::Cell;

/// Contains methods to format types, traits, values etc.
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
                    self.fmt_ty(f, param.ty, &Cell::new(false))?;
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
                    self.fmt_value(f, arg.value, &Cell::new(false))?;
                }
            }
            if i != args.positional().len() - 1 {
                write!(f, ", ")?;
            }
        }

        Ok(())
    }

    /// Format the given [AppTyFn] with the given formatter.
    pub fn fmt_app_ty_fn(&self, f: &mut fmt::Formatter, app_ty_fn: &AppTyFn) -> fmt::Result {
        let subject_is_atomic = Cell::new(false);
        let subject_fmt = format!(
            "{}",
            app_ty_fn
                .ty_fn_value
                .for_formatting_with_atomic_flag(self.global_storage, &subject_is_atomic)
        );

        if !subject_is_atomic.get() {
            write!(f, "(")?;
        }
        write!(f, "{}", subject_fmt)?;
        if !subject_is_atomic.get() {
            write!(f, ")")?;
        }
        write!(f, "<")?;

        self.fmt_args(f, &app_ty_fn.args)?;
        write!(f, ">")?;

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

    /// Format the [Value] indexed by the given [ValueId] with the given formatter.
    pub fn fmt_value(
        &self,
        f: &mut fmt::Formatter,
        value_id: ValueId,
        is_atomic: &Cell<bool>,
    ) -> fmt::Result {
        match self.global_storage.value_store.get(value_id) {
            Value::Trt(trt_def_id) => {
                is_atomic.set(true);
                self.fmt_trt_def(f, *trt_def_id)?;
                Ok(())
            }
            Value::Ty(ty_id) => {
                self.fmt_ty(f, *ty_id, is_atomic)?;
                Ok(())
            }
            Value::Rt => {
                is_atomic.set(true);
                write!(f, "{{runtime value}}")
            }
            Value::TyFn(TyFnValue {
                name,
                general_params,
                general_return_ty,
                cases,
            }) => {
                match name {
                    Some(name) => {
                        is_atomic.set(true);
                        write!(f, "{}", name)?;
                        Ok(())
                    }
                    None => {
                        is_atomic.set(false);
                        write!(f, "<")?;
                        self.fmt_params(f, general_params)?;
                        write!(f, "> -> ")?;
                        self.fmt_ty(f, *general_return_ty, &Cell::new(false))?;

                        if let Some(case) = cases.first() {
                            write!(f, " => ")?;
                            let is_atomic = Cell::new(false);
                            self.fmt_value(f, case.return_value, &is_atomic)?;
                        }

                        // We assume only the first case is the base one
                        // @@TODO: refine this to show all cases
                        Ok(())
                    }
                }
            }
            Value::AppTyFn(app_ty_fn) => {
                is_atomic.set(true);
                self.fmt_app_ty_fn(f, app_ty_fn)
            }
            Value::Var(var) => {
                is_atomic.set(true);
                write!(f, "{}", var.name)
            }
            Value::Merge(values) => {
                is_atomic.set(false);
                for (i, value) in values.iter().enumerate() {
                    let value_is_atomic = Cell::new(false);
                    let value_fmt = format!(
                        "{}",
                        value
                            .for_formatting_with_atomic_flag(self.global_storage, &value_is_atomic)
                    );

                    if !value_is_atomic.get() {
                        write!(f, "(")?;
                    }
                    write!(f, "{}", value_fmt)?;
                    if !value_is_atomic.get() {
                        write!(f, ")")?;
                    }

                    if i != values.len() - 1 {
                        write!(f, " ~ ")?;
                    }
                }
                Ok(())
            }
            Value::Unset => {
                is_atomic.set(true);
                write!(f, "{{unset}}")
            }
            Value::ModDef(_) => todo!(),
            Value::NominalDef(_) => todo!(),
        }
    }

    pub fn fmt_unresolved(
        &self,
        f: &mut fmt::Formatter,
        UnresolvedTy { resolution_id }: &UnresolvedTy,
    ) -> fmt::Result {
        write!(f, "{{unresolved({:?})}}", resolution_id,)
    }

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

    pub fn fmt_mod_def(
        &self,
        f: &mut fmt::Formatter,
        mod_def_id: ModDefId,
        is_atomic: &Cell<bool>,
    ) -> fmt::Result {
        is_atomic.set(true);
        let mod_def = self.global_storage.mod_def_store.get(mod_def_id);
        match mod_def.name {
            Some(name) => {
                write!(f, "{}", name)
            }
            None => match mod_def.origin {
                ModDefOrigin::TrtImpl(trt_def_id) => {
                    write!(
                        f,
                        "impl[{}](..)",
                        trt_def_id.for_formatting(self.global_storage)
                    )
                }
                ModDefOrigin::AnonImpl => {
                    write!(f, "impl(..)")
                }
                ModDefOrigin::Mod => {
                    write!(f, "mod(..)")
                }
                ModDefOrigin::Source(_) => {
                    // @@TODO: show the source path
                    write!(f, "source(..)")
                }
            },
        }
    }

    /// Format the [Ty] indexed by the given [TyId] with the given formatter.
    pub fn fmt_ty(
        &self,
        f: &mut fmt::Formatter,
        ty_id: TyId,
        is_atomic: &Cell<bool>,
    ) -> fmt::Result {
        match self.global_storage.ty_store.get(ty_id) {
            Ty::NominalDef(nominal_def_id) => self.fmt_nominal_def(f, *nominal_def_id, is_atomic),
            Ty::ModDef(mod_def_id) => self.fmt_mod_def(f, *mod_def_id, is_atomic),
            Ty::Tuple(TupleTy { members }) => {
                is_atomic.set(true);
                write!(f, "(")?;
                self.fmt_params(f, members)?;
                write!(f, ")")?;

                Ok(())
            }
            Ty::Fn(FnTy { params, return_ty }) => {
                is_atomic.set(false);
                write!(f, "(")?;
                self.fmt_params(f, params)?;
                write!(f, ") -> ")?;
                self.fmt_ty(f, *return_ty, &Cell::new(false))?;
                Ok(())
            }
            Ty::Var(var) => {
                is_atomic.set(true);
                write!(f, "{}", var.name)
            }
            Ty::TyFn(TyFnTy { params, return_ty }) => {
                is_atomic.set(false);

                write!(f, "<")?;
                self.fmt_params(f, params)?;
                write!(f, "> -> ")?;
                self.fmt_ty(f, *return_ty, &Cell::new(false))?;

                Ok(())
            }
            Ty::AppTyFn(app_ty_fn) => {
                is_atomic.set(true);
                self.fmt_app_ty_fn(f, app_ty_fn)
            }
            Ty::Trt => {
                is_atomic.set(true);
                write!(f, "Trait")
            }
            Ty::Ty(None) => {
                is_atomic.set(true);
                write!(f, "Type")
            }
            Ty::Ty(Some(bound_trt_def_id)) => {
                write!(
                    f,
                    "{}",
                    bound_trt_def_id
                        .for_formatting_with_atomic_flag(self.global_storage, is_atomic)
                )
            }
            Ty::Merge(tys) => {
                is_atomic.set(false);
                for (i, ty) in tys.iter().enumerate() {
                    let ty_is_atomic = Cell::new(false);
                    let ty_fmt = format!(
                        "{}",
                        ty.for_formatting_with_atomic_flag(self.global_storage, &ty_is_atomic)
                    );

                    if !ty_is_atomic.get() {
                        write!(f, "(")?;
                    }
                    write!(f, "{}", ty_fmt)?;
                    if !ty_is_atomic.get() {
                        write!(f, ")")?;
                    }

                    if i != tys.len() - 1 {
                        write!(f, " ~ ")?;
                    }
                }
                Ok(())
            }
            Ty::Unresolved(unresolved) => {
                is_atomic.set(true);
                self.fmt_unresolved(f, unresolved)
            }
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

impl PrepareForFormatting for ValueId {}
impl PrepareForFormatting for TyId {}
impl PrepareForFormatting for TrtDefId {}
impl PrepareForFormatting for ModDefId {}

// Convenience implementations of Display for the types that implement PrepareForFormatting:

impl fmt::Display for ForFormatting<'_, '_, ValueId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_value(
            f,
            self.t,
            self.is_atomic.unwrap_or(&Cell::new(false)),
        )
    }
}

impl fmt::Display for ForFormatting<'_, '_, TyId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        TcFormatter::new(self.global_storage).fmt_ty(
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
