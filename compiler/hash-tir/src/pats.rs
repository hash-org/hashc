//! Contains structures to keep track of patterns and information relating to
//! them.
use std::fmt;

use hash_ast::ast::RangeEnd;
use hash_source::identifier::Identifier;
use hash_utils::{
    new_sequence_store_key, new_store, new_store_key,
    store::{CloneStore, Store},
};

use crate::{
    fmt::{ForFormatting, PrepareForFormatting},
    params::{GetNameOpt, ParamList, ParamListStore},
    scope::{Mutability, Visibility},
    storage::GlobalStorage,
    terms::TermId,
};

/// A binding pattern, which is essentially a declaration left-hand side.
#[derive(Clone, Debug, Copy)]
pub struct BindingPat {
    /// The name that is associated with the binding.
    pub name: Identifier,

    /// The associated [Mutability] with this pattern bind. If the pattern does
    /// not specify a mutability, then this will be [Mutability::Immutable].
    pub mutability: Mutability,

    /// The associated [Visibility] with this pattern bind. If the pattern does
    /// specify the `visibility` in source, it is determined by the context.
    pub visibility: Visibility,
}

/// An access pattern is the equivalent of an access expression which denotes
/// accessing symbols within some namespace. The `property` that is accessed
/// from the subject.
#[derive(Clone, Debug, Copy)]
pub struct AccessPat {
    /// The subject that is to be accessed
    pub subject: PatId,
    /// The property that is accessed from the `subject`
    pub property: Identifier,
}

/// A constant pattern is essentially a bind pattern that can be resolved within
/// the current scope of the pattern. This used to support [Pat::Access] working
/// the resolution machinery.
#[derive(Clone, Debug, Copy)]
pub struct ConstPat {
    /// The resolved term of the constant.
    pub term: TermId,
}

/// A pattern of a parameter, used for tuple patterns and constructor patterns.
#[derive(Clone, Debug, Copy)]
pub struct PatArg {
    pub name: Option<Identifier>,
    pub pat: PatId,
}

impl GetNameOpt for PatArg {
    fn get_name_opt(&self) -> Option<Identifier> {
        self.name
    }
}

/// A pattern of parameters.
pub type PatArgs<'p> = ParamList<'p, PatArg>;

/// A constructor pattern, used for enum variants and structs.
#[derive(Clone, Debug, Copy)]
pub struct ConstructorPat {
    pub subject: TermId,
    /// If `params` is `None`, it means that the constructor has no parameters;
    /// it is a unit.
    pub args: PatArgsId,
}

/// A list pattern
#[derive(Clone, Debug, Copy)]
pub struct ArrayPat {
    /// The element type of the list
    pub list_element_ty: TermId,
    /// Patterns for the list elements
    pub element_pats: PatArgsId,
}

impl ArrayPat {
    /// Split the pattern into the `prefix`, `suffix` and an optional;
    /// `rest` pattern.
    pub fn into_parts(&self, tcx: &GlobalStorage) -> (Vec<PatId>, Vec<PatId>, Option<PatId>) {
        let mut prefix = vec![];
        let mut suffix = vec![];
        let mut rest = None;

        tcx.pat_args_store.map_as_param_list_fast(self.element_pats, |args| {
            for arg in args.positional() {
                let is_spread = tcx.pat_store.map_fast(arg.pat, |pat| pat.is_spread());

                match rest {
                    Some(_) => {
                        suffix.push(arg.pat);
                    }
                    None if is_spread => {
                        assert!(rest.is_none());
                        rest = Some(arg.pat);
                    }
                    None => {
                        prefix.push(arg.pat);
                    }
                }
            }
        });

        (prefix, suffix, rest)
    }
}

/// Spread pattern
#[derive(Clone, Debug, Copy)]
pub struct SpreadPat {
    /// Associated bind to the spread
    pub name: Option<Identifier>,
}

/// A conditional pattern, containing a pattern and an condition.
#[derive(Clone, Debug, Copy)]
pub struct IfPat {
    pub pat: PatId,
    pub condition: TermId,
}

/// A module pattern, containing a list of patterns to be used to match module
/// members.
#[derive(Clone, Debug, Copy)]
pub struct ModPat {
    pub members: PatArgsId,
}

/// A range pattern containing two terms `lo` and `hi`, and
/// an `end` kind which specifies if the [RangePat] is a
/// closed range or not.
///
/// The `lo` and `hi` values must be `Term::Level0(Level0Term::Lit)`.
#[derive(Clone, Debug, Copy)]
pub struct RangePat {
    /// Start value of the range, must be a literal term.
    pub lo: TermId,
    /// End value of the range, must be a literal term.
    pub hi: TermId,
    /// If the range is closed or not.
    pub end: RangeEnd,
}

/// Represents a pattern at the typechecking stage.
#[derive(Clone, Debug)]
pub enum Pat {
    /// Binding pattern.
    Binding(BindingPat),
    /// Access pattern.
    Access(AccessPat),
    /// Resolved binding pattern.
    Const(ConstPat),
    /// A range pattern `2..5
    Range(RangePat),
    /// Literal pattern, of the given term.
    ///
    /// The inner term must be `Term::Level0(Level0Term::Lit)`.
    Lit(TermId),
    /// Tuple pattern.
    Tuple(PatArgsId),
    /// Module pattern.
    Mod(ModPat),
    /// Constructor pattern.
    Constructor(ConstructorPat),
    /// List pattern
    Array(ArrayPat),
    /// Spread pattern, which represents a pattern that captures a range of
    /// items within a list pattern
    Spread(SpreadPat),
    /// A set of patterns that are OR-ed together. If any one of them matches
    /// then the whole pattern matches.
    Or(Vec<PatId>),
    /// A conditional pattern.
    If(IfPat),
    /// A wildcard pattern, ignoring the subject and always matching.
    Wild,
}

impl Pat {
    /// Check if the pattern is of the [Pat::Spread] variant.
    pub fn is_spread(&self) -> bool {
        matches!(self, Pat::Spread(_))
    }

    /// Check if this pattern is a or-pattern
    pub fn is_or(&self) -> bool {
        matches!(self, Pat::Or(_))
    }

    /// Check if the pattern is of the [Pat::Spread] variant.
    pub fn is_bind(&self) -> bool {
        matches!(self, Pat::Binding(_))
    }

    /// Check if the pattern is wrapped with an `if` guard.
    pub fn is_if(&self) -> bool {
        matches!(self, Pat::If(_))
    }

    /// Convert the pattern into a binding pattern, if it is one.
    pub fn into_bind(self) -> Option<BindingPat> {
        match self {
            Pat::Binding(pat) => Some(pat),
            _ => None,
        }
    }
}

new_store_key!(pub PatId);
new_store!(pub PatStore<PatId, Pat>);

new_sequence_store_key!(pub PatArgsId);
pub type PatArgsStore = ParamListStore<PatArgsId, PatArg>;

impl PrepareForFormatting for PatArgsId {}
impl PrepareForFormatting for PatId {}

impl fmt::Display for ForFormatting<'_, PatId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let pat = self.global_storage.pat_store.get(self.t);

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

                write!(f, "{visibility}{mutability}{}", binding.name)
            }
            Pat::Access(AccessPat { subject, property }) => {
                write!(f, "{property}::{}", subject.for_formatting(self.global_storage))
            }
            Pat::Const(ConstPat { term }) => {
                term.for_formatting_with_opts(self.global_storage, self.opts).fmt(f)
            }
            Pat::Range(RangePat { lo, hi, end }) => {
                // write the `lo`, then the range end, and finally the `hi`
                write!(
                    f,
                    "{}{}{}",
                    lo.for_formatting_with_opts(self.global_storage, self.opts),
                    end,
                    hi.for_formatting_with_opts(self.global_storage, self.opts)
                )
            }
            Pat::Lit(term) => term.for_formatting_with_opts(self.global_storage, self.opts).fmt(f),
            Pat::Tuple(tuple_pat) => {
                write!(f, "({})", tuple_pat.for_formatting(self.global_storage))
            }
            Pat::Constructor(constructor_pat) => {
                write!(
                    f,
                    "{}({})",
                    constructor_pat.subject.for_formatting(self.global_storage),
                    constructor_pat.args.for_formatting(self.global_storage)
                )
            }
            Pat::Or(pats) => {
                if pats.is_empty() {
                    write!(f, "{{empty or pattern}}")?;
                    Ok(())
                } else {
                    for (i, pat_id) in pats.iter().enumerate() {
                        write!(
                            f,
                            "({})",
                            pat_id.for_formatting_with_opts(self.global_storage, self.opts)
                        )?;

                        if i != pats.len() - 1 {
                            write!(f, " | ")?;
                        }
                    }
                    Ok(())
                }
            }
            Pat::If(if_pat) => {
                write!(
                    f,
                    "({}) if ({})",
                    if_pat.pat.for_formatting(self.global_storage),
                    if_pat.condition.for_formatting(self.global_storage),
                )?;

                Ok(())
            }
            Pat::Wild => {
                write!(f, "_")
            }
            Pat::Mod(ModPat { members }) => {
                self.global_storage.pat_args_store.map_as_param_list_fast(members, |pat_args| {
                    write!(f, "{{ ")?;
                    for (i, arg) in pat_args.positional().iter().enumerate() {
                        match arg.name {
                            Some(arg_name) => {
                                write!(
                                    f,
                                    "{} as {}",
                                    arg_name,
                                    arg.pat.for_formatting(self.global_storage)
                                )?;
                            }
                            None => {
                                write!(f, "{}", arg.pat.for_formatting(self.global_storage))?;
                            }
                        }
                        if i != pat_args.positional().len() - 1 {
                            write!(f, "; ")?;
                        }
                    }
                    write!(f, " }}")?;

                    Ok(())
                })
            }
            Pat::Array(ArrayPat { element_pats: inner, .. }) => {
                write!(f, "[{}]", inner.for_formatting(self.global_storage))
            }
            Pat::Spread(SpreadPat { name }) => {
                write!(f, "...")?;

                // Write the name bind, if it exists
                if let Some(name) = name {
                    write!(f, "{name}")?;
                }

                Ok(())
            }
        }
    }
}

impl fmt::Debug for ForFormatting<'_, PatId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.global_storage.pat_store.get(self.t))
    }
}

impl fmt::Display for ForFormatting<'_, PatArgsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let pat_args_id = self.t;

        self.global_storage.pat_args_store.map_as_param_list_fast(pat_args_id, |pat_args| {
            for (i, arg) in pat_args.positional().iter().enumerate() {
                match arg.name {
                    Some(arg_name) => {
                        write!(
                            f,
                            "{} = {}",
                            arg_name,
                            arg.pat.for_formatting(self.global_storage)
                        )?;
                    }
                    None => {
                        write!(f, "{}", arg.pat.for_formatting(self.global_storage))?;
                    }
                }
                if i != pat_args.positional().len() - 1 {
                    write!(f, ", ")?;
                }
            }

            Ok(())
        })
    }
}

#[cfg(all(target_arch = "x86_64", target_pointer_width = "64"))]
mod size_asserts {
    use hash_utils::assert::static_assert_size;

    use super::*;

    static_assert_size!(Pat, 32);
}
