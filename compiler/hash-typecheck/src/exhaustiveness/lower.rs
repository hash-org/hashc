//! Lowering utilities from a [primitives::Pat] into a [Pat]. The
//! [Pat] is an intermediate data structure that represents a
//! simplification of the [primitives::Pat] since a lot of
//! the information that is stored within the [primitives::Pat] is
//! not necessary for the exhaustiveness checking to be carried out.
use crate::{
    diagnostics::macros::tc_panic,
    exhaustiveness::constant::Constant,
    ops::AccessToOps,
    storage::{
        primitives::{
            self, ConstructorPat, Level0Term, Level1Term, ListPat, LitTerm, NominalDef,
            NominalDefId, PatArg, PatArgsId, PatId, Term, TermId,
        },
        AccessToStorage, StorageRef,
    },
};
use hash_source::{location::Span, string::Str};
use if_chain::if_chain;
use itertools::Itertools;

#[derive(Debug, Clone)]
pub struct FieldPat {
    /// Relative to the associated definition
    pub(crate) index: usize,
    /// Pattern associated with this field
    pub(crate) pat: Pat,
}

/// [PatKind] represents a lowered form of patterns from [primitives::Pat]. This
/// removes unnecessary information about the actual pattern which doesn't
/// affect exhaustiveness and usefulness checking.
///
/// @@Future: we might need to introduce a new variant `Binding` if we introduce
/// patterns that can bind a name to a sub-pattern (as in rust `p @ ...PAT...`)
#[derive(Debug, Clone)]
pub enum PatKind {
    /// Wildcard match `_`
    Wild,

    /// Used to represent a spread pattern. It is used to temporarily build
    /// a [PatKind::List], later is thrown away and converted into a
    /// [PatKind::Wild] to simplify exhaustiveness checking.
    Spread,

    // Used to represent a constant pattern range, for integers and floats.
    //
    // **Note** currently only used to represent groupings of constants, as
    // range patterns aren't implemented yet!
    // Range {
    //     lo: Constant,
    //     hi: Constant,
    //     end: RangeEnd,
    // },
    ///

    /// Some constant value like a `char`, `u32`, etc. Booleans don't appear
    /// here because they are internally represented as enumerations.
    Constant {
        value: Constant,
    },

    /// Interned string pattern
    Str {
        value: Str,
    },

    /// A variant within an enumeration, e.g. `Some(3)`
    Variant {
        /// The id of the nominal definition that represents the enumeration.
        ///
        /// @@EnumToUnion: Replace this with id of union of structs, when
        /// `enum`s are no longer represented within `NominalDefId`
        def: NominalDefId,
        /// The inner patterns of the variant
        pats: Vec<FieldPat>,
        /// Which variant this variant represents within the parent definition.
        index: usize,
    },

    /// Essentially [PatKind::Variant], but for nominal definitions that only
    /// have one possible definition such as a struct `Dog(name = "..", ..)
    /// or tuple `(..)`.
    Leaf {
        pats: Vec<FieldPat>,
    },

    /// List pattern, holds the patterns that go before and after an
    /// optional `spread` pattern that is represented as a `wildcard`
    /// pattern.
    ///
    /// If the spread appears at the start of the list, then `prefix`
    /// pats will be empty, and the same applies if it appears at the
    /// end for `suffix`.
    List {
        // Patterns that precede an optional `...` spread selection
        prefix: Vec<Pat>,
        // The optional `...` spread
        spread: Option<Pat>,
        // Patterns that succeed an optional `...` spread selection
        suffix: Vec<Pat>,
    },

    // An `or` pattern, containing inner patterns that the `or` is applied onto.
    Or {
        pats: Vec<Pat>,
    },
}

/// General representation of a lowered pattern ready for exhaustiveness
/// analysis.
#[derive(Debug, Clone)]
pub struct Pat {
    /// Associated pattern span
    pub span: Span,
    /// The kind of the pattern
    pub kind: Box<PatKind>,
    /// If the pattern has an associated if-guard condition.
    pub has_guard: bool,
}

pub struct LowerPatOps<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for LowerPatOps<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> LowerPatOps<'tc> {
    /// Create a new [LowerPatOps].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Take a [primitives::Pat] and convert it into [Pat], essentially lowering
    /// the pattern.
    pub fn lower_pat(&self, id: PatId) -> Pat {
        let reader = self.reader();

        let pat = reader.get_pat(id);
        let span = self.location_store().get_span(id).unwrap();

        // Convert the pattern into a kind
        let kind = match pat {
            primitives::Pat::Binding(_)
            | primitives::Pat::Access(_)
            | primitives::Pat::Const(_)
            | primitives::Pat::Wild
            | primitives::Pat::Mod(_) => PatKind::Wild,
            primitives::Pat::Spread(_) => PatKind::Spread,
            primitives::Pat::Lit(term) => return self.lower_constant(id, *term, span),
            // Tuple patterns are represented as leaves since they can't have alternative
            // variants
            primitives::Pat::Tuple(fields) => {
                let pats = self.lower_pat_fields(*fields);
                PatKind::Leaf { pats }
            }
            primitives::Pat::Constructor(_) => {
                return self.lower_constructor(pat.clone(), span);
            }
            primitives::Pat::List(ListPat { inner, .. }) => {
                let mut prefix = vec![];
                let mut suffix = vec![];
                let mut spread = None;

                let pats = reader.get_pat_args(*inner).clone();

                // We don't care about the `name` of the arg because the list
                // never has the `name` assigned to anything...
                for PatArg { pat, .. } in pats.positional() {
                    let mut lowered_pat = self.lower_pat(*pat);

                    if matches!(lowered_pat.kind.as_ref(), PatKind::Spread) {
                        if spread.is_some() {
                            tc_panic!(pat, self, "found multiple spread patterns within list");
                        }

                        // Overwrite the kind into `Wild` to simplify things
                        let _ = std::mem::replace(&mut *lowered_pat.kind, PatKind::Wild);
                        spread = Some(lowered_pat);
                    } else {
                        match spread {
                            Some(_) => suffix.push(lowered_pat),
                            None => prefix.push(lowered_pat),
                        }
                    }
                }

                PatKind::List { prefix, spread, suffix }
            }
            primitives::Pat::Or(pats) => PatKind::Or {
                pats: pats.clone().into_iter().map(|pat| self.lower_pat(pat)).collect_vec(),
            },
            primitives::Pat::If(if_pat) => {
                // we need to set `has_guard` to true on the pattern
                let mut inner = self.lower_pat(if_pat.pat);
                inner.has_guard = true;

                return inner;
            }
            primitives::Pat::Range { .. } => todo!(),
        };

        Pat { span, kind: Box::new(kind), has_guard: false }
    }

    /// Function to lower a [primitives::Pat::DeconstructedCtor]. If the
    /// constructor subject is an enum variant, it will create a
    /// [PatKind::Variant] pattern, otherwise it uses [PatKind::Leaf] to
    /// represent other definitions.
    ///
    /// **Note** the term of the subject of the constructor must be simplified!
    pub fn lower_constructor(&self, pat: primitives::Pat, span: Span) -> Pat {
        let ConstructorPat { subject, args } = match pat {
            primitives::Pat::Constructor(constructor) => constructor,
            _ => unreachable!(),
        };

        // Transform the arguments into fields, since it doesn't matter
        // whether this will become a variant or a leaf.
        let pats = self.lower_pat_fields(args);

        // We need to determine if this is a enumeration or a struct, if it is a
        // struct, we can easily conclude that this lowered pattern is a `Leaf`,
        // otherwise it becomes a variant kind
        let reader = self.reader();
        let term = reader.get_term(subject);

        let kind = match term {
            primitives::Term::Level1(Level1Term::NominalDef(id)) => {
                let nominal_def = reader.get_nominal_def(*id);

                match nominal_def {
                    NominalDef::Struct(_) => PatKind::Leaf { pats },
                    // @@EnumToUnion: get the variant index here
                    NominalDef::Enum(_) => unreachable!(),
                }
            }
            // Was the subject not simplified :^( ?
            _ => tc_panic!(subject, self, "Not a nominal!"),
        };

        Pat { kind: Box::new(kind), span, has_guard: false }
    }

    /// Function to lower a collection of pattern fields. This is used for
    /// tuple and constructor patterns. This function takes account of whether
    /// fields are named or not, and properly computes the `index` of each
    /// field based on the definition position and whether or not it is a
    /// named argument.
    pub fn lower_pat_fields(&self, fields: PatArgsId) -> Vec<FieldPat> {
        let reader = self.reader();
        let args = reader.get_pat_args(fields).clone();

        let pats = args
            .positional()
            .iter()
            .enumerate()
            // This tries to resolve the `index` of the argument that is being passed
            // within the tuple field. If the tuple has named arguments, then we have
            // to use the parameter list in order to resolve the index. By now it should be
            // verified that no un-named arguments appear after named arguments as this
            // creates an ambiguous ordering of arguments.
            .map(|(index, arg)| -> FieldPat {
                let field = if_chain! {
                    if let Some(name) = arg.name;
                    if let Some((arg_index, _)) = args.get_by_name(name);
                    then {
                        arg_index
                    } else {
                        index
                    }
                };

                FieldPat { index: field, pat: self.lower_pat(arg.pat) }
            })
            .collect_vec();

        pats
    }

    /// Function that performs a lowering operation on a [Level0Term::Lit] and
    /// converts it into a [PatKind::Constant] or a [PatKind::Str] if it is
    /// a string.
    pub fn lower_constant(&self, pat: PatId, ty: TermId, span: Span) -> Pat {
        let reader = self.reader();
        let value = reader.get_term(ty);

        let kind = match value {
            Term::Level0(Level0Term::Lit(lit)) => match lit {
                LitTerm::Str(value) => PatKind::Str { value: *value },
                LitTerm::Int { value, kind } => {
                    PatKind::Constant { value: Constant::from_int(value.clone(), *kind, ty) }
                }
                LitTerm::Char(value) => {
                    PatKind::Constant { value: Constant::from_char(*value, ty) }
                }
            },
            _ => tc_panic!(pat, self, "Not a constant!"),
        };

        Pat { kind: Box::new(kind), span, has_guard: false }
    }
}
