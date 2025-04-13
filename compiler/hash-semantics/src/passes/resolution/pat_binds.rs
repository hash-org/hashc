//! Sources for [PatBindsChecker]. The [PatBindsChecker] is used to ensure the
//! three following things:
//!
//! 1. Binds declared in variants must be the same.
//!
//! 2. Each declared bind in a variant must have the same mutability.
//!
//! 3. Binds in a single pattern must be unique.
//!
//! The [PatBindsChecker] simply recursively traverses a pattern whilst
//! maintaining a [PatBinds] record of each bind. When it encounters pattern
//! alternatives, the checker ensures that each alternative produces the same
//! [PatBinds]. The algorithm for comparing alternative [PatBinds] is specified
//! in [`PatBinds::compare`].
//!
//! Similarly, when the checker walks a "compound" pattern, i.e. a pattern made
//! of sub-patterns like a tuple or an array, the checker combines all of the
//! sub-pattern [PatBinds] into a single [PatBinds] record. The combination
//! algorithm is specified in [`PatBinds::merge`].

use derive_more::{Constructor, Deref};
use hash_ast::ast::{self, AstNodeId, AstNodeRef, AstNodes, BindingPat};
use hash_source::{identifier::Identifier, location::Span};
use hash_utils::{
    fxhash::FxBuildHasher,
    indexmap::IndexMap,
    itertools::Itertools,
    thin_vec::{ThinVec, thin_vec},
};

use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult},
    env::SemanticEnv,
};

/// What kind of check needs to be performed on a pattern. Variants
/// [PatCheckKind::Args] and [PatCheckKind::List] are semantically equivalent,
/// but one is composed of a list of patterns whilst the other is a list of
/// [ast::PatArgs].
enum PatCheckKind<'ast> {
    /// Ensure that the pattern arguments have unique underlying bindings in
    /// each pattern argument.
    Args(&'ast AstNodes<ast::PatArg>, Option<AstNodeRef<'ast, ast::SpreadPat>>),

    /// Ensure that each pattern in the list has unique underlying bindings.
    List(&'ast AstNodes<ast::Pat>, Option<AstNodeRef<'ast, ast::SpreadPat>>),

    /// Ensure that each variant of the or-pattern has the same underlying
    /// bindings.
    Variant(&'ast AstNodes<ast::Pat>),

    /// Single, we found a single bind - we don't need to check it, but someone
    /// else might need to check it.
    Single(AstNodeRef<'ast, ast::BindingPat>),
}

impl<'ast> PatCheckKind<'ast> {
    /// Workout whether the given `pattern` needs a binding check, and
    /// specifically what kind of [PatCheckKind] it needs.
    fn classify_pat(pat: AstNodeRef<'ast, ast::Pat>) -> Option<Self> {
        match pat.body() {
            ast::Pat::Binding(bind) => Some(PatCheckKind::Single(pat.with_body(bind))),
            ast::Pat::Tuple(ast::TuplePat { fields, spread })
            | ast::Pat::Constructor(ast::ConstructorPat { fields, spread, .. }) => {
                Some(PatCheckKind::Args(fields, spread.as_ref().map(|s| s.ast_ref())))
            }
            ast::Pat::Array(ast::ArrayPat { fields, spread }) => {
                Some(PatCheckKind::List(fields, spread.as_ref().map(|s| s.ast_ref())))
            }
            ast::Pat::Or(ast::OrPat { variants }) => Some(PatCheckKind::Variant(variants)),
            ast::Pat::If(ast::IfPat { pat, .. }) => Self::classify_pat(pat.ast_ref()),
            ast::Pat::Module(_)
            | ast::Pat::Access(_)
            | ast::Pat::Lit(_)
            | ast::Pat::Wild(_)
            | ast::Pat::Macro(_)
            | ast::Pat::TokenMacro(_)
            | ast::Pat::Range(_) => None,
        }
    }
}

/// Wrapper type around a [PatId] in order to also include the
/// underlying [BindingPat] and provide some useful methods to
/// query information about the binding.
#[derive(Debug, Clone, Copy)]
pub struct Bind {
    /// The [Span] of the name in the bind, not the entire binding pattern.
    pat: AstNodeId,

    /// The name that is specified in the binding.
    name: Identifier,

    /// The [ast::Mutability] of the pattern.
    ///
    /// @@Future: perhaps we can use bitflags to also encode `visibility` and
    /// `ref/val`.
    mutability: ast::Mutability,
}

impl Bind {
    /// Get the [Identifier] of the [Bind].
    pub fn name(&self) -> Identifier {
        self.name
    }

    /// Get the mutability of the [Bind].
    pub fn mutable(&self) -> bool {
        self.mutability == ast::Mutability::Mutable
    }

    /// Get the span of the [Bind].
    pub fn span(&self) -> Span {
        self.pat.span()
    }
}

impl From<AstNodeRef<'_, BindingPat>> for Bind {
    fn from(pat: AstNodeRef<'_, BindingPat>) -> Self {
        Self {
            // In error reporting, we want to highlight the name specifically, we
            // don't really care if the bind has the `mut` or `pub` keywords.
            pat: pat.name.id(),
            name: pat.name.ident,
            mutability: pat.mutability.as_ref().map_or(ast::Mutability::Immutable, |m| *m.body()),
        }
    }
}

/// A record of the bindings that a [ast::Pat] contains. The `root` is a
/// reference to the pattern itself.
#[derive(Constructor, Debug)]
struct PatBinds {
    /// The pattern itself.
    root: AstNodeId,

    /// The bindings of the pattern.
    binds: IndexMap<Identifier, Bind, FxBuildHasher>,
}

impl PatBinds {
    /// Create an empty [PatBinds].
    fn empty(root: AstNodeId) -> Self {
        Self::new(root, IndexMap::default())
    }

    /// Create a new [PatBinds] from a single [BindingPat].
    fn single(root: AstNodeId, bind: AstNodeRef<BindingPat>) -> Self {
        let mut binds = Self::empty(root);
        binds.add_bind(bind);
        binds
    }

    /// Add a binding to the [PatBinds]. This function disregards the
    /// uniqueness of the binding, and will overwrite any existing binding
    /// with the same name. It is intended to be used to initialise an
    /// empty [PatBinds] with bindings.
    fn add_bind(&mut self, bind: AstNodeRef<BindingPat>) {
        let _ = self.add_unique_bind(bind);
    }

    /// Try to add the [BindingPat] into the [PatBinds] only if the binding
    /// doesn't already exist. If the binding does exist, we return the
    /// existing binding that is currently stored in the [PatBinds].
    #[inline]
    fn add_unique_bind(&mut self, pat: impl Into<Bind>) -> Option<Bind> {
        // Make the ne bind, and try to insert it.
        let bind = pat.into();
        self.binds.insert(bind.name, bind)
    }

    /// Check if the [PatBinds] is empty.
    fn is_empty(&self) -> bool {
        self.binds.is_empty()
    }

    /// Create an iterator over the bindings in the [PatBinds].
    fn iter(&self) -> impl Iterator<Item = (&Identifier, &Bind)> + '_ {
        self.binds.iter()
    }

    /// Merge two [PatBinds] together whilst checking that there are no
    /// naming conflicts between the two.
    fn merge(&mut self, other: &PatBinds) -> SemanticResult<()> {
        let mut errors = thin_vec![];

        // We iterate over the arguments, create a `PatBinds` for each argument, and
        // merge the current one with the previous ones. If we get any merging errors
        // (i.e. duplicate bindings), we return an error.
        for (_, bind) in other.iter() {
            if let Some(existing) = self.add_unique_bind(*bind) {
                errors.push(SemanticError::DuplicateBindInPat {
                    original: existing,
                    offending: *bind,
                });
            }
        }

        if errors.is_empty() { Ok(()) } else { Err(SemanticError::Compound { errors }) }
    }

    /// Compare two [PatBinds] and ensure all bindings are equal.
    ///
    /// For each bind, check the following things:
    ///
    /// 1. the `other` has a bind of the name `name` in it.
    ///
    /// 2. the bindings are the same, i.e. the mutability of the bindings is
    ///    equivalent.
    fn compare(&self, other: &PatBinds) -> SemanticResult<()> {
        let mut errors = thin_vec![];

        for (name, bind) in self.iter() {
            if let Some(other) = other.binds.get(name) {
                // Check that mutability of the bindings is the same.
                if bind.mutable() != other.mutable() {
                    errors.push(SemanticError::MismatchingPatBind {
                        original: *bind,
                        offending: *other,
                    });
                }
            } else {
                errors.push(SemanticError::MissingPatBind {
                    offending: other.root.span(),
                    missing: *bind,
                });
            }
        }

        // Also check backwards... but don't compare the binds if they do
        // exist since we've already checked them.
        for (name, bind) in other.iter() {
            if self.binds.get(name).is_none() {
                errors.push(SemanticError::MissingPatBind {
                    offending: self.root.span(),
                    missing: *bind,
                });
            }
        }

        if errors.is_empty() { Ok(()) } else { Err(SemanticError::Compound { errors }) }
    }
}

/// [PatBindsChecker] contains the traversal and error collecting logic
/// for pattern bind rule checking.
#[derive(Deref)]
pub struct PatBindsChecker<'env, E> {
    /// Collected errors that have been found.
    errors: ThinVec<SemanticError>,

    /// The ambient environment for target etc.
    #[deref]
    env: &'env E,
}

impl<'env, T: SemanticEnv> PatBindsChecker<'env, T> {
    /// Create a new [PatBindsChecker].
    pub(crate) fn new(env: &'env T) -> Self {
        Self { errors: ThinVec::new(), env }
    }

    /// Check that a given pattern adheres to the rules for bindings. The rules
    /// are as follows:
    ///
    /// - For all variants in a pattern, each variant must declare the same
    ///   bindings with the same types.
    ///
    /// - A binding cannot be used more than once in a single variant.
    ///
    /// @@Todo: this doesn't implement checks for the types of `spread`
    /// patterns.
    pub(crate) fn check(mut self, pat: AstNodeRef<ast::Pat>) -> SemanticResult<()> {
        let _ = self.check_pat_binds(pat)?;

        // If we got any "recoverable" errors during traversal, emit them!
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(SemanticError::Compound { errors: self.errors })
        }
    }

    /// This function actually performs the pattern binding check. If the
    /// bindings are valid, it returns a [PatBinds] object containing the
    /// bindings. If the bindings are invalid, it returns an error.
    fn check_pat_binds(&mut self, pat: AstNodeRef<ast::Pat>) -> SemanticResult<PatBinds> {
        // Slow-path: we need to check more thoroughly that the pattern bindings are
        // valid.
        if let Some(check) = PatCheckKind::classify_pat(pat) {
            let root = pat.id();

            match check {
                PatCheckKind::Args(pats, spread) => {
                    if let Some(spread) = spread
                        && spread.name.is_some()
                    {
                        unimplemented!("spread pattern binding checking isn't implemented yet.")
                    }

                    // @@Investigate what we have to do here for the names themselves?
                    let pats = pats.iter().map(|arg| arg.pat.ast_ref()).collect_vec();
                    self.check_compound_pat(root, &pats)
                }
                PatCheckKind::List(pats, spread) => {
                    if let Some(spread) = spread
                        && spread.name.is_some()
                    {
                        unimplemented!("spread pattern binding checking isn't implemented yet.")
                    }

                    let pats = pats.iter().map(|pat| pat.ast_ref()).collect_vec();
                    self.check_compound_pat(root, &pats)
                }
                PatCheckKind::Variant(variants) => self.check_pat_variants(root, variants),
                PatCheckKind::Single(bind) => Ok(PatBinds::single(root, bind)),
            }
        } else {
            // Fast-path: if the pattern is can't have variants, we don't need to perform
            // any checks on it.
            Ok(PatBinds::empty(pat.id()))
        }
    }

    /// Check that each pattern variant has equivalent [PatBinds].
    fn check_pat_variants(
        &mut self,
        root: AstNodeId,
        variants: &AstNodes<ast::Pat>,
    ) -> SemanticResult<PatBinds> {
        let variants = variants.iter().map(|variant| variant.ast_ref()).collect_vec();

        // If we didn't find any binds, then we don't need to check anything.
        let Some((first_binds, idx)) = self.find_binds(&variants)? else {
            return Ok(PatBinds::empty(root));
        };

        // Now we want to check the binds against every other bind...
        for (variant_idx, variant) in variants.iter().enumerate() {
            // we don't need to check against ourselves...
            if variant_idx == idx {
                continue;
            }

            // Get the bindings for this variant.
            let other_binds = if variant_idx < idx {
                PatBinds::empty(variant.id())
            } else {
                self.check_pat_binds(*variant)?
            };

            // Now we check the two binds...
            if let Err(err) = first_binds.compare(&other_binds) {
                self.errors.push(err);
            }
        }

        Ok(first_binds)
    }

    /// Check and construct the [PatBinds] for a compound pattern.
    fn check_compound_pat(
        &mut self,
        root: AstNodeId,
        pats: &[ast::AstNodeRef<ast::Pat>],
    ) -> SemanticResult<PatBinds> {
        // If we didn't find any binds, then we don't need to check anything.
        let Some((mut first_binds, idx)) = self.find_binds(pats)? else {
            return Ok(PatBinds::empty(root));
        };

        // Skip the first `idx` pats since we have already checked them.
        for pat in pats.iter().skip(idx + 1) {
            let other_binds = self.check_pat_binds(*pat)?;
            if let Err(err) = first_binds.merge(&other_binds) {
                self.errors.push(err)
            }
        }

        // Update the root of the first binds as being the root of the compound pattern.
        first_binds.root = root;
        Ok(first_binds)
    }

    /// Find the first pattern in a collection of patterns that produces
    /// a non-empty [PatBinds].
    fn find_binds(
        &mut self,
        pats: &[ast::AstNodeRef<ast::Pat>],
    ) -> SemanticResult<Option<(PatBinds, usize)>> {
        let mut idx = 0;

        // Compute the variant binds of the first variant, until we get
        // at least a `PatBinds`...
        while idx < pats.len() {
            let found = self.check_pat_binds(pats[idx])?;

            if !found.is_empty() {
                return Ok(Some((found, idx)));
            } else {
                idx += 1;
            }
        }

        Ok(None)
    }
}
