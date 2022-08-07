//! Hash semantic analysis module for validating various constructs relating to
//! patterns within the AST.

use hash_ast::ast::{AstNodes, Pat, TuplePatEntry};

use super::SemanticAnalyser;
use crate::diagnostics::{error::AnalysisErrorKind, origins::PatOrigin};

impl SemanticAnalyser<'_> {
    pub(crate) fn check_compound_pat_rules(
        &mut self,
        fields: &AstNodes<TuplePatEntry>,
        origin: PatOrigin,
    ) {
        let mut seen_spread_pat = false;
        let mut seen_named_field = false;

        // Verify that no spread patterns are present in the top level
        for field in fields.iter() {
            let TuplePatEntry { name, pat } = field.body();

            let is_spread_pat = matches!(pat.body(), Pat::Spread(_));

            // Detect an incorrect ordering of named-un/named arguments within the pattern
            if !is_spread_pat {
                if name.is_some() {
                    seen_named_field = true;
                } else if seen_named_field {
                    self.append_error(
                        AnalysisErrorKind::AmbiguousPatFieldOrder { origin },
                        field.span(),
                    );
                }
            }

            // We only care if this is a binding-free pattern entry, and we don't
            // care where the pattern occurs if it is after or before the named/un-named
            // argument order.
            if name.is_none() && is_spread_pat {
                if seen_spread_pat {
                    self.append_error(
                        AnalysisErrorKind::MultipleSpreadPats { origin: PatOrigin::Constructor },
                        field.span(),
                    );
                }

                seen_spread_pat = true;
            }
        }
    }

    /// Here we need to check that the list pattern only contains a single
    /// spread pattern since it wouldn't make sense for there to be multiple
    /// spread patterns. This is primarily because having multiple spreads
    /// would introduce ambiguity about which elements are captured by the
    /// spread. For example in the following pattern:
    /// ```ignore
    /// >>> [..., ...x]
    /// ```
    ///
    /// Note: this isn't the only case that is erroneous, in general any list
    /// pattern with multiple spread patterns is considered to be incorrect.
    ///
    /// Which parts does the `x` spread pattern capture? It's clear that this is
    /// ambiguous and should be disallowed within the list patten.
    pub(crate) fn check_list_pat(&mut self, fields: &AstNodes<Pat>) {
        // @@TODO: Rather than use a boolean, we should use a reference to the pattern
        // so that we can report an auxiliary span of where the initial use of the
        // pattern occurs.
        let mut seen_spread_pat = false;

        for field in fields.iter() {
            if matches!(field.body(), Pat::Spread(_)) {
                if seen_spread_pat {
                    self.append_error(
                        AnalysisErrorKind::MultipleSpreadPats { origin: PatOrigin::List },
                        field.span(),
                    );
                } else {
                    seen_spread_pat = true;
                }
            }
        }
    }
}
