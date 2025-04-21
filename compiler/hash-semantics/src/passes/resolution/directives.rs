//! Utilities for processing and expanding any directives that need to be
//! applied before continuing processing of the TIR.

use hash_ast::ast;
use hash_source::identifier::IDENTS;
use hash_tir::{
    intrinsics::definitions::Intrinsic,
    tir::{Arg, CallTerm, NodeOrigin, Term, TermId},
};

use crate::{
    SemanticEnv,
    passes::{ResolutionPass, SemanticResult},
};

impl<E: SemanticEnv> ResolutionPass<'_, E> {
    /// Apply and expand any directives that are presently applying to the
    /// application.
    pub(super) fn apply_directives(
        &self,
        macros: Option<&ast::AstNode<ast::MacroInvocations>>,
        subject: ast::AstNodeRef<ast::Expr>,
    ) -> SemanticResult<TermId> {
        // Construct the term that's to be applied
        let mut subject = self.make_term_from_ast_expr(subject)?;

        let Some(macros) = macros else {
            // If no macros are present, then we can return the subject
            // as-is.
            return Ok(subject);
        };

        // We need to walk the macros backwards and expand them as appropriate.
        for invocation in macros.ast_ref().body().invocations.iter().rev() {
            let origin = NodeOrigin::ComputedFrom(invocation.id());

            // Check what kind of invocation we have.
            match invocation.name.ident {
                n if n == IDENTS.size_of => {
                    subject = Term::from(
                        CallTerm {
                            subject: Term::from(Term::Intrinsic(Intrinsic::SizeOf), origin),
                            args: Arg::seq_positional([subject], origin),
                            implicit: false,
                        },
                        origin,
                    );
                }
                _ => {
                    // Don't do anything, but potentially emit a warning for an
                    // unknown directive (as we should of
                    // caught it here?)
                }
            }
        }

        Ok(subject)
    }
}
