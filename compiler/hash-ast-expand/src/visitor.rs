use std::convert::Infallible;

use hash_ast::{
    ast::{AstNode, Name},
    ast_visitor_mut_self_default_impl,
    tree::AstTreeGenerator,
    visitor::{walk_mut_self, AstVisitor, AstVisitorMutSelf},
};
use hash_fmt::AstPrinter;
use hash_pipeline::{
    interface::CompilerOutputStream,
    settings::{AstDumpMode, CompilerSettings},
};
use hash_source::{
    identifier::IDENTS,
    location::{SourceLocation, Span},
    SourceId, SourceMap,
};
use hash_utils::{
    stream_writeln,
    tree_writing::{TreeNode, TreeWriter, TreeWriterConfig},
};

#[derive(Debug)]
pub struct AstExpander<'s> {
    /// The map of the current workspace sources.
    pub(crate) source_map: &'s SourceMap,
    /// The `id` of the module that is currently being checked
    source_id: SourceId,

    /// The settings to the AST expansion pass.
    pub(crate) settings: &'s CompilerSettings,

    /// The [CompilerOutputStream] that will be used to dump the AST.
    stdout: CompilerOutputStream,
}

impl<'s> AstExpander<'s> {
    /// Create a new [AstDesugaring]. Contains the [SourceMap] and the
    /// current id of the source in reference.
    pub fn new(
        source_map: &'s SourceMap,
        source_id: SourceId,
        settings: &'s CompilerSettings,
        stdout: CompilerOutputStream,
    ) -> Self {
        Self { source_map, settings, source_id, stdout }
    }

    /// Create a [SourceLocation] from a [Span]
    pub(crate) fn source_location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, id: self.source_id }
    }
}

impl<'s> AstVisitorMutSelf for AstExpander<'s> {
    type Error = Infallible;

    ast_visitor_mut_self_default_impl!(hiding: DirectiveExpr);

    type DirectiveExprRet = ();
    fn visit_directive_expr(
        &mut self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let _ = walk_mut_self::walk_directive_expr(self, node);

        let mut write_tree = |index| {
            let ast_settings = self.settings.ast_settings();

            // We want to get the total span of the subject, so we must
            // include the span of the directives that come after the `dump_ast` directive.
            let directive_span = if let Some(directive) = node.directives.get(index + 1) {
                let directive: &AstNode<Name> = directive; // @@RustBug: for some reason it can't infer the type here, maybe `smallvec`
                                                           // related?
                directive.span().join(node.subject.span())
            } else {
                node.subject.span()
            };
            let location = self.source_location(directive_span);

            stream_writeln!(self.stdout, "AST dump for {}", self.source_map.fmt_location(location));

            match ast_settings.dump_mode {
                AstDumpMode::Pretty => {
                    let mut printer = AstPrinter::new(&mut self.stdout);
                    printer.visit_expr(node.subject.ast_ref()).unwrap();
                }
                AstDumpMode::Tree => {
                    let mut tree = AstTreeGenerator.visit_expr(node.subject.ast_ref()).unwrap();

                    // Since this might be a non-singular directive, we also might
                    // need to wrap the tree in a any of the directives that were specified
                    // after the `dump_ast` directive.
                    for directive in node.directives.iter().skip(index + 1).rev() {
                        tree = TreeNode::branch(
                            format!("directive \"{}\"", directive.ident),
                            vec![tree],
                        );
                    }

                    stream_writeln!(
                        self.stdout,
                        "{}",
                        TreeWriter::new_with_config(
                            &tree,
                            TreeWriterConfig::from_character_set(self.settings.character_set)
                        )
                    );
                }
            }
        };

        // for the `dump_ast` directive, we essentially "dump" the generated tree
        // that the parser created. We emit this tree regardless of whether or not
        // there will be errors later on in the compilation stage.
        for (index, directive) in node.directives.iter().enumerate() {
            if directive.is(IDENTS.dump_ast) {
                write_tree(index)
            }
        }

        Ok(())
    }
}
