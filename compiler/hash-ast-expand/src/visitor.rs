use std::convert::Infallible;

use hash_ast::{
    ast_visitor_mut_self_default_impl,
    tree::AstTreeGenerator,
    visitor::{walk_mut_self, AstVisitor, AstVisitorMutSelf},
};
use hash_pipeline::interface::CompilerOutputStream;
use hash_source::{
    identifier::IDENTS,
    location::{SourceLocation, Span},
    SourceId, SourceMap,
};
use hash_utils::tree_writing::TreeWriter;

#[derive(Debug)]
pub struct AstExpander<'s> {
    /// The map of the current workspace sources.
    pub(crate) source_map: &'s SourceMap,
    /// The `id` of the module that is currently being checked
    source_id: SourceId,

    /// The [CompilerOutputStream] that will be used to dump the AST.
    stdout: CompilerOutputStream,
}

impl<'s> AstExpander<'s> {
    /// Create a new [AstDesugaring]. Contains the [SourceMap] and the
    /// current id of the source in reference.
    pub fn new(
        source_map: &'s SourceMap,
        source_id: SourceId,
        stdout: CompilerOutputStream,
    ) -> Self {
        Self { source_map, source_id, stdout }
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

        // for the `dump_ast` directive, we essentially "dump" the generated tree
        // that the parser created. We emit this tree regardless of whether or not
        // there will be errors later on in the compilation stage.
        if node.name.is(IDENTS.dump_ast) {
            let tree = AstTreeGenerator.visit_expr(node.subject.ast_ref()).unwrap();
            let location = self.source_location(node.subject.span());

            self.stdout.writeln(&format!(
                "AST dump for {}\n{}",
                self.source_map.fmt_location(location),
                TreeWriter::new(&tree)
            ));
        }

        Ok(())
    }
}
