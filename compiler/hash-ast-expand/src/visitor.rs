use std::convert::Infallible;

use hash_ast::{
    ast_visitor_default_impl,
    tree::AstTreeGenerator,
    visitor::{walk, AstVisitor},
};
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
}

impl<'s> AstExpander<'s> {
    /// Create a new [AstDesugaring]. Contains the [SourceMap] and the
    /// current id of the source in reference.
    pub fn new(source_map: &'s SourceMap, source_id: SourceId) -> Self {
        Self { source_map, source_id }
    }

    /// Create a [SourceLocation] from a [Span]
    pub(crate) fn source_location(&self, span: Span) -> SourceLocation {
        SourceLocation { span, id: self.source_id }
    }
}

impl<'s> AstVisitor for AstExpander<'s> {
    type Error = Infallible;

    ast_visitor_default_impl!(hiding: DirectiveExpr);

    type DirectiveExprRet = ();
    fn visit_directive_expr(
        &self,
        node: hash_ast::ast::AstNodeRef<hash_ast::ast::DirectiveExpr>,
    ) -> Result<Self::DirectiveExprRet, Self::Error> {
        let _ = walk::walk_directive_expr(self, node);

        // for the `dump_ast` directive, we essentially "dump" the generated tree
        // that the parser created. We emit this tree regardless of whether or not
        // there will be errors later on in the compilation stage.
        if node.name.is(IDENTS.dump_ast) {
            let tree = AstTreeGenerator.visit_expr(node.subject.ast_ref()).unwrap();
            let name = self.source_map.canonicalised_path_by_id(self.source_id);

            let location = self.source_location(node.subject.span());
            let span = self.source_map.get_column_row_span_for(location);

            println!("AST for {name}:{span}\n{}", TreeWriter::new(&tree));
        }

        Ok(())
    }
}
