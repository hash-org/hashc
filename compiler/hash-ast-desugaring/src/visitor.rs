use std::convert::Infallible;

use hash_ast::{
    ast::Block,
    ast_visitor_mut_default_impl,
    visitor::{walk_mut, AstVisitorMut},
};
use hash_source::SourceMap;

#[derive(Debug)]
pub struct AstDesugaring<'s> {
    pub(crate) source_map: &'s SourceMap,
}

impl<'s> AstDesugaring<'s> {
    /// Create a new [AstDesugaring]. Contains the [SourceMap] and the
    /// current id of the source in reference.
    pub fn new(source_map: &'s SourceMap) -> Self {
        Self { source_map }
    }
}

impl<'s> AstVisitorMut for AstDesugaring<'s> {
    type Error = Infallible;
    ast_visitor_mut_default_impl!(hiding: Block);

    type BlockRet = ();

    fn visit_block(
        &mut self,
        mut node: hash_ast::ast::AstNodeRefMut<hash_ast::ast::Block>,
    ) -> Result<Self::BlockRet, Self::Error> {
        let parent_span = node.span();

        // Check if this is a for, while, or if block and then apply the appropriate
        // transformations.
        match node.body() {
            Block::For(_) => {
                node.replace(|old| self.desugar_for_loop_block(old, parent_span));
            }
            Block::While(_) => {
                node.replace(|old| self.desugar_while_loop_block(old, parent_span));
            }
            Block::If(_) => {
                node.replace(|old| self.desugar_if_block(old, parent_span));
            }
            _ => {}
        };

        // We still need to walk the block now
        let _ = walk_mut::walk_block(self, node);

        Ok(())
    }
}
