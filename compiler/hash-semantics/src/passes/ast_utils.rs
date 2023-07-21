use hash_ast::{
    ast::{self, AstNodeRef, BodyBlock, Module, OwnsAstNode},
    node_map::SourceRef,
};
use hash_tir::symbols::{sym, Symbol};

use crate::{diagnostics::error::SemanticResult, environment::sem_env::AccessToSemEnv};

pub trait AstPass: AccessToSemEnv {
    fn pass_interactive(&self, node: AstNodeRef<BodyBlock>) -> SemanticResult<()>;
    fn pass_module(&self, node: AstNodeRef<Module>) -> SemanticResult<()>;

    /// Called before the pass starts, returns `true` if the pass should go
    /// ahead
    fn pre_pass(&self) -> SemanticResult<bool> {
        Ok(true)
    }

    /// Called after the pass has finished
    fn post_pass(&self) -> SemanticResult<()> {
        Ok(())
    }

    fn pass_source(&self) -> SemanticResult<()> {
        if self.pre_pass()? {
            let source = self.node_map().get_source(self.current_source_info().source_id());
            match source {
                SourceRef::Interactive(interactive_source) => {
                    self.pass_interactive(interactive_source.node_ref())?
                }
                SourceRef::Module(module_source) => self.pass_module(module_source.node_ref())?,
            };
            self.post_pass()?;
            Ok(())
        } else {
            Ok(())
        }
    }
}

pub trait AstUtils: AccessToSemEnv {
    /// Create a [`Symbol`] for the given [`ast::Name`], or a fresh symbol if no
    /// name is provided.
    fn new_symbol_from_ast_name(&self, name: Option<&ast::AstNode<ast::Name>>) -> Symbol {
        match name {
            Some(name) => sym(name.ident),
            None => Symbol::fresh(),
        }
    }
}

impl<T: AccessToSemEnv> AstUtils for T {}
