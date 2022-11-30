use hash_ast::{
    ast::{AstNodeRef, BodyBlock, Module, OwnsAstNode},
    node_map::SourceRef,
};

use crate::new::{
    diagnostics::error::TcResult, environment::tc_env::AccessToTcEnv, ops::common::CommonOps,
};

pub trait AstPass: AccessToTcEnv {
    fn pass_interactive(&self, node: AstNodeRef<BodyBlock>) -> TcResult<()>;
    fn pass_module(&self, node: AstNodeRef<Module>) -> TcResult<()>;

    fn pass_source(&self) {
        let source = self.node_map().get_source(self.current_source_info().source_id);
        let result = match source {
            SourceRef::Interactive(interactive_source) => {
                self.pass_interactive(interactive_source.node_ref())
            }
            SourceRef::Module(module_source) => self.pass_module(module_source.node_ref()),
        };
        self.tc_env().try_or_add_error(result);
    }
}
