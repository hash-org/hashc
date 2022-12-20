// @@Docs
use self::{
    context_ops::ContextOps, data_ops::DataOps, def_ops::CommonDefOps, fn_ops::FnOps,
    infer_ops::InferOps, mod_ops::ModOps, param_ops::ParamOps, stack_ops::StackOps,
    tuple_ops::TupleOps,
};

pub mod ast_ops;
pub mod common_ops;
pub mod context_ops;
pub mod data_ops;
pub mod def_ops;
pub mod fn_ops;
pub mod infer_ops;
pub mod mod_ops;
pub mod oracle;
pub mod param_ops;
pub mod stack_ops;
pub mod tuple_ops;

macro_rules! ops {
    ($($name:ident: $ty:ty),* $(,)?) => {
        /// A trait that defines typechecking operations, which operate on [`TcEnv`].
        pub trait AccessToOps: $crate::new::environment::tc_env::AccessToTcEnv {
            $(
                fn $name(&self) -> $ty {
                    <$ty>::new(self.tc_env())
                }
            )*
        }
        impl<T: $crate::new::environment::tc_env::AccessToTcEnv> AccessToOps for T { }
    };
}

ops! {
  mod_ops: ModOps,
  data_ops: DataOps,
  stack_ops: StackOps,
  infer_ops: InferOps,
  common_def_ops: CommonDefOps,
  fn_ops: FnOps,
  param_ops: ParamOps,
  context_ops: ContextOps,
  tuple_ops: TupleOps,
}
