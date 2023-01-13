use derive_more::Constructor;
use hash_types::{impl_access_to_env, new::environment::env::Env};

#[derive(Constructor)]
pub struct IntrinsicDefinitions<'tc> {
    env: &'tc Env<'tc>,
}

impl_access_to_env!(IntrinsicDefinitions<'tc>);

impl<'tc> IntrinsicDefinitions<'tc> {
    pub fn define_intrinsics(&self) {
        todo!()
        // self.make_intrinsic(
        //     "panic",
        //     FnTy {
        //         implicit: false,
        //         pure: true,
        //         is_unsafe: false,
        //         params: self.new_empty_params(),
        //         return_ty: todo!(),
        //     },
        //     |_env, _| todo!(),
        // );
    }
}
