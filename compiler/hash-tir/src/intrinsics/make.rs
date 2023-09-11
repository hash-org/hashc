/// Generate intrinsics for the compiler.
///
/// Intrinsics are functions that can be invoked from within Hash, but are
/// implemented on the compiler-side. Each intrinsic has a `$name`, a set of
/// parameters `($($param_name:ident: $param_ty:expr),*)` and a return type
/// `$return_ty`.
///
/// The definition of all the intrinsics is given in `super::definitions`.
#[macro_export]
macro_rules! intrinsics {
    ($($name:ident := ($($param_name:ident: $param_ty:expr),*) -> $return_ty:expr => |$env:ident| $impl:expr;)*) => {
        use paste::paste;
        use $crate::{
            building::gen::{params, sym, ty},
            fns::FnTy,
            terms::TermId,
            intrinsics::*,
        };

        paste! {
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub enum Intrinsic {
                $(
                    [<$name:camel>],
                )*
            }
        }

        impl Intrinsic {
            pub fn try_from_name(name: Identifier) -> Option<Self> {
                match name.as_str() {
                    $(
                        stringify!($name) => paste! { Some(Intrinsic::[<$name:camel>]) },
                    )*
                    _ => None,
                }
            }
        }

        impl std::fmt::Display for Intrinsic {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "#{}", self.name())
            }
        }

        impl IsIntrinsic for Intrinsic {
            fn name(&self) -> Identifier {
                match self {
                    $(
                        paste! { Intrinsic::[<$name:camel>] } => paste! { [<$name:camel>] }.name(),
                    )*
                }
            }

            fn ty(&self) -> FnTy {
                match self {
                    $(
                        paste! { Intrinsic::[<$name:camel>] } => paste! { [<$name:camel>] }.ty(),
                    )*
                }
            }

            fn call<I: IntrinsicAbilities>(&self, env: I, args: &[TermId]) -> Result<Option<TermId>, String> {
                match self {
                    $(
                        paste! { Intrinsic::[<$name:camel>] } => paste! { [<$name:camel>] }.call(env, args),
                    )*
                }
            }
        }

        $(
            paste! {
                pub struct [<$name:camel>];
            }

            impl IsIntrinsic for paste! { [<$name:camel>] } {
                fn name(&self) -> Identifier {
                    stringify!($name).into()
                }

                fn ty(&self) -> FnTy {
                    #[allow(clippy::redundant_closure_call)]
                    #[allow(non_snake_case)]
                    #[allow(unused_variables)]
                    (|$($param_name,)*| {
                        FnTy::builder()
                            .params(params([$(($param_name, $param_ty, None)),*]))
                            .return_ty($return_ty)
                            .build()
                    })($(sym(stringify!($param_name))),*)
                }

                fn call<I: IntrinsicAbilities>(&self, env: I, args: &[TermId]) -> Result<Option<TermId>, String> {
                    match *args {
                        #[allow(non_snake_case)]
                        #[allow(unused_variables)]
                        [$($param_name,)*] => {
                            #[allow(clippy::redundant_closure_call)]
                            (|$env: I| $impl)(env)
                        },
                        _ => Err(format!("intrinisic `{}` has type {}, but got {} arguments", stringify!($name), self.ty(), args.len()))
                    }
                }
            }
        )*
    };
}
