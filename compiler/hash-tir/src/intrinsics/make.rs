use std::iter::once;

/// Generation macros for intrinsics and primitives.
use hash_source::identifier::Identifier;
use hash_storage::store::statics::SequenceStoreValue;
use hash_target::HasTarget;
use hash_utils::itertools::Itertools;

use super::definitions::{all_intrinsics_as_mod_members, all_primitives_as_mod_members};
use crate::{
    building::gen,
    context::HasContext,
    tir::{
        CtorDefId, DataDefId, FnTy, ModDef, ModDefId, ModKind, ModMember, ModMemberValue, Node,
        TermId,
    },
};

/// Functionality that is available to invoke from within intrinsics.
pub trait IntrinsicAbilities: HasContext + HasTarget {
    /// Normalise a term fully.
    fn normalise_term(&self, term: TermId) -> Result<Option<TermId>, String>;

    /// Resolve a term from the prelude.
    fn resolve_from_prelude(&self, name: impl Into<Identifier>) -> TermId;
}

/// Trait implemented by all intrinsics.
pub trait IsIntrinsic {
    /// Get the name of the intrinsic.
    fn name(&self) -> Identifier;

    /// Get the function type of the intrinsic.
    fn ty(&self) -> FnTy;

    /// Get the implementation of the intrinsic.
    fn call<I: IntrinsicAbilities>(
        &self,
        env: I,
        args: &[TermId],
    ) -> Result<Option<TermId>, String>;
}

/// Trait implemented by all primitives.
pub trait IsPrimitive {
    type Ctor: IsPrimitiveCtor;

    /// Get the name of the primitive.
    fn name(&self) -> Identifier;

    /// Get the [`DataDefId`] of the primitive.
    fn def(&self) -> DataDefId;

    /// Get the constructors of the primitive.
    fn ctors(&self) -> &'static [Self::Ctor];
}

/// Trait implemented by all primitive constructors.
pub trait IsPrimitiveCtor {
    /// Get the name of the constructor.
    fn name(&self) -> Identifier;

    /// Get the [`CtorDefId`] of the constructor.
    fn def(&self) -> CtorDefId;
}

/// Make a module containing all the primitives and intrinsics.
pub fn make_root_mod() -> ModDefId {
    // ##GeneratedOrigin: Primitives do not have a source location.
    let intrinsics_sym = gen::sym("Intrinsics");
    Node::create_gen(ModDef {
        name: gen::sym("Root"),
        kind: ModKind::Transparent,
        members: Node::create_gen(Node::<ModMember>::seq(
            all_primitives_as_mod_members()
                .iter()
                .copied()
                .chain(once(Node::gen(ModMember {
                    name: intrinsics_sym,
                    value: ModMemberValue::Mod(Node::create_gen(ModDef {
                        name: intrinsics_sym,
                        kind: ModKind::Transparent,
                        members: Node::create_gen(Node::<ModMember>::seq(
                            all_intrinsics_as_mod_members().iter().copied(),
                        )),
                    })),
                })))
                .collect_vec(),
        )),
    })
}

/// Generate intrinsics for the compiler.
///
/// Intrinsics are functions that can be invoked from within Hash, but are
/// implemented on the compiler-side. Each intrinsic has a `$name`, a set of
/// parameters `($($param_name:ident: $param_ty:expr),*)` and a return type
/// `$return_ty`.
///
/// The definition of all the intrinsics is given in `super::definitions`.
#[macro_export]
macro_rules! make_intrinsics {
    ($($name:ident := ($($param_name:ident: $param_ty:expr),*) -> $return_ty:expr => |$env:ident| $impl:expr;)*) => {
        paste! {
            /// The enum containing all the intrinsics.
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub enum Intrinsic {
                $(
                    [<$name:camel>],
                )*
            }
        }

        impl Intrinsic {
            /// Convenience function to get an intrinsic by name.
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
                write!(f, "{}", self.name())
            }
        }

        // ##GeneratedOrigin: Intrinsics do not have a source location.
        /// All the intrinsics as a tuple.
        pub fn all_intrinsics_as_mod_members() -> &'static [$crate::tir::Node<ModMember>] {
            use $crate::tir::Node;
            use $crate::tir::ModMemberValue;
            use std::sync::OnceLock;

            static INTRINSICS_MOD: OnceLock<Vec<Node<ModMember>>> = OnceLock::new();
            INTRINSICS_MOD.get_or_init(|| {
                paste! {
                    vec![
                        $(
                            Node::gen(ModMember {
                                name: sym(stringify!($name)),
                                value: ModMemberValue::Intrinsic(Intrinsic::[<$name:camel>]),
                            }),
                        )*
                    ]
                }
            })
        }

        /// Implements `IsIntrinsic` for `Intrinsic` by delegating to each `$name:camel Intrinsic`.
        impl IsIntrinsic for Intrinsic {
            fn name(&self) -> Identifier {
                match self {
                    $(
                        paste! { Intrinsic::[<$name:camel>] } => paste! { [<$name:camel Intrinsic>] }.name(),
                    )*
                }
            }

            fn ty(&self) -> FnTy {
                match self {
                    $(
                        paste! { Intrinsic::[<$name:camel>] } => paste! { [<$name:camel Intrinsic>] }.ty(),
                    )*
                }
            }

            fn call<I: IntrinsicAbilities>(&self, env: I, args: &[TermId]) -> Result<Option<TermId>, String> {
                match self {
                    $(
                        paste! { Intrinsic::[<$name:camel>] } => paste! { [<$name:camel Intrinsic>] }.call(env, args),
                    )*
                }
            }
        }

        $(
            paste! {
                // Unit struct to represent the intrinsic.
                #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
                pub struct [<$name:camel Intrinsic>];
            }

            impl IsIntrinsic for paste! { [<$name:camel Intrinsic>] } {
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

/// Generate primitives for the compiler.
///
/// Primitives are common core data types which are handled specially by the
/// compiler in many instances. They are represented by `DataDef`s which are
/// either using defined or primitive constructors.
///
/// The definition of all the primitives is given in `super::definitions`.
#[macro_export]
macro_rules! make_primitives {
    (
        $($name:ident :=
            $(primitive $(<($($prim_param_name:ident: $prim_param_ty:expr),*)>)? ($prim_ctor:expr))?
            $(
                data $(<($($param_name:ident: $param_ty:expr),*)>)?
                (
                    $(
                        $ctor_name:ident $(($($ctor_param_name:ident: $ctor_param_ty:expr),*))?:
                        $name_in_ctor:ident $(<($($ctor_arg:expr),*)>)?
                   ),*
                )
            )?;
        )*
    ) => {
        use $crate::intrinsics::make::*;

        paste! {
            /// All the primitives.
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub enum Primitive {
                $(
                    [<$name:camel>],
                )*
            }
        }

        paste! {
            /// All the defined constructors.
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub enum PrimitiveCtor {
                $(
                    $(
                        $(
                            [<$name:camel $ctor_name:camel>],
                        )*
                    )?
                )*
            }
        }

        impl Primitive {
            /// Convenience function to get a primitive by name.
            pub fn try_from_name(name: Identifier) -> Option<Self> {
                match name.as_str() {
                    $(
                        stringify!($name) => paste! { Some(Primitive::[<$name:camel>]) },
                    )*
                    _ => None,
                }
            }

            /// Convenience function to get a primitive by [`DataDefId`].
            pub fn try_from_def(def: DataDefId) -> Option<Self> {
                match def {
                    $(
                        d if paste! { d == [<$name:camel Primitive>].def() } => paste! { Some(Primitive::[<$name:camel>]) },
                    )*
                    _ => None,
                }
            }
        }

        impl std::fmt::Display for Primitive {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.name())
            }
        }


        // ##GeneratedOrigin: Intrinsics do not have a source location.
        /// All the primitives as module members.
        pub fn all_primitives_as_mod_members() -> &'static [$crate::tir::Node<ModMember>] {
            use $crate::tir::Node;
            use $crate::tir::ModMemberValue;
            use std::sync::OnceLock;

            static PRIMITIVES_MOD: OnceLock<Vec<Node<ModMember>>> = OnceLock::new();
            PRIMITIVES_MOD.get_or_init(|| {
                paste! {
                    vec![
                        $(
                            Node::gen(ModMember {
                                name: sym(stringify!($name)),
                                value: ModMemberValue::Data([<$name:camel Primitive>].def()),
                            }),
                        )*
                    ]
                }
            })
        }

        impl IsPrimitiveCtor for PrimitiveCtor {
            fn name(&self) -> Identifier {
                match *self {
                    $(
                        $(
                            $(
                                paste! { PrimitiveCtor::[<$name:camel $ctor_name:camel>] } => stringify!($ctor_name).into(),
                            )*
                        )?
                    )*
                }
            }

            fn def(&self) -> CtorDefId {
                match *self {
                    $(
                        $(
                            $(
                                paste! { PrimitiveCtor::[<$name:camel $ctor_name:camel>] } => paste! { [<$name:camel $ctor_name:camel Ctor>] }.def(),
                            )*
                        )?
                    )*
                }
            }
        }

        /// Implements `IsPrimitive` for `Primitive` by delegating to each `$name:camel Primitive`.
        impl IsPrimitive for Primitive {
            type Ctor = PrimitiveCtor;

            fn name(&self) -> Identifier {
                match *self {
                    $(
                        paste! { Primitive::[<$name:camel>] } => paste! { [<$name:camel Primitive>] }.name(),
                    )*
                }
            }

            fn def(&self) -> DataDefId {
                match *self {
                    $(
                        paste! { Primitive::[<$name:camel>] } => paste! { [<$name:camel Primitive>] }.def(),
                    )*
                }
            }

            fn ctors(&self) -> &'static [Self::Ctor] {
                match *self {
                    $(
                        paste! { Primitive::[<$name:camel>] } => &[
                            $(
                                $(
                                    paste! { PrimitiveCtor::[<$name:camel $ctor_name:camel>] },
                                )*
                            )?
                        ],
                    )*
                }
            }
        }

        $(
            paste! {
                // Unit struct to represent the primitive.
                #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
                pub struct [<$name:camel Primitive>];

                /// Convenience accessor for the `DataDefId` of the primitive.
                pub fn [<$name:snake _def>]() -> DataDefId {
                    [<$name:camel Primitive>].def()
                }

                $(
                    /// Convenience constructor for the type of the primitive with parameters (defined constructors).
                    #[allow(non_snake_case)]
                    pub fn [<$name:snake _ty>](
                        $($($param_name: TermId),*,)?
                        origin: $crate::tir::NodeOrigin,
                    ) -> TyId {
                        use $crate::tir::Ty;
                        use $crate::tir::Arg;
                        Ty::indexed_data_ty(
                            [<$name:camel Primitive>].def(),
                            Arg::seq_positional([$($($param_name,)*)?], origin),
                            origin
                        )
                    }

                    /// Convenience constructor for the type of the primitive with parameters (defined constructors).
                    /// This uses generated origin information.
                    #[allow(non_snake_case)]
                    pub fn [<$name:snake _gen_ty>](
                        $($($param_name: TermId),*)?
                    ) -> TyId {
                        use $crate::tir::Ty;
                        use $crate::tir::Arg;
                        Ty::indexed_data_ty(
                            [<$name:camel Primitive>].def(),
                            Arg::seq_positional([$($($param_name,)*)?], NodeOrigin::Generated),
                            NodeOrigin::Generated
                        )
                    }
                )?

                $(
                    /// Convenience constructor for the type of the primitive with parameters (primitive constructors).
                    #[allow(non_snake_case)]
                    pub fn [<$name:snake _ty>](
                        $($($prim_param_name: TermId),*,)?
                        origin: $crate::tir::NodeOrigin,
                    ) -> TyId {
                        use $crate::tir::Ty;
                        use $crate::tir::Arg;
                        Ty::indexed_data_ty(
                            [<$name:camel Primitive>].def(),
                            Arg::seq_positional([$($($prim_param_name,)*)?], origin),
                            origin
                        )
                    }

                    /// Convenience constructor for the type of the primitive with parameters (defined constructors).
                    /// This uses generated origin information.
                    #[allow(non_snake_case)]
                    pub fn [<$name:snake _gen_ty>](
                        $($($prim_param_name: TermId),*)?
                    ) -> TyId {
                        use $crate::tir::Ty;
                        use $crate::tir::Arg;
                        Ty::indexed_data_ty(
                            [<$name:camel Primitive>].def(),
                            Arg::seq_positional([$($($prim_param_name,)*)?], NodeOrigin::Generated),
                            NodeOrigin::Generated
                        )
                    }
                )?
            }

            paste! {
                // Enum to represent the defined constructors.
                #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
                pub enum [<$name:camel Ctor>] {
                    $(
                        $(
                            [<$ctor_name:camel>],
                        )*
                    )?
                }

                /// List of all the constructor names of the primitive.
                pub const [<$name:upper _ CTOR_NAMES>]: &'static [&'static str] = &[
                    $(
                        $(
                            stringify!($ctor_name),
                        )*
                    )?
                ];

                impl IsPrimitiveCtor for [<$name:camel Ctor>] {
                    fn name(&self) -> Identifier {
                        match *self {
                            $(
                                $(
                                    [<$name:camel Ctor>]::[<$ctor_name:camel>] => [<$name:camel $ctor_name:camel Ctor>].name(),
                                )*
                            )?
                        }
                    }

                    fn def(&self) -> CtorDefId {
                        match *self {
                            $(
                                $(
                                    [<$name:camel Ctor>]::[<$ctor_name:camel>] => [<$name:camel $ctor_name:camel Ctor>].def(),
                                )*
                            )?
                        }
                    }
                }
            }

            $(
                $(
                    paste! {
                        // Unit structs to represent the defined constructors.
                        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
                        pub struct [<$name:camel $ctor_name:camel Ctor>];

                        /// Convenience access to the constructor's `CtorDefId`.
                        pub fn [<$name:snake _ $ctor_name:snake _ctor>]() -> CtorDefId {
                            [<$name:camel $ctor_name:camel Ctor>].def()
                        }

                        impl IsPrimitiveCtor for [<$name:camel $ctor_name:camel Ctor>] {
                            fn name(&self) -> Identifier {
                                stringify!($ctor_name).into()
                            }

                            fn def(&self) -> CtorDefId {
                                use std::sync::OnceLock;
                                use hash_storage::store::TrivialSequenceStoreKey;
                                static DEF: OnceLock<CtorDefId> = OnceLock::new();

                                *DEF.get_or_init(|| {
                                    let ctors = [<$name:camel Primitive>].def().borrow().ctors;
                                    let ctor_idx = [<$name:upper _ CTOR_NAMES>]
                                        .iter()
                                        .position(|c| *c == stringify!($ctor_name))
                                        .unwrap();
                                    ctors.assert_defined().at(ctor_idx).unwrap()
                                })
                            }
                        }
                    }
                )*
            )?

            impl IsPrimitive for paste! { [<$name:camel Primitive>] } {
                type Ctor = paste! { [<$name:camel Ctor>] };

                fn name(&self) -> Identifier {
                    stringify!($name).into()
                }

                fn ctors(&self) -> &'static [Self::Ctor] {
                    &[
                        $(
                            $(
                                paste! { [<$name:camel Ctor>]::[<$ctor_name:camel>] },
                            )*
                        )?
                    ]
                }

                fn def(&self) -> DataDefId {
                    use std::sync::OnceLock;
                    static DEF: OnceLock<DataDefId> = OnceLock::new();

                    #[allow(clippy::redundant_closure_call)]
                    #[allow(non_snake_case)]
                    #[allow(unused_variables)]
                    *DEF.get_or_init(
                        // Handle defined constructors:
                        $(
                            || (
                                $(|$($param_name,)*|)? {
                                    indexed_enum_def(
                                        sym(self.name()),
                                        params([$($(($param_name, $param_ty, None)),*)?]),
                                        [
                                            $(
                                                #[allow(clippy::redundant_closure_call)]
                                                #[allow(non_snake_case)]
                                                #[allow(unused_variables)]
                                                ($(|$($ctor_param_name,)*|)? {
                                                    (
                                                        sym(stringify!($ctor_name)),
                                                        params([
                                                            $(
                                                                $(($ctor_param_name, $ctor_param_ty, None)),*
                                                            )?
                                                        ]),
                                                        // ##Hack: count the number of characters
                                                        // in the stringified arguments to
                                                        // determine if there are any
                                                        if stringify!($($($ctor_arg,)*)?).len() > 0 {
                                                            Some(args([$($($ctor_arg,)*)?]))
                                                        } else {
                                                            None
                                                        }
                                                    )
                                                })$(($(sym(stringify!($ctor_param_name))),*))?,
                                            )*
                                        ]
                                    )
                                }
                            )$(($(sym(stringify!($param_name))),*))?
                        )?
                        // Handle primitive constructors:
                        $(
                            || (
                                $(|$($prim_param_name,)*|)? {
                                    primitive_with_params(
                                        sym(self.name()),
                                        params([$($(($prim_param_name, $prim_param_ty, None)),*)?]),
                                        $prim_ctor
                                    )
                                }
                            )$(($(sym(stringify!($prim_param_name))),*))?
                        )?
                    )
                }
            }
        )*
    };
}
