//! Definition and lookup of primitive types.
use std::{iter::once, sync::OnceLock};

use hash_storage::store::statics::StoreId;

use crate::{
    building::gen::{
        args, data_ty, empty_data_def, enum_def, indexed_enum_def, params, primitive,
        primitive_with_params, sym, universe_ty,
    },
    data::{ArrayCtorInfo, DataDefId, NumericCtorBits, NumericCtorInfo, PrimitiveCtorInfo},
    mods::{ModMember, ModMemberValue},
    terms::Term,
    tys::Ty,
};

macro_rules! defined_primitives {
    ($($name:ident),* $(,)?) => {
        #[derive(Debug, Copy, Clone)]
        pub struct DefinedPrimitives {
            $($name: DataDefId),*
        }

        impl DefinedPrimitives {
            $(
                pub fn $name(&self) -> DataDefId {
                    self.$name
                }
            )*
        }

        /// The global [`DefinedPrimitives`] instance.
        static PRIMITIVES: OnceLock<DefinedPrimitives> = OnceLock::new();

        /// Access the global [`DefinedPrimitives`] instance.
        pub fn primitives() -> &'static DefinedPrimitives {
            PRIMITIVES.get_or_init(DefinedPrimitives::create)
        }

        impl DefinedPrimitives {
            /// Create a list of [`ModMemberData`] that corresponds to the defined primitives.
            ///
            /// This can be used to make a module and enter its scope.
            pub fn as_mod_members(&self) -> Vec<$crate::node::Node<ModMember>> {
                vec![
                    $(
                        $crate::node::Node::gen(ModMember {
                            name: self.$name.borrow().name,
                            value: ModMemberValue::Data(self.$name)
                        }),
                    )*
                ]
            }
        }
    };

}

// All the primitive types:
defined_primitives! {
    never,
    bool,
    u8,
    u16,
    u32,
    u64,
    u128,
    ubig,
    usize,
    i8,
    i16,
    i32,
    i64,
    i128,
    ibig,
    isize,
    f32,
    f64,
    str,
    char,
    option,
    result,
    list,
    array,
    equal,
}

impl DefinedPrimitives {
    /// Create the primitive types using the given environment.
    pub fn create() -> Self {
        // Helper function to create a numeric primitive.
        let numeric = |name, bits, signed, float| {
            primitive(
                sym(name),
                PrimitiveCtorInfo::Numeric(NumericCtorInfo {
                    bits: if bits == 0 {
                        NumericCtorBits::Unbounded
                    } else {
                        NumericCtorBits::Bounded(bits)
                    },
                    is_signed: signed,
                    is_float: float,
                }),
            )
        };

        let usize = numeric("usize", 64, false, false);

        DefinedPrimitives {
            // Never
            never: empty_data_def(sym("never"), params([])),

            // bool
            bool: enum_def(
                sym("bool"),
                params([]),
                [(sym("true"), params([])), (sym("false"), params([]))],
            ),

            // numerics
            i8: numeric("i8", 8, true, false),
            i16: numeric("i16", 16, true, false),
            i32: numeric("i32", 32, true, false),
            i64: numeric("i64", 64, true, false),
            i128: numeric("i128", 128, true, false),
            isize: numeric("isize", 64, true, false),
            ibig: numeric("ibig", 0, true, false),

            u8: numeric("u8", 8, false, false),
            u16: numeric("u16", 16, false, false),
            u32: numeric("u32", 32, false, false),
            u64: numeric("u64", 64, false, false),
            u128: numeric("u128", 128, false, false),
            ubig: numeric("ubig", 0, false, false),
            usize,

            f32: numeric("f32", 32, false, true),
            f64: numeric("f64", 64, false, true),

            // str and char
            str: primitive(sym("str"), PrimitiveCtorInfo::Str),
            char: primitive(sym("char"), PrimitiveCtorInfo::Char),

            // list
            list: {
                let list_sym = sym("List");
                let t_sym = sym("T");
                let params = params(once((t_sym, universe_ty(), None)));
                primitive_with_params(
                    list_sym,
                    params,
                    PrimitiveCtorInfo::Array(ArrayCtorInfo {
                        element_ty: Ty::var(t_sym),
                        length: None,
                    }),
                )
            },
            array: {
                let list_sym = sym("Array");
                let t_sym = sym("T");
                let n_sym = sym("n");
                let params = params([(t_sym, universe_ty(), None), (n_sym, data_ty(usize), None)]);
                primitive_with_params(
                    list_sym,
                    params,
                    PrimitiveCtorInfo::Array(ArrayCtorInfo {
                        element_ty: Ty::var(t_sym),
                        length: Some(Term::from(n_sym)),
                    }),
                )
            },

            // option
            option: {
                let option_sym = sym("Option");
                let none_sym = sym("None");
                let some_sym = sym("Some");
                let t_sym = sym("T");
                let ps = params(once((t_sym, universe_ty(), None)));
                let some_params = params(once((sym("value"), Ty::var(t_sym), None)));
                enum_def(option_sym, ps, [(none_sym, params([])), (some_sym, some_params)])
            },

            // result
            result: {
                let result_sym = sym("Result");
                let ok_sym = sym("Ok");
                let err_sym = sym("Err");
                let t_sym = sym("T");
                let e_sym = sym("E");
                let ps = params([(t_sym, universe_ty(), None), (e_sym, universe_ty(), None)]);
                let ok_ps = params(once((sym("value"), Ty::var(t_sym), None)));
                let err_ps = params(once((sym("error"), Ty::var(e_sym), None)));
                enum_def(result_sym, ps, [(ok_sym, ok_ps), (err_sym, err_ps)])
            },
            equal: {
                let eq_sym = sym("Equal");
                let refl_sym = sym("Refl");

                let t_sym = sym("T");
                let a_sym = sym("a");
                let b_sym = sym("b");

                let x_sym = sym("x");

                let ps = params([
                    (t_sym, universe_ty(), None),
                    (a_sym, Ty::var(t_sym), None),
                    (b_sym, Ty::var(t_sym), None),
                ]);
                let refl_ps = params(once((x_sym, Ty::var(t_sym), None)));

                let refl_result_args = args([Term::var(t_sym), Term::var(x_sym), Term::var(x_sym)]);

                indexed_enum_def(eq_sym, ps, [(refl_sym, refl_ps, Some(refl_result_args))])
            },
        }
    }
}
