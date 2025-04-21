//! Defines all of the builtin attributes that the Hash compiler supports.

use std::sync::LazyLock;

use hash_ast_utils::attr::AttrTarget;
use hash_source::identifier::Identifier;
use hash_tir::building::generate;
use paste::paste;

use crate::ty::{AttrId, AttrTy, AttrTyMap};

// @@Future: add more complex rules which allow to specify more exotic types,
// i.e. a list of values.
macro_rules! make_ty {
    ($kind: ident) => {{
        // ##GeneratedOrigin: these attributes are generated, so they do not
        // have an origin.
        use hash_tir::intrinsics::definitions::*;
        paste! {
            [<$kind _gen_ty>]()
        }
    }};
}

macro_rules! define_attr {
    // @@Future: support for default values, via a literal. This would probably be
    // better done using a procedural macro, so that we can emit better errors.
    //
    // @@Improve: ensure that provided argument names are unique!
    ($table:expr, $name:ident, { ($($arg:ident : $ty:ident),*), $subject:expr }) => {
        let name: Identifier = stringify!($name).into();

        let params = if ${count($arg)} == 0 {
            generate::params([])
        } else {
            generate::params([
                $(
                    (generate::sym(stringify!(arg)), make_ty!($ty), None)
                ),*
            ])
        };

        let index = $table.map.push(AttrTy::new(name, params, $subject));
        if $table.name_map.insert(name, index).is_some() {
            panic!("duplicate attribute name: `{}`", name);
        }
    };
    ($table:expr, $name:ident, { $subject:expr }) => {
        define_attr!($table, $name, { (), $subject });
    }
}

macro_rules! define_attrs {
    ($($name:ident $args:tt),*) => {
        // Define the module with all of the constant attributes. This will
        // assign the `AttrId`s in the source order that the attributes are
        // specified.
        pub mod attrs {
            pub use super::*;

            $(
                paste!(
                    pub const [<$name:upper>]: AttrId = AttrId::from_usize_unchecked(${ index() });
                );
            )*
        }

        // Then, define the actual attribute type map.
        pub static ATTR_MAP: LazyLock<AttrTyMap> = LazyLock::new(|| {
            let mut table = AttrTyMap::new();

            $(
                define_attr!(table, $name, $args);
            )*

            table
        });
    };
}

define_attrs!(
    // ------------------------------------------
    // Internal compiler attributes and tooling.
    // ------------------------------------------
    dump_ast { AttrTarget::all() },
    dump_tir { AttrTarget::all() },
    dump_ir { AttrTarget::FnDef },
    dump_llvm_ir { AttrTarget::FnDef },
    layout_of { AttrTarget::StructDef | AttrTarget::EnumDef },

    // ------------------------------------------
    // Language feature based attributes.
    // ------------------------------------------
    run { AttrTarget::Expr },
    size_of { AttrTarget::Ty | AttrTarget::Field | AttrTarget::Expr },

    // ------------------------------------------
    // Function attributes.
    // ------------------------------------------
    lang {  AttrTarget::FnDef },
    intrinsics {AttrTarget::ModDef },
    entry_point {  AttrTarget::FnDef },
    pure {  AttrTarget::FnDef },
    foreign {  AttrTarget::FnDef },
    no_mangle {  AttrTarget::FnDef },
    link_name { (name: str), AttrTarget::FnDef },

    // ------------------------------------------
    // Type representation attributes.
    // ------------------------------------------
    repr { (abi: str), AttrTarget::StructDef | AttrTarget::EnumDef },
    discriminant { (value: i128), AttrTarget::EnumVariant }
);
