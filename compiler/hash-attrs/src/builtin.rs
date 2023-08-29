//! Defines all of the builtin attributes that the Hash compiler supports.

use std::sync::LazyLock;

use hash_source::identifier::Identifier;
use hash_storage::store::statics::SequenceStoreValue;
use hash_tir::{params::Param, primitives::primitives, symbols::sym, tys::Ty};

use crate::{
    target::AttrTarget,
    ty::{AttrTy, AttrTyMap},
};

// @@Future: add more complex rules which allow to specify more exotic types,
// i.e. a list of values.
macro_rules! make_ty {
    ($kind: ident) => {
        Ty::data(primitives().$kind())
    };
}

macro_rules! define_attr {
    // @@Future: support for default values, via a literal. This would probably be
    // better done usin a procedural macro, so that we can emit better errors.
    //
    // @@Improve: ensure that provided argument names are unique!
    ($table:expr, $name:ident, ($($arg:ident : $ty:ident),*), $subject:expr) => {
        let name: Identifier = stringify!($name).into();

        let params = if ${count(arg)} == 0 {
            Param::empty_seq()
        } else {
            Param::seq_data([
                $(
                    Param { name: sym(stringify!(arg)), ty: make_ty!($ty), default: None }
                ),*
            ])
        };

        let index = $table.map.push(AttrTy::new(name, params, $subject));
        if $table.name_map.insert(name, index).is_some() {
            panic!("duplicate attribute name: `{}`", name);
        }
    };
    ($table:expr, $name:ident, $subject:expr) => {
        define_attr!($table, $name, (), $subject);
    }
}

pub static ATTR_MAP: LazyLock<AttrTyMap> = {
    LazyLock::new(|| {
        let mut table = AttrTyMap::new();

        // ------------------------------------------
        // Internal compiler attributes and tooling.
        // ------------------------------------------
        define_attr!(table, dump_ast, AttrTarget::all());
        define_attr!(table, dump_tir, AttrTarget::all());
        define_attr!(table, dump_ir, AttrTarget::FnDef);
        define_attr!(table, dump_llvm_ir, AttrTarget::FnDef);
        define_attr!(table, layout_of, AttrTarget::StructDef | AttrTarget::EnumDef);

        // ------------------------------------------
        // Language feature based attributes.
        // ------------------------------------------
        define_attr!(table, run, AttrTarget::Expr);

        // ------------------------------------------
        // Function attributes.
        // ------------------------------------------
        define_attr!(table, lang, AttrTarget::FnDef);
        define_attr!(table, entry_point, AttrTarget::FnDef);
        define_attr!(table, pure, AttrTarget::FnDef);
        define_attr!(table, foreign, AttrTarget::FnDef);
        define_attr!(table, no_mangle, AttrTarget::FnDef);
        define_attr!(table, link_name, (name: str), AttrTarget::FnDef);

        // ------------------------------------------
        // Type attributes.
        // ------------------------------------------
        define_attr!(table, repr, (abi: str), AttrTarget::StructDef | AttrTarget::EnumDef);

        table
    })
};
