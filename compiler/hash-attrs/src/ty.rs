//! Implementation for the registering procedural macro which can parse
//! attribute definitions into something that the compiler can understand and
//! later use to programatically check attribute annotations.

use std::sync::LazyLock;

use hash_source::identifier::Identifier;
use hash_storage::store::statics::SequenceStoreValue;
use hash_tir::{
    params::{Param, ParamsId},
    primitives::primitives,
    symbols::sym,
    tys::Ty,
};
use hash_utils::{
    fxhash::FxHashMap,
    index_vec::{define_index_type, IndexVec},
    lazy_static,
};

use crate::target::AttrTarget;

define_index_type! {
    /// This is the unique identifier for an AST node. This is used to
    /// map spans to nodes, and vice versa. [AstNodeId]s are unique and
    /// they are always increasing as a new nodes are created.
    pub struct AttrId = u32;
    MAX_INDEX = i32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

/// A table that stores the definitions for all of the builtin compiler
/// attributes that a program may use. The table stores information about what
/// the type of the attributes parameters are, and what kind of subject the
/// attribute is allowed to be applied onto.
#[derive(Debug, Default)]
pub struct AttrTyMap {
    /// A storage of all of the attributes that the compiler knows and
    /// supports.
    map: IndexVec<AttrId, AttrTy>,

    /// A mapping between the name of an attribute and its [AttrId].
    name_map: FxHashMap<Identifier, AttrId>,
}

impl AttrTyMap {
    /// Create a new [AttrTyMap].
    pub fn new() -> Self {
        Self { map: IndexVec::new(), name_map: FxHashMap::default() }
    }

    /// Get the [AttrTy] for the given [AttrId].
    pub fn get(&self, id: AttrId) -> &AttrTy {
        &self.map[id]
    }

    /// Get the [AttrId] by the name of the attribute.
    pub fn get_id_by_name(&self, name: Identifier) -> Option<AttrId> {
        self.name_map.get(&name).copied()
    }

    /// Get the [AttrTy] by the name of the attribute.
    pub fn get_by_name(&self, name: Identifier) -> Option<&AttrTy> {
        self.name_map.get(&name).map(|id| &self.map[*id])
    }
}

/// An [AttrTy] stores the expected "type" of the parameter arguments, so that
/// the compiler can check that the arguments are correct.
#[derive(Debug)]
pub struct AttrTy {
    /// The name of the attribute.
    pub name: Identifier,

    /// The type of the parameters that the attribute expects. We use
    /// [ParamsId] in order so that we can use the defined logic in
    /// [hash_tir::utils::params] to check that the arguments to an
    /// attribute are correct. This is possible because the same rules
    /// to attribute parameters and arguments apply as they do to other
    /// parameters and arguments.
    pub params: ParamsId,

    /// The expected kind of subject that the attribute is allowed to be
    /// applied onto.
    pub subject: AttrTarget,
}

impl AttrTy {
    /// Create a new [AttrTy] with the given name, parameters and subject.
    pub fn new(name: impl Into<Identifier>, params: ParamsId, subject: AttrTarget) -> Self {
        Self { name: name.into(), params, subject }
    }
}

macro_rules! make_ty {
    (str) => {
        Ty::data(primitives().str())
    };
    (int) => {
        Ty::data(primitives().i32())
    };
    (float) => {
        Ty::data(primitives().f64())
    };
    (char) => {
        Ty::data(primitives().char())
    };
}

macro_rules! define_attr {
    // @@Future: support for default values, via a literal. This would probably be
    // better done usin a procedural macro, so that we can emit better errors.
    //
    // @@Improve: ensure that provided argument names are unique!
    ($table:expr, $name:ident, ($($arg:ident : $ty:ident),*), $subject:expr) => {
        let name: Identifier = stringify!($name).into();

        let params = Param::seq_data([
            $(
                Param { name: sym(name), ty: make_ty!($ty), default: None }
            ),*
        ]);

        let index = $table.map.push(AttrTy::new(name, params, $subject));
        if $table.name_map.insert(name, index).is_some() {
            panic!("duplicate attribute name: `{}`", name);
        }
    };
    ($table:expr, $name:ident, $subject:expr) => {
        let name: Identifier = stringify!($name).into();
        let index = $table.map.push(AttrTy::new(name, Param::empty_seq(), $subject));

        if $table.name_map.insert(name, index).is_some() {
            panic!("duplicate attribute name: `{}`", name);
        }
    }
}

lazy_static::lazy_static! {
    pub static ref ATTR_MAP: LazyLock<AttrTyMap> = {
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
}

/// Valid `#[repr(...)]` options, ideally we should be able to just generate
/// this in the macro.
pub(crate) const REPR_OPTIONS: &[&str] = &["c", "u8", "u16", "u32", "u64", "u128"];
