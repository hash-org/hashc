//! This module contains logic for creating mangle symbol
//! names for instance items. This is needed when emitting
//! function names that might conflict with other names in
//! the same module (if they are generic), or the same named
//! functions externally, or in different modules.
//!
//! The mangle symbol name is a unique name that is used to
//! identify the function in the generated object file. The
//! mangling algorithm first deals with the following cases:
//!
//! 1. If the function is not generic, then the mangle symbol
//! name is the same as the function name, with the module
//! path prepended as a namespace that is relative to the
//! entry_point module.
//!
//! 2. If the function is generic, the type parameters of the
//! function are needed to create a unique name such that they
//! distinguish the function from other functions with the same
//! name. The type parameters are encoded into the final symbol
//! name.
//!
//!
//! 3. If there are any attributes that are set on the instance
//! which prevent the function function from being "mangled", then
//! we have to avoid mangling the symbol name.

use hash_ir::{ty::InstanceId, IrCtx};
use hash_source::{identifier::IDENTS, InteractiveId, ModuleId};
use hash_utils::store::{Store, StoreKey};

/// The [Mangler] is a structure that is used to build up the "mangled"
/// symbol for an instance or static item.
///
/// @@Incomplete: This API is incomplete, and will be extended as the mangling
/// algorithm is extended.
struct Mangler {
    /// The mangled symbol value, this is built up as the mangling
    /// process occurs.
    out: String,
}

impl Mangler {
    /// Push an additional string value into the mangled
    /// name.
    fn push(&mut self, s: &str) {
        self.out.push_str(s);
    }
}

/// This is the entry point of the symbol mangling algorithm. This
/// will produce a unique symbol from the provided instance. For now,
/// the algorithm is very symbol because we're not expecting that the
/// symbol names should be "de-mangled" by the user for debugging
/// purposes.
///
/// Therefore, the current mangling scheme produces the following
/// symbol:
///
/// ```text
/// <module_id>::<function_name>(is_generic? instance-id)
/// ```
pub fn compute_symbol_name(ctx: &IrCtx, instance_id: InstanceId) -> String {
    // @@Todo: allow for certain symbol names to be exported
    // without mangling. This is useful for debugging purposes.

    let m = &mut Mangler { out: String::new() };

    ctx.instances().map_fast(instance_id, |instance| {
        if !instance.attributes.contains(IDENTS.no_mangle)
            && !instance.attributes.contains(IDENTS.foreign)
        {
            if let Some(source) = instance.source {
                if source.is_module() {
                    // If the source is a module, then we need to
                    // use the module id as a unique identifier.
                    m.push(format!("m{}_", ModuleId::from(source).raw()).as_str());
                } else {
                    m.push(format!("i{}_", InteractiveId::from(source).raw()).as_str());
                }
            } else {
                // If we don't have the source, then we need to
                // use the instance id as a unique identifier.
                m.push(format!("p{}_", instance_id.to_index()).as_str());
            }
        }

        // @@Future: if we allow for unicode names, then we have to convert the
        // name of the module into a valid UTF-8 string.
        m.push(format!("{}", instance.name()).as_str());

        if instance.is_generic_origin() {
            m.push(format!("_g{instance_id:?}").as_str());
        }
    });

    std::mem::take(&mut m.out)
}
