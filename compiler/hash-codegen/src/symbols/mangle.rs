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

use hash_attrs::builtin::attrs;
use hash_ir::ty::{InstanceHelpers, InstanceId};
use hash_source::{identifier::IDENTS, InteractiveId, ModuleId};
use hash_storage::store::{statics::StoreId, StoreKey};

use super::{push_string_encoded_count, ALPHANUMERIC_BASE};

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
pub fn compute_symbol_name(instance_id: InstanceId) -> String {
    // @@Todo: allow for certain symbol names to be exported
    // without mangling. This is useful for debugging purposes.

    let m = &mut Mangler { out: String::new() };

    instance_id.map(|instance| {
        if !instance.has_attr(attrs::NO_MANGLE) && !instance.has_attr(attrs::FOREIGN) {
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

        let name = instance.name();

        // This is the case that the name wasn't given by the typechecking for several
        // reasons:
        //
        // 1. The function was monomorphised and it didn't retain the original name,
        // this will be fixed in the future.
        //
        // 2. The function is anonymous (a closure) with no inherited name.
        //
        // 3. The name wasn't set for some reason.
        //
        // In this case, we generate a new name by randomly generating a name which
        // is unlikely to conflict with any other name.
        if name == IDENTS.underscore {
            m.push(format!("closure$SP$_{}", instance_id.to_index()).as_str())
        } else {
            // @@Future: if we allow for unicode names, then we have to convert the
            // name of the module into a valid UTF-8 string.
            m.push(format!("{name}").as_str());
        }

        if instance.is_origin_polymorphic() {
            m.push(format!("_g{instance_id:?}").as_str());
            push_string_encoded_count(
                instance_id.to_index() as u128,
                ALPHANUMERIC_BASE,
                &mut m.out,
            );
        }
    });

    std::mem::take(&mut m.out)
}
