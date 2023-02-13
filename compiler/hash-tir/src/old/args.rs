//! Definition of [Arg] data structure, which is the representation of a
//! an argument to some function, type function, and other constructs that
//! can take arguments.
use std::fmt;

use hash_source::identifier::Identifier;
use hash_utils::new_sequence_store_key;

use crate::old::{
    fmt::{ForFormatting, PrepareForFormatting},
    params::{GetNameOpt, ParamList, ParamListStore},
    terms::TermId,
};

/// An argument to a parameter.
#[derive(Debug, Clone, Hash, Copy)]
pub struct Arg {
    /// Optional name that is attached to the argument.
    pub name: Option<Identifier>,
    /// The term that is the value of the argument.
    pub value: TermId,
}

impl GetNameOpt for Arg {
    fn get_name_opt(&self) -> Option<Identifier> {
        self.name
    }
}

/// A list of arguments.
pub type Args<'p> = ParamList<'p, Arg>;

new_sequence_store_key!(pub ArgsId);
pub type ArgsStore = ParamListStore<ArgsId, Arg>;

impl PrepareForFormatting for ArgsId {}

impl fmt::Display for ForFormatting<'_, ArgsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let args_id = self.t;

        self.global_storage.args_store.map_as_param_list_fast(args_id, |args| {
            for (i, arg) in args.positional().iter().enumerate() {
                match arg.name {
                    Some(arg_name) => {
                        write!(
                            f,
                            "{} = {}",
                            arg_name,
                            arg.value.for_formatting(self.global_storage)
                        )?;
                    }
                    None => arg.value.for_formatting(self.global_storage).fmt(f)?,
                }
                if i != args.positional().len() - 1 {
                    write!(f, ", ")?;
                }
            }

            Ok(())
        })
    }
}
