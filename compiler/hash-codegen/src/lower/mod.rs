//! This module is responsible for converting Hash IR into the target code
//! backend via the code generation traits. This minimizes the amount of code
//! that needs to be shared between the different backends, so they can all
//! deal with the specifics of each backend within the particular crate.

pub(crate) mod operands;
pub(crate) mod place;
