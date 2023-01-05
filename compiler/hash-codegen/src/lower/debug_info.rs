//! Module that hosts all of the logic for emitting debug
//! information when converting Hash IR into target backend
//! IR. This module is responsible for emitting debug information
//! all allocations made, all variable locations, and all
//! function debug information via the common debug info
//! interface.

use super::FnBuilder;
use crate::traits::builder::BlockBuilderMethods;

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {}
