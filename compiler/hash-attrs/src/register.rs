//! Implementation for the registering procedural macro which can parse attribute
//! definitions into something that the compiler can understand and later use 
//! to programatically check attribute annotations.


// @@Temporary
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AttrId(u32);
