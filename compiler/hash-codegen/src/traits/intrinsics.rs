//! This defines all of the traits to generate **intrinsic** specific 
//! code for a target backend. The intrinsics for Hash are defined in 
//! the `prelude` module within the standard library, and are used to
//! provide a common interface for the standard library to interact with
//! compiler.


pub trait BuildIntrinsicCallMethods<'b>: BackendTypes {
    fn codegen_intrinsic_call(
        &self,
        intrinsic: Intrinsic,
        args: &[Self::Value],
        result: Self::Value,
    ) -> Self::Value;
} 

