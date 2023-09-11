use std::process;

use hash_storage::store::statics::StoreId;
use hash_utils::stream_less_writeln;

use crate::{
    building::gen::{data_ty, never, unit_term, unit_ty, Type},
    intrinsics,
    lits::Lit,
    primitives::primitives,
    terms::Term,
};

intrinsics! {
    size_of := (T: Type()) -> data_ty(primitives().usize()) => |env| {
        // @@Todo: actually return the size
        Ok(None)
    };

    eval := (T: Type(), a: ty(T)) -> ty(T) => |env| {
        env.normalise_term(a)
    };

    transmute := (T: Type(), U: Type(), a: ty(T)) -> ty(U) => |env| {
        // Warning: highly unsafe!
        Ok(Some(a))
    };

    cast := (T: Type(), U: Type(), a: ty(T)) -> ty(T) => |env| {
        // @@Todo: actually cast
        Ok(None)
    };

    abort := () -> never() => |env| {
        process::exit(1)
    };

    panic := (message: data_ty(primitives().str())) -> never() => |env| {
        stream_less_writeln!("{}", message);
        process::exit(1)
    };

    user_error := (message: data_ty(primitives().str())) -> never() => |env| {
        if let Term::Lit(lit) = *message.value() && let Lit::Str(str_lit) = *lit.value() {
            Err(str_lit.value().to_string())
        } else {
            Err("`user_error` expects a string literal as argument".to_string())
        }
    };

    debug_print := (T: Type(), a: ty(T)) -> unit_ty() => |env| {
        stream_less_writeln!("{}", a);
        Ok(Some(unit_term()))
    };
}
