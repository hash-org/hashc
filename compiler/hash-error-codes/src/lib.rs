macro_rules! register_diagnostics {
    ($($ecode:ident: $message:expr,)* ; $($code:ident,)*) => (
        pub static DIAGNOSTICS: &[(&str, Option<&str>)] = &[
            $( (stringify!($ecode), Some($message)), )*
            $( (stringify!($code), None), )*
        ];
    )
}

pub enum DiagnosticId {
    Error(String),
}

mod error_codes;
pub use error_codes::DIAGNOSTICS;

#[macro_export]
macro_rules! error_code {
    ($code:ident) => {{
        $crate::DiagnosticId::Error(stringify!($code).to_owned())
    }};
}
