//! Hash Error code library file.
//!
//! All rights reserved 2022 (c) The Hash Language authors

/// Error code macro is used to generate the [HashErrorCode] macro.
macro_rules! error_codes {
    ($($name:ident = $code:expr,)*) => (
        #[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
        #[allow(dead_code)]
        pub enum HashErrorCode {
            $($name, )*
        }

        // This is used to verify that error codes cannot be re-used for error variants.
        #[allow(dead_code)]
        enum Dummy {
            $($name = $code, )*
        }

        impl HashErrorCode {
            #[allow(unused)]
            pub fn to_num(&self) -> u32 {
                match self {
                    $(Self::$name => $code, )*
                }
            }
        }
    )
}

pub mod error_codes;
