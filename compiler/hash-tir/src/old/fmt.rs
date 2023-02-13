//! Contains utilities to format types for displaying in error messages and
//! debug output.
use std::fmt;

use crate::old::storage::GlobalStorage;

// Contains various options regarding the formatting of terms.
#[derive(Debug, Clone, Copy, Default)]
pub struct TcFormatOpts {
    /// Out parameter for whether the term is atomic.
    // pub is_atomic: Rc<Cell<bool>>,
    /// Parameter for whether to always expand terms.
    pub expand: bool,
}

/// Format some arbitrary item that implements [PrepareForFormatting] as
/// a single component. This means that if `atomic` is not set, then we
/// surround the item with parentheses and print the item.
pub macro fmt_as_single($f:expr, $item:expr) {{
    write!($f, "(")?;
    $item;
    write!($f, ")")?;
}}

/// Wraps a type `T` in a structure that contains information to be able to
/// format `T` using [TcFormatter].
///
/// This can wrap any type, but only types that have corresponding `fmt_*`
/// methods in [TcFormatter] are useful with it.
pub struct ForFormatting<'gs, T> {
    pub t: T,
    pub global_storage: &'gs GlobalStorage,
    pub opts: TcFormatOpts,
}

/// Convenience trait to create a `ForFormatting<T>` given a `T`.
pub trait PrepareForFormatting: Sized {
    /// Create a `ForFormatting<T>` given a `T`.
    fn for_formatting(self, global_storage: &GlobalStorage) -> ForFormatting<Self> {
        ForFormatting { t: self, global_storage, opts: TcFormatOpts::default() }
    }

    /// Create a `ForFormatting<T>` given a `T`, and provide an out parameter
    /// for the `is_atomic` check.
    fn for_formatting_with_opts(
        self,
        global_storage: &GlobalStorage,
        opts: TcFormatOpts,
    ) -> ForFormatting<Self> {
        ForFormatting { t: self, global_storage, opts }
    }
}

impl<T: PrepareForFormatting> PrepareForFormatting for Option<T> {}
impl<T: PrepareForFormatting> PrepareForFormatting for &Vec<T> {}

impl<'gs, T: PrepareForFormatting + Clone> fmt::Display for ForFormatting<'gs, Option<T>>
where
    ForFormatting<'gs, T>: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.t.as_ref() {
            Some(t) => {
                write!(
                    f,
                    "Some({})",
                    t.clone().for_formatting_with_opts(self.global_storage, self.opts)
                )
            }
            None => {
                write!(f, "None")
            }
        }
    }
}

impl<'gs, T: PrepareForFormatting + Clone> fmt::Display for ForFormatting<'gs, &Vec<T>>
where
    ForFormatting<'gs, T>: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (idx, el) in self.t.iter().enumerate() {
            write!(f, "{}", el.clone().for_formatting_with_opts(self.global_storage, self.opts))?;

            if idx != self.t.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}
