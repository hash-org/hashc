//! Defines compiler messages that are passed in and out of the compiler.

pub mod listener;
pub mod stream;

use hash_pipeline::{metrics::Metrics, settings::CompilerSettings};
use hash_reporting::report::Report;
use hash_utils::{
    log::kv,
    schemars::{self, JsonSchema},
    serde::{self, Serialize},
};

/// The [CompilerMessagingFormat] specifies the message mode that the compiler
/// will use to to emit and receive messages.
#[derive(Debug, Clone)]
pub enum CompilerMessagingFormat {
    /// All messages that are emitted to and from the compiler will be in JSON
    /// format according to the schema that represents [CompilerMessage].
    Json,

    /// Normal mode is the classic emission of messages as the compiler would
    /// normally do, i.e. calling [fmt::Display] on provided [Report]s.
    ///
    /// @@Note: do we support listening to messages in this mode - this doesn't
    /// really make sense?
    Normal,
}

#[derive(Clone, JsonSchema, Serialize)]
#[serde(crate = "self::serde", rename_all = "camelCase")]
pub enum CompilerOutputMessage<'a> {
    /// A message that is emitted by the compiler, this is any diagnostic.
    Report(&'a Report),

    /// The configuration of the compiler.
    Settings(&'a CompilerSettings),

    /// Metrics that the compiler collected.
    Metrics(&'a Metrics),

    /// The current "linker line" that the compiler is using for
    /// a particular workspace.
    LinkerLine(&'a str),
}

// ##Hack: needed for using `log::info!(...)` with `CompilerOutputMessage`.
impl kv::ToValue for CompilerOutputMessage<'_> {
    fn to_value(&self) -> kv::Value<'_> {
        kv::Value::from_serde(self)
    }
}

/// Any messages that the compiler can accept as an input.
#[derive(Clone, JsonSchema)]
pub enum CompilerInputMessage {}

/// This is purely a utility struct to help with the JSON schema generation.
#[derive(Clone, JsonSchema)]
pub enum CompilerMessage<'a> {
    /// A message that is emitted by the compiler, this is any diagnostic.
    Output(CompilerOutputMessage<'a>),

    /// A message that is sent to the compiler, this is any request.
    Input(CompilerInputMessage),
}
