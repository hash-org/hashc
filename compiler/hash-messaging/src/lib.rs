//! Defines compiler messages that are passed in and out of the compiler.

pub mod listener;
pub mod stream;

use hash_pipeline::settings::CompilerSettings;
use hash_reporting::report::Report;
use hash_utils::schemars::{self, JsonSchema};

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

#[derive(Debug, Clone, JsonSchema)]
pub enum CompilerOutputMessage {
    /// A message that is emitted by the compiler, this is any diagnostic.
    Report(Report),

    /// The configuration of the compiler.
    Settings(CompilerSettings),
}

#[derive(Debug, Clone, JsonSchema)]
pub enum CompilerInputMessage {}

///
///
/// This is purely a utility struct to help with the JSON schema generation.
#[derive(Debug, Clone, JsonSchema)]
pub enum CompilerMessage {
    /// A message that is emitted by the compiler, this is any diagnostic.
    Output(CompilerOutputMessage),

    /// A message that is sent to the compiler, this is any request.
    Input(CompilerInputMessage),
}
