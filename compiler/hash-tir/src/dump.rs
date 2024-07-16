use hash_utils::log;

/// Function to emit a TIR dump, this is useful for debugging purposes.
pub fn dump_tir(value: impl ToString) {
    // @@Messaging: provide a format for the TIR to be dumped in (which is public).
    log::info!("TIR dump:\n{}", value.to_string());
}
