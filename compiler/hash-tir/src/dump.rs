use hash_utils::log;

pub fn dump_tir(value: impl ToString) {
    log::info!("TIR dump:\n{}", value.to_string());
}
