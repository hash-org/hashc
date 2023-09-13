use hash_utils::stream_less_writeln;

pub fn dump_tir(value: impl ToString) {
    stream_less_writeln!("[TIR dump]:\n{}", value.to_string());
}
