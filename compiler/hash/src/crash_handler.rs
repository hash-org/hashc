//! Hash compiler crash handler
//
// All rights reserved 2021 (c) The Hash Language authors

use backtrace::Backtrace;
use std::panic::PanicInfo;
use std::process::exit;
use std::{io::Write, sync::atomic, thread};

pub(crate) fn panic_handler(info: &PanicInfo) {
    // keep track to ensure that we only panic once and multiple threads can exit gracefully!
    static PANIC_ONCE: atomic::AtomicBool = atomic::AtomicBool::new(false);

    if !PANIC_ONCE.swap(true, atomic::Ordering::SeqCst) {
        let stdout = std::io::stdout();
        let mut stdout = stdout.lock();

        let _ = write!(&mut stdout, "Sorry :^(\nInternal Panic");

        if let Some(s) = info.payload().downcast_ref::<&str>() {
            let _ = writeln!(&mut stdout, ": {}\n", s);
        } else if let Some(s) = info.message() {
            let _ = writeln!(&mut stdout, ": {}\n", s);
        } else {
            let _ = writeln!(&mut stdout, "\n");
        }

        // Display the location if we can...
        if let Some(location) = info.location() {
            let _ = writeln!(
                &mut stdout,
                "Occurred in file '{}' at {}:{}",
                location.file(),
                location.line(),
                location.column()
            );
        }

        let backtrace = Backtrace::new();

        // Print backtrace and thread name if available
        if let Some(name) = thread::current().name() {
            let _ = writeln!(
                &mut stdout,
                "Backtrace for thread \"{}\":\n{:?}",
                name, backtrace
            );
        } else {
            let _ = writeln!(&mut stdout, "Backtrace:\n{:?}", backtrace);
        }

        let msg = "This is an compiler bug, please file a bug report at";
        let uri = "https://github.com/hash-org/lang/issues";

        let _ = writeln!(&mut stdout, "{}\n\n{:^len$}\n", msg, uri, len = msg.len());
    }

    // Now call exit after we have printed all the relevant info
    exit(1);
}
