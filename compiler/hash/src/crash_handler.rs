//! Hash Compiler crash handler
use backtrace::Backtrace;
use std::{io::Write, panic::PanicInfo, process::exit, sync::atomic, thread};

const BUG_REPORT_MSG: &str = "This is an compiler bug, please file a bug report at";
const BUG_REPORT_URI: &str =
    "https://github.com/hash-org/lang/issues?labels=bug&template=bug_report";

pub(crate) fn panic_handler(info: &PanicInfo) {
    // keep track to ensure that we only panic once and multiple threads can exit
    // gracefully!
    static PANIC_ONCE: atomic::AtomicBool = atomic::AtomicBool::new(false);

    if !PANIC_ONCE.swap(true, atomic::Ordering::SeqCst) {
        let stdout = std::io::stdout();
        let mut stdout = stdout.lock();

        let _ = write!(&mut stdout, "Sorry :^(\nInternal Compiler Error");

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
                "Occurred at '{}:{}:{}'",
                location.file(),
                location.line(),
                location.column()
            );
        }

        let backtrace = Backtrace::new();

        // Print backtrace and thread name if available
        if let Some(name) = thread::current().name() {
            let _ = writeln!(&mut stdout, "Backtrace for thread \"{}\":\n{:?}", name, backtrace);
        } else {
            let _ = writeln!(&mut stdout, "Backtrace:\n{:?}", backtrace);
        }

        let _ = writeln!(
            &mut stdout,
            "{}\n\n{:^len$}\n",
            BUG_REPORT_MSG,
            BUG_REPORT_URI,
            len = BUG_REPORT_MSG.len()
        );
    }

    // Now call exit after we have printed all the relevant info
    exit(1);
}
