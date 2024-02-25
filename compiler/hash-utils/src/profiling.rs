//! Timing/profiling utilities.


cfg_match! {
    cfg(windows) => {
        pub fn get_resident_set_size() -> Option<usize> {
            use std::mem;

            use windows::{
                // FIXME: change back to K32GetProcessMemoryInfo when windows crate
                // updated to 0.49.0+ to drop dependency on psapi.dll
                Win32::System::ProcessStatus::{GetProcessMemoryInfo, PROCESS_MEMORY_COUNTERS},
                Win32::System::Threading::GetCurrentProcess,
            };

            let mut pmc = PROCESS_MEMORY_COUNTERS::default();
            let pmc_size = mem::size_of_val(&pmc);
            unsafe {
                GetProcessMemoryInfo(
                    GetCurrentProcess(),
                    &mut pmc,
                    pmc_size as u32,
                )
            }
            .ok()
            .ok()?;

            Some(pmc.WorkingSetSize)
        }
    }
    cfg(target_os = "macos")  => {
        pub fn get_resident_set_size() -> Option<usize> {
            use libc::{c_int, c_void, getpid, proc_pidinfo, proc_taskinfo, PROC_PIDTASKINFO};
            use std::mem;
            const PROC_TASKINFO_SIZE: c_int = mem::size_of::<proc_taskinfo>() as c_int;

            unsafe {
                let mut info: proc_taskinfo = mem::zeroed();
                let info_ptr = &mut info as *mut proc_taskinfo as *mut c_void;
                let pid = getpid() as c_int;
                let ret = proc_pidinfo(pid, PROC_PIDTASKINFO, 0, info_ptr, PROC_TASKINFO_SIZE);
                if ret == PROC_TASKINFO_SIZE {
                    Some(info.pti_resident_size as usize)
                } else {
                    None
                }
            }
        }
    }
    cfg(unix) => {
        pub fn get_resident_set_size() -> Option<usize> {
            let field = 1;
            let contents = fs::read("/proc/self/statm").ok()?;
            let contents = String::from_utf8(contents).ok()?;
            let s = contents.split_whitespace().nth(field)?;
            let npages = s.parse::<usize>().ok()?;
            Some(npages * 4096)
        }
    }
    _ => {
        pub fn get_resident_set_size() -> Option<usize> {
            None
        }
    }
}
