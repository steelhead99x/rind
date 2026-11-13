//! Idle check: other work on the host, sampled the way `admin/bench-report` samples it.

use crate::error::{Error, Result};
use crate::tables::BUSY_SHARE;

pub fn cpu_count() -> u64 {
    std::thread::available_parallelism()
        .map(|n| n.get() as u64)
        .unwrap_or(1)
}

pub fn busy_limit() -> f64 {
    (BUSY_SHARE * cpu_count() as f64).max(1.0)
}

pub fn cpu_times() -> Result<(u64, u64)> {
    #[cfg(target_os = "macos")]
    {
        macos_cpu_times()
    }
    #[cfg(not(target_os = "macos"))]
    {
        linux_cpu_times()
    }
}

fn linux_cpu_times() -> Result<(u64, u64)> {
    let text = std::fs::read_to_string("/proc/stat").map_err(|err| Error::new(err.to_string()))?;
    let line = text.lines().next().unwrap_or("");
    let fields: Vec<u64> = line
        .split_whitespace()
        .skip(1)
        .take(8)
        .filter_map(|part| part.parse().ok())
        .collect();
    if fields.len() < 8 {
        return Err(Error::new("could not read /proc/stat"));
    }
    let idle = fields[3] + fields[4];
    let total: u64 = fields.iter().sum();
    Ok((total - idle, total))
}

#[cfg(target_os = "macos")]
fn macos_cpu_times() -> Result<(u64, u64)> {
    unsafe extern "C" {
        fn mach_host_self() -> u32;
        fn host_statistics(host: u32, flavor: i32, info: *mut u32, count: *mut u32) -> i32;
    }
    let mut ticks = [0u32; 4];
    let mut count = 4u32;
    let rc = unsafe { host_statistics(mach_host_self(), 3, ticks.as_mut_ptr(), &mut count) };
    if rc != 0 {
        return Err(Error::new("host_statistics failed"));
    }
    let (user, system, idle, nice) = (
        ticks[0] as u64,
        ticks[1] as u64,
        ticks[2] as u64,
        ticks[3] as u64,
    );
    Ok((user + system + nice, user + system + idle + nice))
}

pub fn busy_cpus_since(start: (u64, u64)) -> f64 {
    let (now_busy, now_total) = match cpu_times() {
        Ok(times) => times,
        Err(_) => return 0.0,
    };
    let busy = now_busy.wrapping_sub(start.0) % (1u64 << 32);
    let total = now_total.wrapping_sub(start.1) % (1u64 << 32);
    busy as f64 / total.max(1) as f64 * cpu_count() as f64
}

pub fn busy_cpus(seconds: u64) -> f64 {
    let start = cpu_times().unwrap_or((0, 0));
    std::thread::sleep(std::time::Duration::from_secs(seconds));
    busy_cpus_since(start)
}

pub fn children_cpu_seconds() -> f64 {
    let mut usage = unsafe { std::mem::zeroed::<libc::rusage>() };
    unsafe {
        libc::getrusage(libc::RUSAGE_CHILDREN, &mut usage);
    }
    timeval(usage.ru_utime) + timeval(usage.ru_stime)
}

fn timeval(value: libc::timeval) -> f64 {
    value.tv_sec as f64 + value.tv_usec as f64 / 1e6
}

#[derive(Debug)]
pub struct Busy {
    pub message: String,
}

pub fn check_idle(when: &str) -> std::result::Result<f64, Busy> {
    let busy = busy_cpus(5);
    let limit = busy_limit();
    if busy > limit {
        Err(Busy {
            message: format!(
                "{busy:.1} of {} CPUs busy {when} (limit {limit:.1})",
                cpu_count()
            ),
        })
    } else {
        Ok((busy * 100.0).round() / 100.0)
    }
}
