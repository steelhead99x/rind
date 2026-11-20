//! The CPU cycle counter Marvin's harness times each decryption with.

use std::time::Instant;

/// Reads the CPU's counter after every earlier instruction completes, and
/// before any later one starts.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn ticks() -> u64 {
    use std::arch::x86_64::{_mm_lfence, _rdtsc};
    // `_rdtsc` is safe from Rust 1.94 but `unsafe` on the 1.90 MSRV.
    #[allow(unused_unsafe)]
    // SAFETY: every x86_64 CPU has SSE2, so LFENCE, and RDTSC.
    unsafe {
        _mm_lfence();
        let t = _rdtsc();
        _mm_lfence();
        t
    }
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
pub fn ticks() -> u64 {
    let t: u64;
    // SAFETY: Linux, macOS, and Windows let user space read the virtual
    // counter.
    unsafe {
        std::arch::asm!(
            "isb",
            "mrs {t}, cntvct_el0",
            "isb",
            t = out(reg) t,
            options(nomem, nostack, preserves_flags),
        );
    }
    t
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
compile_error!("rind-timing reads the x86_64 or aarch64 counter");

/// The counter's rate, measured against the system clock.
pub fn ticks_per_second() -> u64 {
    let start = (Instant::now(), ticks());
    while start.0.elapsed().as_millis() < 100 {}
    let ticks = ticks().wrapping_sub(start.1);
    (ticks as f64 / start.0.elapsed().as_secs_f64()) as u64
}
