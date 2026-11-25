//! What one enter/exit of rind's per-call guard costs, apart from any work.
//!
//! Every rind call that handles a secret enters at its start and leaves at its
//! end; on an aarch64 core with DIT that sets data-independent timing on and
//! then off, with Apple's speculation barrier after the set on Apple's cores.
//! These rows time calls that do almost nothing, so the toggle is nearly all
//! of what they measure. As in every other rind row, `rind` is timed holding
//! [`rind::cpu::Dit`], and the `dit-per-call/` group times it again without:
//!
//! - `dit-toggle/verify-empty/rind`: `constant_time::verify` of two empty
//!   slices under a held guard, where the entry finds DIT already on.
//! - `dit-per-call/dit-toggle/verify-empty/rind`: the same with no guard, one
//!   toggle per call. On aarch64 only; on a core with DIT, it minus the held
//!   row is the cost of one toggle.
//! - `dit-toggle/hold-drop/rind`: `Dit::hold()` then drop, one toggle through
//!   the public guard. Made only where the guard turns DIT on.
//! - `dit-toggle/no-entry/rind`: a public call that makes no entry, for the
//!   cost of calling and timing alone.
//!
//! Run with `RIND_CPU_DISABLE_dit=1` (needs `--cfg rind_cpu_disable` in a
//! release build) and rind sets no DIT: the hold-drop row is not made, since
//! the guard turns nothing on, and both verify-empty rows are the cost of an
//! empty call.

#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod criterion;
#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use criterion::{Criterion, criterion_group, criterion_main};

/// Says on stderr whether this CPU reports `dit` and `sb`, which pick what the
/// guard runs: on Apple's cores, `sb` after setting DIT where there is one,
/// `dsb nsh; isb sy` where not. The devbench report lists the same features
/// under `device`.
#[cfg(not(target_arch = "xtensa"))]
fn report_features() {
    #[cfg(target_arch = "aarch64")]
    eprintln!(
        "dit-toggle: dit={} sb={}",
        std::arch::is_aarch64_feature_detected!("dit"),
        std::arch::is_aarch64_feature_detected!("sb")
    );
    #[cfg(not(target_arch = "aarch64"))]
    eprintln!("dit-toggle: not aarch64, rind sets no DIT here");
}

/// Whether a fresh guard turns PSTATE.DIT on, read back from the CPU, so the
/// hold-drop row follows what rind decided rather than what the CPU reports:
/// with `dit` denied rind sets none.
#[cfg(target_arch = "aarch64")]
fn guard_sets_dit() -> bool {
    #[target_feature(enable = "dit")]
    fn read() -> u64 {
        let pstate: u64;
        // SAFETY: `mrs _, DIT` reads a register and touches no memory; the
        // caller has checked that the CPU has DIT.
        unsafe {
            core::arch::asm!(
                "mrs {r}, DIT",
                r = out(reg) pstate,
                options(nomem, nostack, preserves_flags)
            )
        };
        pstate
    }
    if !std::arch::is_aarch64_feature_detected!("dit") {
        return false;
    }
    let _guard = rind::cpu::Dit::hold();
    // SAFETY: the CPU reported `dit` above.
    let pstate = unsafe { read() };
    pstate & (1 << 24) != 0
}

#[cfg(not(any(target_arch = "aarch64", target_arch = "xtensa")))]
fn guard_sets_dit() -> bool {
    false
}

#[cfg(not(target_arch = "xtensa"))]
fn toggle(c: &mut Criterion) {
    report_features();

    let verify = || black_box(rind::constant_time::verify(black_box(&[]), black_box(&[])));
    let mut group = c.benchmark_group("dit-toggle/verify-empty");
    group.bench_function("rind", |b| {
        let _dit = criterion::rind_dit();
        b.iter(verify)
    });
    group.finish();
    if let Some(mut group) = criterion::dit_per_call(c, "dit-toggle/verify-empty") {
        group.bench_function("rind", |b| b.iter(verify));
        group.finish();
    }

    // The guard makes no toggle where rind sets no DIT, so this row would time
    // an empty call there, under a name that says otherwise.
    if guard_sets_dit() {
        let mut group = c.benchmark_group("dit-toggle/hold-drop");
        group.bench_function("rind", |b| {
            b.iter(|| drop(black_box(rind::cpu::Dit::hold())))
        });
        group.finish();
    }

    let mut group = c.benchmark_group("dit-toggle/no-entry");
    group.bench_function("rind", |b| {
        b.iter(|| black_box(rind::cpu::has_aes_hardware()))
    });
    group.finish();
}

#[cfg(not(target_arch = "xtensa"))]
criterion_group!(benches, toggle);
#[cfg(not(target_arch = "xtensa"))]
criterion_main!(benches);
