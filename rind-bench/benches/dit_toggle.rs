//! What one enter/exit of rind's per-call guard costs, apart from any work.
//!
//! Every rind call that handles a secret enters at its start and leaves at its
//! end; on Apple's cores with DIT that sets data-independent timing on and then
//! off, with a speculation barrier after the set. These rows time calls that do
//! almost nothing, so the toggle is nearly all of what they measure:
//!
//! - `dit-toggle/verify-empty/rind`: `constant_time::verify` of two empty
//!   slices, one entry per call, with DIT off between calls.
//! - `dit-toggle/verify-empty/rind-dit-held`: the same inside a held
//!   [`rind::cpu::Dit`], where the entry finds DIT already on. On an Apple CPU
//!   with DIT, `rind` minus `rind-dit-held` is the cost of one toggle. Elsewhere
//!   the second row is not made, and `rind` is the cost of an empty call.
//! - `dit-toggle/hold-drop/rind`: `Dit::hold()` then drop, one toggle through the
//!   public guard. Not made where the guard does nothing.
//! - `dit-toggle/no-entry/rind`: a public call that makes no entry, for the cost
//!   of calling and timing alone.
//!
//! Run `rind` and `rind-dit-held` with `RIND_CPU_DISABLE_dit=1` (needs
//! `--cfg rind_cpu_disable` in a release build) and the two rows should agree:
//! rind then sets no DIT, so the toggle's cost is the difference.

#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod criterion;
#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use criterion::{Criterion, criterion_group, criterion_main};

/// Says on stderr whether this CPU reports `dit` and `sb`, which pick what the
/// guard runs: `sb` after setting DIT where there is one, `dsb nsh; isb sy`
/// where not. The devbench report lists the same features under `device`.
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

#[cfg(not(target_arch = "xtensa"))]
fn toggle(c: &mut Criterion) {
    report_features();

    let mut group = c.benchmark_group("dit-toggle/verify-empty");
    for (lib, _dit) in criterion::rind_rows() {
        group.bench_function(lib, |b| {
            b.iter(|| black_box(rind::constant_time::verify(black_box(&[]), black_box(&[]))))
        });
    }
    group.finish();

    // The guard makes no toggle where rind sets no DIT, so this row would time
    // an empty call there, under a name that says otherwise.
    if criterion::rind_rows().count() > 1 {
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
