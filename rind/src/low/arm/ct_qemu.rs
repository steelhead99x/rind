// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The constant-time check for what valgrind hides: the crypto extension
//! from armv7 programs, and SHA3 from aarch64 ones. `admin/ct-qemu` runs
//! each test named `ct_qemu` twice under qemu-arm or qemu-aarch64, with a
//! different [`seed`] each time, and compares the addresses of every
//! instruction and memory access in the [`traced`] region.

/// The seed `admin/ct-qemu` sets for this run, from which the test derives
/// every secret it passes to the traced code.
pub(crate) fn seed() -> u64 {
    let seed = std::env::var("RIND_CT_QEMU_SEED").expect("run by admin/ct-qemu");
    u64::from_str_radix(&seed, 16).unwrap()
}

/// Whether the CPU `admin/ct-qemu` runs this test under, `max` or
/// `cortex-a15`, has the crypto extension: `max` does, so the test requires
/// the hardware AES, and the Cortex-A15 has only NEON, so it requires that.
#[cfg(target_arch = "arm")]
pub(crate) fn crypto_ext() -> bool {
    match std::env::var("RIND_CT_QEMU_CPU")
        .expect("run by admin/ct-qemu")
        .as_str()
    {
        "max" => true,
        "cortex-a15" => false,
        cpu => panic!("unknown qemu cpu {cpu}"),
    }
}

/// Runs `f` between the marks that start and stop the plugin's trace.
pub(crate) fn traced<T>(f: impl FnOnce() -> T) -> T {
    // SAFETY: an unallocated hint, which executes as a no-op in ARM and A64.
    unsafe { core::arch::asm!("hint #82", options(nostack, preserves_flags)) };
    let r = core::hint::black_box(f());
    // SAFETY: as above.
    unsafe { core::arch::asm!("hint #83", options(nostack, preserves_flags)) };
    r
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // `admin/ct-qemu` requires these to differ between seeds, so that a
    // harness that traces nothing, or strips the addresses it compares,
    // fails.

    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_planted_branch() {
        let secret = core::hint::black_box(seed());
        traced(|| {
            if secret & 1 == 1 {
                core::hint::black_box(0);
            }
        });
    }

    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_planted_index() {
        let secret = core::hint::black_box(seed());
        let table = core::hint::black_box([0u8; 64]);
        traced(|| core::hint::black_box(&table)[secret as usize % 64]);
    }
}
