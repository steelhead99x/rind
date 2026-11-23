// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! pyca/verified-garbage's AVX-512 IFMA X25519 ladder and Ed25519
//! verification, re-encoded for AVX-IFMA by `admin/avx-ifma`, for CPUs that
//! have IFMA in its VEX encoding and no AVX-512, such as Arrow Lake.
//!
//! These are not VG's proven bytes. The transform changes each EVEX
//! `vpmadd52luq`, `vpmadd52huq`, and `vpxorq` to its VEX form, one for one,
//! and where VG's ladder holds three 256-bit accumulators in ymm16 to ymm18,
//! which VEX cannot name, it renames each live range onto a ymm register dead
//! throughout it, or spills one around it to a 96-byte stack frame the ladder
//! allocates at its entry (not the red zone, which Windows lacks) and frees
//! before it returns, without wiping it, as with any stack temporary. No other instruction, branch, or memory
//! access changes, so the routines compute what VG's do. `admin/ct-sde`
//! checks the ladder's trace under an Arrow Lake model, as `admin/ctgrind`
//! cannot decode AVX-IFMA, and `rind/tests` check them against s2n-bignum,
//! aws-lc-rs, and Wycheproof. VG's Lean proofs do not cover them; `quest` plans their proof.

pub(crate) mod vg_ed25519_verify_avx2_ifma;
pub(crate) mod vg_ed25519_verify_equation_ifma;
pub(crate) mod vg_x25519_exchange_ifma;
pub(crate) mod vg_x25519_ifma;

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    const SOURCES: [&str; 4] = [
        include_str!("vg_ed25519_verify_avx2_ifma.rs"),
        include_str!("vg_ed25519_verify_equation_ifma.rs"),
        include_str!("vg_x25519_exchange_ifma.rs"),
        include_str!("vg_x25519_ifma.rs"),
    ];

    // The routines must not use the red zone, which Windows x86_64 lacks:
    // no memory operand is below the stack pointer, and a routine that
    // spills allocates its slots with `lea` on entry and frees them before
    // each of its returns, so the stack pointer is the caller's again there.
    #[test]
    fn spills_stay_above_the_stack_pointer() {
        for source in SOURCES {
            let asm: Vec<&str> = source
                .lines()
                .filter(|line| !line.starts_with("//"))
                .map(|line| line.trim_start().trim_start_matches("r#\""))
                .collect();
            let is_adjust = |line: &str| line.starts_with("lea ") && line.ends_with("(%rsp), %rsp");
            for line in &asm {
                let below = line.contains("-") && line.contains("(%rsp)");
                assert!(!below || is_adjust(line), "red zone access: {line}");
            }
            let allocs = asm.iter().filter(|l| l.starts_with("lea -")).count();
            let rets: Vec<usize> = (0..asm.len()).filter(|&i| asm[i] == ".byte 0xc3").collect();
            assert!(allocs <= 1, "one allocation, on entry");
            for ret in rets {
                assert_eq!(allocs == 1, is_adjust(asm[ret - 1]), "freed before ret");
            }
        }
    }
}
