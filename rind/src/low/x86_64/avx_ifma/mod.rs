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
//! allocates at its entry (not the red zone, which Windows lacks), zeroes
//! before it returns, and frees. No other instruction, branch, or memory
//! access changes, so the routines compute what VG's do. `admin/ct-sde`
//! checks the ladder's trace under an Arrow Lake model, as `admin/ctgrind`
//! cannot decode AVX-IFMA, and `rind/tests` check them against s2n-bignum,
//! aws-lc-rs, and Wycheproof. VG's Lean proofs do not cover them; `quest` plans their proof.

pub(crate) mod vg_ed25519_verify_avx2_ifma;
pub(crate) mod vg_ed25519_verify_equation_ifma;
pub(crate) mod vg_x25519_exchange_ifma;
pub(crate) mod vg_x25519_ifma;
