// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-KEM-768 on pyca/verified-garbage's proven routines (`super::vg`).
//!
//! Each routine is a whole FIPS 203 operation, its hashing included. Its
//! encapsulation measured faster than rind's with the SHA-3 instructions, so
//! rind takes it there; without them, and for key generation and
//! decapsulation, rind's own was faster. A routine returns 0 only if a
//! `SampleNTT` reached VG's bound on its loop (FIPS 203 Appendix B), with
//! probability below 2^-261; these return `None` then, and the caller runs
//! rind's arithmetic instead.

use core::mem::MaybeUninit;

use super::cpu::HaveSha3;
use super::vg;
pub(crate) use crate::low::generic::mlkem768_vg::KeyPair;

/// The 32 KiB of working space each routine takes, aligned to a cache line
/// as VG's own API aligns it. The routines accept any initial contents, and
/// leave each byte unchanged or zero: each zeroes it before returning. VG
/// proves no variant without that wipe, so rind keeps it, as AGENTS.md's
/// exception for imported routines allows; the measured speed includes its
/// cost.
#[repr(C, align(64))]
struct Scratch(MaybeUninit<[u64; 4096]>);

/// Proof that VG's encapsulation runs here: the CPU has the SHA-3
/// instructions.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Encaps(HaveSha3);

impl Encaps {
    pub(crate) fn check() -> Option<Self> {
        HaveSha3::check().map(Self)
    }

    /// FIPS 203's encapsulation key check (section 7.2): whether every
    /// coefficient `ek` encodes is below q.
    pub(crate) fn check_ek(self, ek: &[u8; 1184]) -> bool {
        // SAFETY: `ek` is valid for reads of its size, and a Rust object, so
        // it neither overlaps the stack nor wraps around the address space.
        unsafe { vg::vg_mlkem768_check_ek::vg_mlkem768_check_ek(ek) == 1 }
    }

    /// `ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17): the shared
    /// secret and ciphertext, given `H(ek)` as `h` where the caller has it.
    ///
    /// `ek` must have passed [`Self::check_ek`], and `h` be its hash.
    pub(crate) fn encaps(
        self,
        ek: &[u8; 1184],
        h: Option<&[u8; 32]>,
        m: &[u8; 32],
    ) -> Option<([u8; 32], [u8; 1088])> {
        // Apple's cores take the variant that also runs Keccak on the SHA-3
        // instructions, as VG's dispatcher picks; it measured slower on
        // Neoverse N2.
        self.encaps_with(cfg!(target_vendor = "apple"), ek, h, m)
    }

    /// [`Self::encaps`], on the variant that runs Keccak on the SHA-3
    /// instructions if `keccak_sha3`, or on NEON otherwise.
    fn encaps_with(
        self,
        keccak_sha3: bool,
        ek: &[u8; 1184],
        h: Option<&[u8; 32]>,
        m: &[u8; 32],
    ) -> Option<([u8; 32], [u8; 1088])> {
        use vg::*;
        let mut key = [0u8; 32];
        let mut ct = [0u8; 1088];
        let mut scratch = Scratch(MaybeUninit::uninit());
        let (k, c, s) = (&mut key, &mut ct, scratch.0.as_mut_ptr());
        // SAFETY: every pointer is to a distinct Rust object valid for its
        // size, so none overlaps another, the stack, or the end of the
        // address space. The caller checked `ek` and that `h` is its hash.
        // `self` proves the CPU has the SHA-3 instructions both variants
        // need.
        let ok = unsafe {
            match (keccak_sha3, h) {
                (false, None) => vg_mlkem768_encaps_x2_sha3::vg_mlkem768_encaps_x2_sha3(ek, m, k, c, s),
                (true, None) => vg_mlkem768_encaps_x2_sha3_keccak_sha3::vg_mlkem768_encaps_x2_sha3_keccak_sha3(ek, m, k, c, s),
                (false, Some(h)) => vg_mlkem768_encaps_h_x2_sha3::vg_mlkem768_encaps_h_x2_sha3(ek, h, m, k, c, s),
                (true, Some(h)) => vg_mlkem768_encaps_h_x2_sha3_keccak_sha3::vg_mlkem768_encaps_h_x2_sha3_keccak_sha3(ek, h, m, k, c, s),
            }
        };
        (ok == 1).then_some((key, ct))
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::mid::sha3::Sha3_256Context;
    use crate::test::{Acvp, acvp};

    // The CPU runs one variant, so each, with the key's hash and without,
    // is checked against ACVP's ML-KEM-768 encapsulations here.
    #[test]
    fn variants_match_acvp() {
        let Some(vg) = Encaps::check() else {
            return;
        };
        let mut ran = 0;
        for group in acvp("ML-KEM-encapDecap-FIPS203-tr1") {
            if group.str("parameterSet") != "ML-KEM-768" || group.str("function") != "encapsulation"
            {
                continue;
            }
            for test in group.tests() {
                let ek: [u8; 1184] = test.hex("ek").try_into().unwrap();
                let m: [u8; 32] = test.hex("m").try_into().unwrap();
                let mut h = Sha3_256Context::new();
                h.update(&ek);
                let h = h.finish();
                for keccak_sha3 in [false, true] {
                    for h in [None, Some(&h)] {
                        let (k, c) = vg.encaps_with(keccak_sha3, &ek, h, &m).unwrap();
                        assert_eq!(k, &test.hex("k")[..]);
                        assert_eq!(c, &test.hex("c")[..]);
                        ran += 1;
                    }
                }
            }
        }
        assert!(ran > 0);
    }

    // `mid::mlkem::ct_qemu_mlkem` traces the variant this target picks,
    // never Apple's on Linux, so this traces both under `admin/ct-qemu`,
    // with the key's hash and without: a secret message to a fixed key.
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_mlkem768_variants() {
        use crate::low::ct_qemu;
        use crate::mid::mlkem::{DecapKey, MlKem768};

        let vg = Encaps::check().expect("SHA3");
        let seed = ct_qemu::seed().to_le_bytes();
        let m = core::array::from_fn(|i| seed[i % seed.len()]);
        let ek = *DecapKey::<MlKem768>::keygen_internal(&[0x5a; 64])
            .encapsulation_key()
            .as_bytes();
        let mut h = Sha3_256Context::new();
        h.update(&ek);
        let h = h.finish();
        for keccak_sha3 in [false, true] {
            for h in [None, Some(&h)] {
                ct_qemu::traced(|| vg.encaps_with(keccak_sha3, &ek, h, &m));
            }
        }
    }
}
