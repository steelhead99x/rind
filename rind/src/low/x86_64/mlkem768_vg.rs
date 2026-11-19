// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-KEM-768 on pyca/verified-garbage's proven routines (`super::vg`).
//!
//! Each routine is a whole FIPS 203 operation, its hashing included. They
//! measured faster than rind's arithmetic at encapsulation on every x86_64
//! CPU, and at key generation and decapsulation with AVX-512, so those are
//! what rind takes. Each picks the widest variant the CPU runs, as VG's own
//! dispatcher does. A routine returns 0 only if a `SampleNTT` reached VG's
//! bound on its loop (FIPS 203 Appendix B), with probability below 2^-261;
//! these return `None` then, and the caller runs rind's arithmetic instead.

use core::mem::MaybeUninit;

use super::cpu::{HaveAvx, HaveAvx2, HaveAvx512ForVgMlKem};
use super::vg;

/// The 32 KiB of working space each routine takes, aligned to a cache line
/// as VG's own API aligns it. The routines accept any initial contents, and
/// leave each byte unchanged or zero: each zeroes the scratch it wrote, and
/// clears its registers and the stack below its caller's. VG proves no
/// variant without that wipe, so rind keeps it, as AGENTS.md's exception for
/// imported routines allows; the measured speed includes its cost.
#[repr(C, align(64))]
struct Scratch(MaybeUninit<[u64; 4096]>);

impl Scratch {
    fn new() -> Self {
        Self(MaybeUninit::uninit())
    }

    fn as_mut_ptr(&mut self) -> *mut [u64; 4096] {
        self.0.as_mut_ptr()
    }
}

/// Proof that VG's encapsulation runs here, as it does on every x86_64 CPU.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Encaps(());

impl Encaps {
    pub(crate) fn check() -> Option<Self> {
        Some(Self(()))
    }

    /// FIPS 203's encapsulation key check (section 7.2): whether every
    /// coefficient `ek` encodes is below q.
    pub(crate) fn check_ek(self, ek: &[u8; 1184]) -> bool {
        check_ek(HaveAvx2::check(), ek)
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
        encaps(Width::best(), ek, h, m)
    }
}

/// The variants of VG's encapsulation, each with proof that the CPU has its
/// features.
#[derive(Clone, Copy, Debug)]
enum Width {
    Base,
    Avx(HaveAvx),
    Avx2(HaveAvx2),
    Avx512(HaveAvx512ForVgMlKem),
}

impl Width {
    /// The widest the CPU runs, as VG's dispatcher picks.
    fn best() -> Self {
        let all = Self::all();
        all.into_iter().flatten().last().unwrap()
    }

    /// Each, if the CPU runs it, narrowest first.
    fn all() -> [Option<Self>; 4] {
        [
            Some(Self::Base),
            HaveAvx::check().map(Self::Avx),
            HaveAvx2::check().map(Self::Avx2),
            HaveAvx512ForVgMlKem::check().map(Self::Avx512),
        ]
    }
}

/// [`Encaps::check_ek`], on VG's AVX2 variant given proof the CPU has it.
fn check_ek(avx2: Option<HaveAvx2>, ek: &[u8; 1184]) -> bool {
    // SAFETY: `ek` is valid for reads of its size, and a Rust object, so it
    // neither overlaps the stack nor wraps around the address space. The
    // AVX2 variant runs only where the CPU has AVX and AVX2.
    let ok = unsafe {
        match avx2 {
            Some(_) => vg::vg_mlkem768_check_ek_avx2::vg_mlkem768_check_ek_avx2(ek),
            None => vg::vg_mlkem768_check_ek::vg_mlkem768_check_ek(ek),
        }
    };
    ok == 1
}

/// [`Encaps::encaps`], on the variant `width`.
fn encaps(
    width: Width,
    ek: &[u8; 1184],
    h: Option<&[u8; 32]>,
    m: &[u8; 32],
) -> Option<([u8; 32], [u8; 1088])> {
    use vg::*;
    let mut key = [0u8; 32];
    let mut ct = [0u8; 1088];
    let mut scratch = Scratch::new();
    let (k, c, s) = (&mut key, &mut ct, scratch.as_mut_ptr());
    // SAFETY: every pointer is to a distinct Rust object valid for its size,
    // so none overlaps another, the stack, or the end of the address space.
    // The caller checked `ek` and that `h` is its hash. `width` proves the
    // CPU has its variant's features: AVX-512 F, BW, and VL with AVX2 for
    // the AVX-512 one, AVX and AVX2 for the AVX2 one, and AVX for the AVX one.
    let ok = unsafe {
        match (width, h) {
            (Width::Base, None) => vg_mlkem768_encaps::vg_mlkem768_encaps(ek, m, k, c, s),
            (Width::Avx(_), None) => vg_mlkem768_encaps_avx::vg_mlkem768_encaps_avx(ek, m, k, c, s),
            (Width::Avx2(_), None) => {
                vg_mlkem768_encaps_avx2::vg_mlkem768_encaps_avx2(ek, m, k, c, s)
            }
            (Width::Avx512(_), None) => {
                vg_mlkem768_encaps_avx512::vg_mlkem768_encaps_avx512(ek, m, k, c, s)
            }
            (Width::Base, Some(h)) => vg_mlkem768_encaps_h::vg_mlkem768_encaps_h(ek, h, m, k, c, s),
            (Width::Avx(_), Some(h)) => {
                vg_mlkem768_encaps_h_avx::vg_mlkem768_encaps_h_avx(ek, h, m, k, c, s)
            }
            (Width::Avx2(_), Some(h)) => {
                vg_mlkem768_encaps_h_avx2::vg_mlkem768_encaps_h_avx2(ek, h, m, k, c, s)
            }
            (Width::Avx512(_), Some(h)) => {
                vg_mlkem768_encaps_h_avx512::vg_mlkem768_encaps_h_avx512(ek, h, m, k, c, s)
            }
        }
    };
    (ok == 1).then_some((key, ct))
}

/// Proof that VG's key generation and decapsulation run here: with
/// AVX-512, where they measured faster than rind's.
#[derive(Clone, Copy, Debug)]
pub(crate) struct KeyPair(HaveAvx512ForVgMlKem);

impl KeyPair {
    pub(crate) fn check() -> Option<Self> {
        HaveAvx512ForVgMlKem::check().map(Self)
    }

    /// `ML-KEM.KeyGen_internal(d, z)` (FIPS 203 Algorithm 16), from the
    /// seed `d || z`: the decapsulation key, which holds the encapsulation
    /// key.
    pub(crate) fn keygen(self, seed: &[u8; 64]) -> Option<[u8; 2400]> {
        let mut ek = [0u8; 1184];
        let mut dk = [0u8; 2400];
        let mut scratch = Scratch::new();
        // SAFETY: every pointer is to a distinct Rust object valid for its
        // size, so none overlaps another, the stack, or the end of the
        // address space; `self` proves the CPU has the routine's features.
        let ok = unsafe {
            vg::vg_mlkem768_keygen_avx512::vg_mlkem768_keygen_avx512(
                seed,
                &mut ek,
                &mut dk,
                scratch.as_mut_ptr(),
            )
        };
        (ok == 1).then_some(dk)
    }

    /// `ML-KEM.Decaps_internal(dk, c)` (FIPS 203 Algorithm 18): the shared
    /// secret, or the implicit rejection key for a ciphertext that does not
    /// re-encrypt to itself.
    ///
    /// `dk` must be [`Self::keygen`]'s output, which VG's contract asks for.
    pub(crate) fn decaps(self, dk: &[u8; 2400], ct: &[u8; 1088]) -> Option<[u8; 32]> {
        let mut key = [0u8; 32];
        let mut scratch = Scratch::new();
        // SAFETY: as for `keygen`, and `keygen` wrote `dk`.
        let ok = unsafe {
            vg::vg_mlkem768_decaps_avx512::vg_mlkem768_decaps_avx512(
                dk,
                ct,
                &mut key,
                scratch.as_mut_ptr(),
            )
        };
        (ok == 1).then_some(key)
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;
    use crate::mid::sha3::Sha3_256Context;
    use crate::test::{Acvp, acvp};

    // The CPU's widest variant hides the others from every other test, so
    // each variant it runs, with the key's hash and without, is checked
    // against ACVP's ML-KEM-768 encapsulations here, with a message
    // `admin/ctgrind` keeps secret; and both key checks against its
    // encapsulation key checks.
    #[test]
    fn widths_match_acvp() {
        let mut ran = 0;
        for group in acvp("ML-KEM-encapDecap-FIPS203-tr1") {
            if group.str("parameterSet") != "ML-KEM-768" {
                continue;
            }
            for test in group.tests() {
                let ek: [u8; 1184] = test.hex("ek").try_into().unwrap();
                match group.str("function") {
                    "encapsulation" => {
                        let m: [u8; 32] = test.hex("m").try_into().unwrap();
                        ct::secret_slice(&m);
                        let mut h = Sha3_256Context::new();
                        h.update(&ek);
                        let h = h.finish();
                        for width in Width::all().into_iter().flatten() {
                            for h in [None, Some(&h)] {
                                let (k, c) = ct::into_public(encaps(width, &ek, h, &m).unwrap());
                                assert_eq!(k, &test.hex("k")[..], "{width:?}");
                                assert_eq!(c, &test.hex("c")[..], "{width:?}");
                                ran += 1;
                            }
                        }
                    }
                    "encapsulationKeyCheck" => {
                        for avx2 in [None, HaveAvx2::check()] {
                            assert_eq!(check_ek(avx2, &ek), test.flag("testPassed"));
                        }
                    }
                    _ => {}
                }
            }
        }
        assert!(ran > 0);
    }
}
