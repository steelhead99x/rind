// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20-Poly1305 in one pass: pyca/verified-garbage's SVE2 routines
//! where the CPU has SVE2; otherwise VG's NEON routines at the lengths
//! `seal_runs_vg` and `open_runs_vg` name, both imported by
//! `admin/import-vg`, and at the rest rind's copy of aws-lc's
//! `chacha20_poly1305_armv8`, which interleaves NEON ChaCha20 with scalar
//! Poly1305. The copy keeps aws-lc's instructions but inlines its AAD helper
//! and lays each routine's control flow out as the `ite` and `loop` of rind's
//! Lean model of AArch64, where `RindIsa/AArch64/ChaCha20Poly1305.lean` holds
//! each routine as one program; `admin/prove lean` checks that rind's Linux
//! build emits that program's bytes. The `.apple.s` bodies, which it does not
//! check, hold the same instructions in Apple's syntax.
//!
//! VG proves in Lean that its routines meet RFC 8439 and take the same
//! branches and memory addresses whatever the key, nonce, and data, but for
//! whether open authenticated, which its contract lets it reveal. Those proofs
//! are over its models of the instructions, which `admin/prove vg` cosimulates.
//! `proofs/Rind/Aarch64/VgChaCha20Poly1305.lean` takes those theorems as
//! axioms about `seal_sve2`, `open_sve2`, `seal_neon`, and `open_neon` and
//! proves `seal` and `open` from them wherever those routines run. The copy
//! of aws-lc's is not yet proven: its correctness rests on aws-lc's use and
//! testing in BoringSSL and aws-lc. rind tests every path against RFC 8439,
//! Wycheproof, aws-lc-rs, and separate ChaCha20 and Poly1305 passes.
//!
//! VG's routines zero their stack scratch before returning, which AGENTS.md
//! allows an imported proven routine: VG defines each routine with that
//! wipe, offers none without it, and its proofs are of the instructions as
//! emitted. The lengths where they run are those where they outrun aws-lc's
//! code with that cost included.

use super::cpu::HaveSve2;
use super::vg::vg_chacha20_poly1305_open_neon::vg_chacha20_poly1305_open_neon;
use super::vg::vg_chacha20_poly1305_open_sve2::vg_chacha20_poly1305_open_sve2;
use super::vg::vg_chacha20_poly1305_seal_neon::vg_chacha20_poly1305_seal_neon;
use super::vg::vg_chacha20_poly1305_seal_sve2::vg_chacha20_poly1305_seal_sve2;
use crate::low::ct_equal;

/// Encrypts `inout` in place, returning the tag over `aad` and the ciphertext.
pub(crate) fn seal(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    match HaveSve2::check() {
        Some(sve2) => seal_sve2(sve2, key, nonce, aad, inout),
        None => {
            if seal_runs_vg(inout.len()) {
                seal_neon(key, nonce, aad, inout)
            } else {
                seal_aws_lc(key, nonce, aad, inout)
            }
        }
    }
}

/// Decrypts `inout` in place, and returns whether `tag` is its tag over
/// `aad` and the ciphertext, a secret.
pub(crate) fn open(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
    tag: &[u8; 16],
) -> bool {
    match HaveSve2::check() {
        Some(sve2) => open_sve2(sve2, key, nonce, aad, inout, tag),
        None => {
            if open_runs_vg(inout.len()) {
                open_neon(key, nonce, aad, inout, tag)
            } else {
                ct_equal(&open_aws_lc(key, nonce, aad, inout), tag)
            }
        }
    }
}

// The message lengths at which CPUs without SVE2 run VG's NEON routines,
// where they took less time than aws-lc's on both an Apple M5 Pro and a
// Neoverse N2. Each code's cost steps at 64-byte blocks, and the two step at
// different blocks, so aws-lc's stays faster at some lengths past VG's first
// win: sealing up to 576 bytes and from 769 to 896, by up to 1.22x, and
// opening up to 128 bytes, from 257 to 448, and from 896 to 960, by up to
// 1.2x. From 961 bytes VG's took 0.72 to 1.00 of aws-lc's time.

/// Whether a seal of `len` bytes runs VG's NEON routine.
fn seal_runs_vg(len: usize) -> bool {
    matches!(len, 577..=768 | 897..)
}

/// Whether an open of `len` bytes runs VG's NEON routine. Never in a
/// ctgrind build: VG's open branches on whether the tag matched, which its
/// contract allows and valgrind cannot tell from a leak, so ctgrind checks
/// aws-lc's open at every length and `ct_qemu_chacha20poly1305` VG's, as
/// valgrind hides SVE2 and AVX-512 IFMA and so VG's other opens.
fn open_runs_vg(len: usize) -> bool {
    !cfg!(feature = "__ctgrind") && matches!(len, 129..=256 | 449..=895 | 961..)
}

fn seal_sve2(
    _: HaveSve2,
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
) -> [u8; 16] {
    let mut tag = [0u8; 16];
    let (data, len) = (inout.as_mut_ptr(), inout.len());
    // SAFETY: each pointer is to a distinct Rust object of the length the
    // routine reads or writes, and the token proves SVE2.
    unsafe {
        asm_call!(unsafe extern "C" vg_chacha20_poly1305_seal_sve2(key, nonce, aad.as_ptr(), aad.len(), data, len, &mut tag))
    };
    tag
}

/// As `open`, and zeroes `inout` when `tag` is not its tag.
fn open_sve2(
    _: HaveSve2,
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
    tag: &[u8; 16],
) -> bool {
    let (data, len) = (inout.as_mut_ptr(), inout.len());
    // SAFETY: as in `seal_sve2`.
    let valid = unsafe {
        asm_call!(unsafe extern "C" vg_chacha20_poly1305_open_sve2(key, nonce, aad.as_ptr(), aad.len(), data, len, tag))
    };
    valid == 1
}

fn seal_neon(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    let mut tag = [0u8; 16];
    let (data, len) = (inout.as_mut_ptr(), inout.len());
    // SAFETY: each pointer is to a distinct Rust object of the length the
    // routine reads or writes. rind requires NEON.
    unsafe {
        asm_call!(unsafe extern "C" vg_chacha20_poly1305_seal_neon(key, nonce, aad.as_ptr(), aad.len(), data, len, &mut tag))
    };
    tag
}

/// As `open`, and zeroes `inout` when `tag` is not its tag.
fn open_neon(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
    tag: &[u8; 16],
) -> bool {
    let (data, len) = (inout.as_mut_ptr(), inout.len());
    // SAFETY: as in `seal_neon`.
    let valid = unsafe {
        asm_call!(unsafe extern "C" vg_chacha20_poly1305_open_neon(key, nonce, aad.as_ptr(), aad.len(), data, len, tag))
    };
    valid == 1
}

fn seal_aws_lc(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    let mut data = Data::new(key, nonce);
    let ptr = inout.as_mut_ptr();
    // SAFETY: `inout` is `inout.len()` readable and writable bytes, which the
    // routine allows to alias exactly, `aad` is `aad.len()` readable bytes,
    // and `data` is the block it reads and writes. rind requires NEON.
    unsafe {
        asm_call!(unsafe extern "C" chacha20_poly1305_seal(ptr, ptr, inout.len(), aad.as_ptr(), aad.len(), &mut data))
    };
    data.tag()
}

/// Decrypts `inout` in place, returning the tag over `aad` and the
/// ciphertext.
fn open_aws_lc(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    let mut data = Data::new(key, nonce);
    let ptr = inout.as_mut_ptr();
    // SAFETY: as in `seal_aws_lc`.
    unsafe {
        asm_call!(unsafe extern "C" chacha20_poly1305_open(ptr, ptr, inout.len(), aad.as_ptr(), aad.len(), &mut data))
    };
    data.tag()
}

/// The routines' argument block: the key and the nonce, after the counter
/// they start from. On return, the tag overwrites the start of the key.
#[repr(C, align(16))]
struct Data {
    key: [u8; 32],
    counter: u32,
    nonce: [u8; 12],
}

impl Data {
    fn new(key: &[u8; 32], nonce: &[u8; 12]) -> Self {
        Self {
            key: *key,
            // Block 0 keys Poly1305.
            counter: 0,
            nonce: *nonce,
        }
    }

    fn tag(&self) -> [u8; 16] {
        let mut tag = [0u8; 16];
        tag.copy_from_slice(&self.key[..16]);
        tag
    }
}

/// The ChaCha20 constant, the counter increments, a rotation mask, and the
/// Poly1305 clamp, which the routines load at once.
#[repr(C, align(128))]
struct Consts([u8; 64]);

static CHACHA20_CONSTS: Consts = Consts(include!(
    "aws_lc/chacha20_poly1305_armv8.chacha20_consts.rs"
));

/// Defines a naked function running rind's structured copy of an aws-lc
/// routine, `chacha20poly1305/<file>.<os>.s`, which reads `CHACHA20_CONSTS`.
macro_rules! routine {
    ($name:ident, $file:literal) => {
        #[unsafe(naked)]
        unsafe extern "C" fn $name(
            out: *mut u8,
            input: *const u8,
            len: usize,
            aad: *const u8,
            aad_len: usize,
            data: *mut Data,
        ) {
            #[cfg(not(target_vendor = "apple"))]
            core::arch::naked_asm!(
                include_str!(concat!("chacha20poly1305/", $file, ".linux.s")),
                chacha20_consts = sym CHACHA20_CONSTS,
            );
            #[cfg(target_vendor = "apple")]
            core::arch::naked_asm!(
                include_str!(concat!("chacha20poly1305/", $file, ".apple.s")),
                chacha20_consts = sym CHACHA20_CONSTS,
            );
        }
    };
}

routine!(chacha20_poly1305_seal, "seal");
routine!(chacha20_poly1305_open, "open");

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;
    use crate::low::generic::chacha20poly1305 as separate;

    type Seal = fn(&[u8; 32], &[u8; 12], &[u8], &mut [u8]) -> [u8; 16];
    type Open = fn(&[u8; 32], &[u8; 12], &[u8], &mut [u8], &[u8; 16]) -> bool;

    /// Each one-pass path the CPU can run, by name, and whether its open
    /// runs VG's under ctgrind, which branches on whether the tag matched.
    fn paths() -> Vec<(&'static str, Seal, Open, bool)> {
        let mut paths: Vec<(&'static str, Seal, Open, bool)> = vec![
            (
                "aws-lc",
                seal_aws_lc,
                |key, nonce, aad, inout, tag| ct_equal(&open_aws_lc(key, nonce, aad, inout), tag),
                false,
            ),
            ("neon", seal_neon, open_neon, true),
            ("dispatch", seal, open, false),
        ];
        if HaveSve2::check().is_some() {
            paths.push((
                "sve2",
                |key, nonce, aad, inout| {
                    seal_sve2(HaveSve2::check().unwrap(), key, nonce, aad, inout)
                },
                |key, nonce, aad, inout, tag| {
                    open_sve2(HaveSve2::check().unwrap(), key, nonce, aad, inout, tag)
                },
                true,
            ));
        }
        paths
    }

    // `open_runs_vg` never runs VG's open in a ctgrind build and runs it from
    // 129 bytes otherwise; no output tells the two apart, so this
    // pins it.
    #[test]
    fn open_runs_vg_selector() {
        assert!(!open_runs_vg(128));
        assert_eq!(open_runs_vg(129), !cfg!(feature = "__ctgrind"));
    }

    // Every message length through the routines' blocks and the tails after
    // them, AAD lengths around their 16-byte blocks, and a long message, on
    // each path, against separate ChaCha20 and Poly1305 passes, under a key
    // `admin/ctgrind` keeps secret, and opening under a tag one bit off.
    // VG's open branches on whether the tag matched, which its contract
    // allows and valgrind cannot tell from a leak, so a path that runs it
    // opens under a public copy of the key, and `ct_qemu_chacha20poly1305`
    // checks VG's routines instead; a ctgrind build's dispatch never runs it
    // (see `open_runs_vg`).
    #[test]
    fn matches_separate_passes() {
        let public_key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let key = public_key;
        ct::secret_slice(&key);
        let nonce = core::array::from_fn(|i| (i * 7) as u8);
        let input: Vec<u8> = (0..16384 + 15).map(|i| (i * 13 + 5) as u8).collect();
        let lens = (0..=1100)
            .map(|len| (len, 13))
            .chain((0..=48).map(|aad| (300, aad)));
        for (len, aad_len) in lens.chain([(16384 + 15, 13)]) {
            let aad = &input[..aad_len];
            let mut sealed = input[..len].to_vec();
            let tag = ct::into_public(separate::seal(&key, &nonce, aad, &mut sealed));
            ct::public_slice(&sealed);
            for (path, seal, open, open_branches) in paths() {
                let open_key = if open_branches { &public_key } else { &key };
                let mut ours = input[..len].to_vec();
                let ours_tag = ct::into_public(seal(&key, &nonce, aad, &mut ours));
                ct::public_slice(&ours);
                assert_eq!(
                    ours_tag, tag,
                    "{path} seal tag, {len} bytes, {aad_len} of AAD"
                );
                assert_eq!(ours, sealed, "{path} seal, {len} bytes, {aad_len} of AAD");
                let valid = ct::into_public(open(open_key, &nonce, aad, &mut ours, &tag));
                ct::public_slice(&ours);
                assert!(valid, "{path} open, {len} bytes, {aad_len} of AAD");
                assert_eq!(
                    ours,
                    input[..len],
                    "{path} open, {len} bytes, {aad_len} of AAD"
                );

                let mut wrong = tag;
                wrong[len % 16] ^= 1 << (len % 8);
                let mut forged = sealed.clone();
                let valid = ct::into_public(open(open_key, &nonce, aad, &mut forged, &wrong));
                assert!(!valid, "{path} forged, {len} bytes, {aad_len} of AAD");
            }
        }
    }

    // Valgrind hides SVE2, and cannot tell VG's open's branch on whether the
    // tag matched from a leak, so `admin/ct-qemu` traces VG's SVE2 and NEON
    // routines here instead, under qemu-aarch64's `max` CPU, with a secret
    // key, nonce, AAD, message, and tag, opening under the right tag and a
    // wrong one, which only the result may tell apart. The routines branch
    // on the lengths into size-specialized kernels and tails. These lengths
    // reach every basic block, of both SVE2 routines and their callees, that
    // qemu's exec log saw in 3,471 sampled pairs of lengths (messages to
    // 8 KiB, AAD to 600 bytes), sealed, opened, and forged. The NEON
    // routines branch as the SVE2 ones do, but for one kernel the NEON open
    // lacks, and call VG's NEON ChaCha20 where those call its SVE2 one. The
    // NEON open takes one more route for a message of 192 bytes with 64 of
    // AAD, and (63, 192) is its control.
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_chacha20poly1305() {
        use crate::low::aarch64::ct_qemu;

        let sve2 = HaveSve2::check().expect("SVE2");
        let seed = ct_qemu::seed().to_le_bytes();
        let bytes = |n| seed.iter().cycle().take(n).copied().collect::<Vec<u8>>();
        let key = bytes(32).try_into().unwrap();
        let nonce = bytes(12).try_into().unwrap();
        let wrong = bytes(16).try_into().unwrap();
        for (aad_len, msg_len) in [
            (29, 43),
            (4, 262),
            (13, 322),
            (64, 192),
            (63, 192),
            (2, 459),
            (3, 520),
            (13, 768),
            (13, 769),
            (13, 896),
            (13, 960),
            (9, 1028),
            (13, 1088),
            (13, 1090),
            (3, 1351),
        ] {
            let aad = bytes(aad_len);
            let mut msg = bytes(msg_len);
            let tag = ct_qemu::traced(|| seal_sve2(sve2, &key, &nonce, &aad, &mut msg));
            assert!(ct_qemu::traced(|| open_sve2(
                sve2, &key, &nonce, &aad, &mut msg, &tag
            )));
            assert!(!ct_qemu::traced(|| open_sve2(
                sve2, &key, &nonce, &aad, &mut msg, &wrong
            )));
            let mut msg = bytes(msg_len);
            let tag = ct_qemu::traced(|| seal_neon(&key, &nonce, &aad, &mut msg));
            assert!(ct_qemu::traced(|| open_neon(
                &key, &nonce, &aad, &mut msg, &tag
            )));
            assert!(!ct_qemu::traced(|| open_neon(
                &key, &nonce, &aad, &mut msg, &wrong
            )));
        }
    }
}
