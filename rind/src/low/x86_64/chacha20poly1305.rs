// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20-Poly1305 in one pass: pyca/verified-garbage's AVX-512 IFMA
//! routines, imported by `admin/import-vg`, where the CPU has AVX512_IFMA,
//! at every length, since they matched or beat aws-lc's at every size
//! measured on Zen 5 and Granite Rapids. Otherwise aws-lc's
//! `chacha20_poly1305_x86_64`, which interleaves ChaCha20 with Poly1305,
//! imported by `admin/import-aws-lc`, with AVX2 where the CPU has it and
//! SSE4.1 otherwise; CPUs with AVX-512 but no IFMA, which no measurement
//! covered, keep it too. Without SSE4.1, ChaCha20 and Poly1305 run in
//! separate passes.
//!
//! VG proves in Lean that its routines meet RFC 8439 and take the same
//! branches and memory addresses whatever the key, nonce, and data, but for
//! whether open authenticated, which its contract lets it reveal. Those
//! proofs are over its models of the instructions, which `admin/prove vg`
//! cosimulates. The aws-lc assembly is not formally verified: its
//! correctness rests on its use and testing in BoringSSL and aws-lc. rind
//! tests both against RFC 8439, Wycheproof, aws-lc-rs, and separate
//! ChaCha20 and Poly1305 passes.
//!
//! VG's routines zero their stack scratch before returning, which AGENTS.md
//! allows an imported proven routine: VG defines each routine with that
//! wipe, offers none without it, and its proofs are of the instructions as
//! emitted. They outrun aws-lc's code with that cost included.

use super::cpu::{HaveAvx2, HaveIfmaForVgChaCha20Poly1305, HaveSse41};
use super::vg::vg_chacha20_poly1305_open_ifma::vg_chacha20_poly1305_open_ifma;
use super::vg::vg_chacha20_poly1305_seal_ifma::vg_chacha20_poly1305_seal_ifma;
use crate::low::generic::chacha20poly1305 as separate;
use crate::low::{Mcdt, ct_equal};

/// Encrypts `inout` in place, returning the tag over `aad` and the ciphertext.
pub(crate) fn seal(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    match (HaveIfmaForVgChaCha20Poly1305::check(), HaveSse41::check()) {
        (Some(ifma), _) => seal_ifma(ifma, key, nonce, aad, inout),
        (None, Some(sse41)) => one_pass(sse41, HaveAvx2::check(), key, nonce, aad, inout, true),
        (None, None) => separate::seal(key, nonce, aad, inout),
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
    match (HaveIfmaForVgChaCha20Poly1305::check(), HaveSse41::check()) {
        (Some(ifma), _) => open_ifma(ifma, key, nonce, aad, inout, tag),
        (None, Some(sse41)) => ct_equal(
            &one_pass(sse41, HaveAvx2::check(), key, nonce, aad, inout, false),
            tag,
        ),
        (None, None) => separate::open(key, nonce, aad, inout, tag),
    }
}

// VG's routines hash with `vpmadd52luq` and `vpmuludq`, which Intel's MXCSR
// mitigation covers. They enter it themselves where they run those, and
// leave MXCSR as they set it, so each wrapper holds a restoring `Mcdt`:
// never inlined, holding it throughout, as `low::mcdt` requires.

#[inline(never)]
fn seal_ifma(
    _: HaveIfmaForVgChaCha20Poly1305,
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
) -> [u8; 16] {
    let _mcdt = Mcdt::enter_restoring();
    let mut tag = [0u8; 16];
    let (data, len) = (inout.as_mut_ptr(), inout.len());
    // SAFETY: each pointer is to a distinct Rust object of the length the
    // routine reads or writes, none of which overlaps the stack below the
    // return address or wraps the address space, as no object does, and the
    // token proves AVX, AVX2, AVX-512 F and VL, and AVX512_IFMA.
    unsafe {
        asm_call!(unsafe extern "sysv64" vg_chacha20_poly1305_seal_ifma(key, nonce, aad.as_ptr(), aad.len(), data, len, &mut tag))
    };
    tag
}

/// As `open`, and zeroes `inout` when `tag` is not its tag.
#[inline(never)]
fn open_ifma(
    _: HaveIfmaForVgChaCha20Poly1305,
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
    tag: &[u8; 16],
) -> bool {
    let _mcdt = Mcdt::enter_restoring();
    let (data, len) = (inout.as_mut_ptr(), inout.len());
    // SAFETY: as in `seal_ifma`.
    let valid = unsafe {
        asm_call!(unsafe extern "sysv64" vg_chacha20_poly1305_open_ifma(key, nonce, aad.as_ptr(), aad.len(), data, len, tag))
    };
    valid == 1
}

/// The routines' argument block: aws-lc's `chacha20_poly1305_seal_data`,
/// whose first 48 bytes are its `chacha20_poly1305_open_data`, then the
/// word rind's copies read in place of `OPENSSL_ia32cap_P[2]`. On return,
/// the tag overwrites the start of the key.
#[repr(C, align(16))]
struct Data {
    key: [u8; 32],
    counter: u32,
    nonce: [u8; 12],
    extra_ciphertext: *const u8,
    extra_ciphertext_len: usize,
    ia32cap: u32,
}

/// The `OPENSSL_ia32cap_P[2]` bits, AVX2 and BMI2, that pick the routines'
/// AVX2 half.
const IA32CAP_AVX2_BMI2: u32 = (1 << 5) | (1 << 8);

fn one_pass(
    _: HaveSse41,
    avx2: Option<HaveAvx2>,
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
    seal: bool,
) -> [u8; 16] {
    let mut data = Data {
        key: *key,
        // Block 0 keys Poly1305.
        counter: 0,
        nonce: *nonce,
        extra_ciphertext: core::ptr::null(),
        extra_ciphertext_len: 0,
        ia32cap: match avx2 {
            Some(_) => IA32CAP_AVX2_BMI2,
            None => 0,
        },
    };
    let ptr = inout.as_mut_ptr();
    // SAFETY: `inout` is `inout.len()` readable and writable bytes, which the
    // routines allow to alias exactly, `aad` is `aad.len()` readable bytes,
    // and `data` is the block they read and write. The tokens prove SSE4.1,
    // and AVX2 and BMI2 where `ia32cap` picks the AVX2 half.
    unsafe {
        match seal {
            true => {
                asm_call!(unsafe extern "sysv64" chacha20_poly1305_seal(ptr, ptr, inout.len(), aad.as_ptr(), aad.len(), &mut data))
            }
            false => {
                asm_call!(unsafe extern "sysv64" chacha20_poly1305_open(ptr, ptr, inout.len(), aad.as_ptr(), aad.len(), &mut data))
            }
        }
    }
    let mut tag = [0u8; 16];
    tag.copy_from_slice(&data.key[..16]);
    tag
}

/// The ChaCha20 constant, rotation masks, counter increments, and Poly1305
/// clamp, which the routines load across.
#[repr(C, align(64))]
struct Consts([u8; 192]);

/// Masks keeping the first 1 to 16 bytes of a block, for the seal routine.
#[repr(C, align(64))]
struct AndMasks([u8; 256]);

static CHACHA20_CONSTS: Consts = Consts(include!(
    "aws_lc/chacha20_poly1305_x86_64.chacha20_consts.rs"
));
static AND_MASKS: AndMasks = AndMasks(include!("aws_lc/chacha20_poly1305_x86_64.and_masks.rs"));

// The routines take the System V ABI on every OS, since their text is
// aws-lc's ELF and Mach-O flavors, which read their arguments from its
// registers.

#[unsafe(naked)]
unsafe extern "sysv64" fn chacha20_poly1305_open(
    out: *mut u8,
    input: *const u8,
    len: usize,
    aad: *const u8,
    aad_len: usize,
    data: *mut Data,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/chacha20_poly1305_open.linux.s"),
        chacha20_consts = sym CHACHA20_CONSTS,
        poly_hash_ad_internal = sym poly_hash_ad_internal,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/chacha20_poly1305_open.apple.s"),
        chacha20_consts = sym CHACHA20_CONSTS,
        poly_hash_ad_internal = sym poly_hash_ad_internal,
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn chacha20_poly1305_seal(
    out: *mut u8,
    input: *const u8,
    len: usize,
    aad: *const u8,
    aad_len: usize,
    data: *mut Data,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/chacha20_poly1305_seal.linux.s"),
        chacha20_consts = sym CHACHA20_CONSTS,
        and_masks = sym AND_MASKS,
        poly_hash_ad_internal = sym poly_hash_ad_internal,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/chacha20_poly1305_seal.apple.s"),
        chacha20_consts = sym CHACHA20_CONSTS,
        and_masks = sym AND_MASKS,
        poly_hash_ad_internal = sym poly_hash_ad_internal,
        options(att_syntax),
    );
}

/// Hashes the AAD into the Poly1305 state the two routines keep in
/// registers and on their stack frame; only they call it.
#[unsafe(naked)]
unsafe extern "sysv64" fn poly_hash_ad_internal() {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/poly_hash_ad_internal.linux.s"),
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/poly_hash_ad_internal.apple.s"),
        options(att_syntax),
    );
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;
    use crate::low::x86_64::adx_mux::tests::Rng;
    use crate::low::x86_64::ct_sde;

    type Seal = fn(&[u8; 32], &[u8; 12], &[u8], &mut [u8]) -> [u8; 16];
    type Open = fn(&[u8; 32], &[u8; 12], &[u8], &mut [u8], &[u8; 16]) -> bool;

    /// Each one-pass path the CPU can run, by name.
    fn paths() -> Vec<(&'static str, Seal, Open)> {
        let mut paths: Vec<(&'static str, Seal, Open)> = Vec::new();
        if HaveIfmaForVgChaCha20Poly1305::check().is_some() {
            paths.push((
                "vg ifma",
                |key, nonce, aad, inout| {
                    let t = HaveIfmaForVgChaCha20Poly1305::check().unwrap();
                    seal_ifma(t, key, nonce, aad, inout)
                },
                |key, nonce, aad, inout, tag| {
                    let t = HaveIfmaForVgChaCha20Poly1305::check().unwrap();
                    open_ifma(t, key, nonce, aad, inout, tag)
                },
            ));
        }
        if HaveSse41::check().is_some() && HaveAvx2::check().is_some() {
            paths.push((
                "aws-lc avx2",
                |key, nonce, aad, inout| {
                    let (sse41, avx2) = (HaveSse41::check().unwrap(), HaveAvx2::check());
                    one_pass(sse41, avx2, key, nonce, aad, inout, true)
                },
                |key, nonce, aad, inout, tag| {
                    let (sse41, avx2) = (HaveSse41::check().unwrap(), HaveAvx2::check());
                    ct_equal(&one_pass(sse41, avx2, key, nonce, aad, inout, false), tag)
                },
            ));
        }
        if HaveSse41::check().is_some() {
            paths.push((
                "aws-lc sse4.1",
                |key, nonce, aad, inout| {
                    one_pass(
                        HaveSse41::check().unwrap(),
                        None,
                        key,
                        nonce,
                        aad,
                        inout,
                        true,
                    )
                },
                |key, nonce, aad, inout, tag| {
                    let sse41 = HaveSse41::check().unwrap();
                    ct_equal(&one_pass(sse41, None, key, nonce, aad, inout, false), tag)
                },
            ));
        }
        paths
    }

    // The CPU's fastest path hides the others from every other test, so each
    // path the CPU runs is checked against separate passes directly, under a
    // key `admin/ctgrind` keeps secret: every message length through the
    // AVX2 half's 512-byte loop and the tails after it, AAD lengths around
    // aws-lc's 13-byte TLS case and its 16-byte blocks, and longer messages
    // through VG's wider loops, and opening under a tag one bit off, which
    // VG's routine answers by zeroing the message. Valgrind hides AVX-512,
    // so ctgrind checks only aws-lc's routines, and `ct_sde_chacha20poly1305`
    // VG's.
    #[test]
    fn paths_match() {
        let key = core::array::from_fn(|i| i as u8);
        ct::secret_slice(&key);
        let nonce = core::array::from_fn(|i| (i * 7) as u8);
        let input: Vec<u8> = (0..16384 + 15).map(|i| (i * 13 + 5) as u8).collect();
        let lens = (0..=1100)
            .map(|len| (len, 13))
            .chain((0..=48).map(|aad| (300, aad)))
            .chain([2047, 4097, 8191, 16384 + 15].map(|len| (len, 13)));
        let before = crate::low::mcdt::mxcsr();
        for (len, aad_len) in lens {
            let aad = &input[..aad_len];
            let mut sealed = input[..len].to_vec();
            let tag = ct::into_public(separate::seal(&key, &nonce, aad, &mut sealed));
            ct::public_slice(&sealed);
            for (path, seal, open) in paths() {
                let mut ours = input[..len].to_vec();
                let ours_tag = ct::into_public(seal(&key, &nonce, aad, &mut ours));
                ct::public_slice(&ours);
                assert_eq!(
                    ours_tag, tag,
                    "{path} seal tag, {len} bytes, {aad_len} of AAD"
                );
                assert_eq!(ours, sealed, "{path} seal, {len} bytes, {aad_len} of AAD");
                let valid = ct::into_public(open(&key, &nonce, aad, &mut ours, &tag));
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
                let valid = ct::into_public(open(&key, &nonce, aad, &mut forged, &wrong));
                assert!(!valid, "{path} forged, {len} bytes, {aad_len} of AAD");
            }
        }
        // VG's routines set MXCSR's status flags where they hash with
        // vectors, which their wrappers undo.
        assert_eq!(crate::low::mcdt::mxcsr(), before);
    }

    // Intel SDE runs VG's routines, which valgrind cannot, under
    // `admin/ct-sde`, with a secret key, nonce, AAD, message, and tag,
    // sealing, then opening under the right tag and a wrong one, which only
    // the result may tell apart. The routines branch on the lengths, which
    // are public, so these take the short and long AAD paths and each
    // message path: a partial block, the one-block-group and the four-group
    // loops with tails, a run long enough for the widest loop, and open's
    // AVX-512 VL body for 449 to 639 bytes, whole blocks and with a tail.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_chacha20poly1305() {
        let t = HaveIfmaForVgChaCha20Poly1305::check().expect("AVX512_IFMA");
        let mut rng = Rng(ct_sde::seed());
        let mut bytes = |n| (0..n).map(|_| rng.next() as u8).collect::<Vec<u8>>();
        let key = bytes(32).try_into().unwrap();
        let nonce = bytes(12).try_into().unwrap();
        let wrong = bytes(16).try_into().unwrap();
        for (aad_len, msg_len) in [
            (0, 0),
            (13, 9),
            (5, 64),
            (29, 300),
            (13, 512),
            (7, 601),
            (13, 1350),
            (77, 4097),
        ] {
            let aad = bytes(aad_len);
            let mut msg = bytes(msg_len);
            let tag = ct_sde::traced(|| seal_ifma(t, &key, &nonce, &aad, &mut msg));
            let mut forged = msg.clone();
            assert!(ct_sde::traced(|| open_ifma(
                t, &key, &nonce, &aad, &mut msg, &tag
            )));
            assert!(!ct_sde::traced(|| open_ifma(
                t,
                &key,
                &nonce,
                &aad,
                &mut forged,
                &wrong
            )));
        }
    }
}
