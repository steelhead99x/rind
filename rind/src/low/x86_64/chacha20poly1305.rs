// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20-Poly1305: aws-lc's `chacha20_poly1305_x86_64`, which interleaves
//! ChaCha20 with Poly1305 in one pass, imported by `admin/import-aws-lc`,
//! with AVX2 where the CPU has it and SSE4.1 otherwise. Without SSE4.1,
//! ChaCha20 and Poly1305 run in separate passes.
//!
//! The aws-lc assembly is not formally verified: its correctness rests on its
//! use and testing in BoringSSL and aws-lc, and on rind's tests of it against
//! RFC 8439, Wycheproof, aws-lc-rs, and the separate passes.

use super::cpu::{HaveAvx2, HaveSse41};
use crate::low::ct_equal;
use crate::low::generic::chacha20poly1305 as separate;

/// Encrypts `inout` in place, returning the tag over `aad` and the ciphertext.
pub(crate) fn seal(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    match HaveSse41::check() {
        Some(sse41) => one_pass(sse41, HaveAvx2::check(), key, nonce, aad, inout, true),
        None => separate::seal(key, nonce, aad, inout),
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
    match HaveSse41::check() {
        Some(sse41) => ct_equal(
            &one_pass(sse41, HaveAvx2::check(), key, nonce, aad, inout, false),
            tag,
        ),
        None => separate::open(key, nonce, aad, inout, tag),
    }
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

    // The CPU's fastest path hides the others from every other test, so each
    // half of the routines the CPU runs is checked against separate passes
    // directly, under a key `admin/ctgrind` keeps secret: every message
    // length through the AVX2 half's 512-byte loop and the tails after it,
    // AAD lengths around aws-lc's 13-byte TLS case and its 16-byte blocks,
    // and a long message.
    #[test]
    fn paths_match() {
        let Some(sse41) = HaveSse41::check() else {
            return;
        };
        let key = core::array::from_fn(|i| i as u8);
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
            let halves = [
                HaveAvx2::check().map(|avx2| ("avx2", Some(avx2))),
                Some(("sse4.1", None)),
            ];
            for (path, avx2) in halves.into_iter().flatten() {
                let mut ours = input[..len].to_vec();
                let ours_tag =
                    ct::into_public(one_pass(sse41, avx2, &key, &nonce, aad, &mut ours, true));
                ct::public_slice(&ours);
                assert_eq!(
                    ours_tag, tag,
                    "{path} seal tag, {len} bytes, {aad_len} of AAD"
                );
                assert_eq!(ours, sealed, "{path} seal, {len} bytes, {aad_len} of AAD");
                let ours_tag =
                    ct::into_public(one_pass(sse41, avx2, &key, &nonce, aad, &mut ours, false));
                ct::public_slice(&ours);
                assert_eq!(
                    ours_tag, tag,
                    "{path} open tag, {len} bytes, {aad_len} of AAD"
                );
                assert_eq!(
                    ours,
                    input[..len],
                    "{path} open, {len} bytes, {aad_len} of AAD"
                );
            }
        }
    }
}
