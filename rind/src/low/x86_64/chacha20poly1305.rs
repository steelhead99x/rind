// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20-Poly1305: aws-lc's `chacha20_poly1305_x86_64`, which interleaves
//! ChaCha20 with Poly1305 in one pass, imported by `admin/import-aws-lc`,
//! with AVX2 where the CPU has it and SSE4.1 otherwise. Without SSE4.1,
//! ChaCha20 and Poly1305 run in separate passes.
//!
//! On a CPU with AVX-512 IFMA, from `IFMA_MIN_LEN` bytes of message, they
//! run in separate passes instead, as OpenSSL runs them there:
//! verified-garbage's AVX-512 VL ChaCha20 and OpenSSL's base 2^44 Poly1305
//! (`poly1305_ifma`), a chunk at a time so the second pass reads what the
//! first left in L1. aws-lc's one pass interleaves a scalar Poly1305, which
//! takes about as long as both vector passes together.
//!
//! The aws-lc assembly is not formally verified: its correctness rests on its
//! use and testing in BoringSSL and aws-lc, and on rind's tests of it against
//! RFC 8439, Wycheproof, aws-lc-rs, and the separate passes.

use super::cpu::{HaveAvx2, HaveAvx512Ifma, HaveSse41};
use super::poly1305_ifma::Poly1305;
use crate::low::chacha20::ChaCha20;
use crate::low::generic::chacha20poly1305 as separate;

/// Encrypts `inout` in place, returning the tag over `aad` and the ciphertext.
pub(crate) fn seal(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    match (HaveAvx512Ifma::check(), HaveSse41::check()) {
        (Some(ifma), _) if inout.len() >= IFMA_MIN_LEN => {
            ifma_passes(ifma, key, nonce, aad, inout, true)
        }
        (_, Some(sse41)) => one_pass(sse41, HaveAvx2::check(), key, nonce, aad, inout, true),
        (_, None) => separate::seal(key, nonce, aad, inout),
    }
}

/// Decrypts `inout` in place, returning the tag over `aad` and the
/// ciphertext, which the caller checks.
pub(crate) fn open(key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], inout: &mut [u8]) -> [u8; 16] {
    match (HaveAvx512Ifma::check(), HaveSse41::check()) {
        (Some(ifma), _) if inout.len() >= IFMA_MIN_LEN => {
            ifma_passes(ifma, key, nonce, aad, inout, false)
        }
        (_, Some(sse41)) => one_pass(sse41, HaveAvx2::check(), key, nonce, aad, inout, false),
        (_, None) => separate::open(key, nonce, aad, inout),
    }
}

/// The shortest message the separate passes take on a CPU with AVX-512
/// IFMA. Below it, the Poly1305 key's powers, the separate key block, and
/// VG taking what follows its eight-block loop one block at a time can cost
/// more than the one pass saves: on an AVX-512 IFMA Xeon, 1350 bytes took
/// 5% longer in separate passes, and 2048 bytes 30% less time.
const IFMA_MIN_LEN: usize = 2048;

/// How much of the message each pass takes before the other: a multiple of
/// VG's eight-block loop, so a TLS record is one chunk, and small enough
/// that the second pass finds the first's output in L1.
const IFMA_CHUNK: usize = 16384;

/// ChaCha20 then Poly1305 for sealing, or Poly1305 then ChaCha20 for opening,
/// a chunk at a time: VG's AVX-512 VL ChaCha20 (`ChaCha20::new` picks it, as
/// the token proves AVX-512 VL) and OpenSSL's IFMA Poly1305.
// Never inlined, holding its `Mcdt` throughout, as `low::mcdt` requires.
#[inline(never)]
fn ifma_passes(
    ifma: HaveAvx512Ifma,
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    inout: &mut [u8],
    seal: bool,
) -> [u8; 16] {
    // `vpmadd52luq` and `vpmadd52huq` multiply the Poly1305 key `r`, its
    // powers, and the accumulator, all secret.
    let _mcdt = crate::low::Mcdt::enter();
    let mut counter_nonce = [0u8; 16];
    counter_nonce[4..].copy_from_slice(nonce);

    // Block 0's first half keys Poly1305.
    let mut chacha = ChaCha20::new(key, &counter_nonce);
    let mut poly_key = [0u8; 32];
    chacha.cipher(&mut poly_key);
    let mut poly = Poly1305::new(ifma, &poly_key);

    // AAD || pad(AAD) || ciphertext || pad(ciphertext) || len_64(AAD) || len_64(ciphertext)
    poly.add_padded(aad);
    let len = inout.len();
    // Every chunk but the last is whole 64-byte blocks, so the counter
    // `cipher` moves on is the next chunk's.
    for chunk in inout.chunks_mut(IFMA_CHUNK) {
        if seal {
            chacha.cipher(chunk);
            poly.add_padded(chunk);
        } else {
            poly.add_padded(chunk);
            chacha.cipher(chunk);
        }
    }
    let mut lengths = [0u8; 16];
    lengths[..8].copy_from_slice(&(aad.len() as u64).to_le_bytes());
    lengths[8..].copy_from_slice(&(len as u64).to_le_bytes());
    poly.add_padded(&lengths);
    poly.finish()
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

    // The CPU's fastest path hides the others from every other test, so each
    // half of the routines the CPU runs, and the IFMA passes at every length,
    // is checked against separate passes directly, under a key
    // `admin/ctgrind` keeps secret: every message length through the AVX2
    // half's 512-byte loop and the tails after it, AAD lengths around
    // aws-lc's 13-byte TLS case and its 16-byte blocks, and long messages
    // across the IFMA passes' chunks.
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
            .chain((0..=48).map(|aad| (300, aad)))
            .chain((0..=48).map(|aad| (IFMA_MIN_LEN + 1, aad)));
        let long = [4095, 4096, 4097, 8191, 8192 + 64, 16384, 16384 + 15];
        for (len, aad_len) in lens.chain(long.map(|len| (len, 13))) {
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
            if let Some(ifma) = HaveAvx512Ifma::check() {
                let mut ours = input[..len].to_vec();
                let ours_tag =
                    ct::into_public(ifma_passes(ifma, &key, &nonce, aad, &mut ours, true));
                ct::public_slice(&ours);
                assert_eq!(
                    ours_tag, tag,
                    "ifma seal tag, {len} bytes, {aad_len} of AAD"
                );
                assert_eq!(ours, sealed, "ifma seal, {len} bytes, {aad_len} of AAD");
                let ours_tag =
                    ct::into_public(ifma_passes(ifma, &key, &nonce, aad, &mut ours, false));
                ct::public_slice(&ours);
                assert_eq!(
                    ours_tag, tag,
                    "ifma open tag, {len} bytes, {aad_len} of AAD"
                );
                assert_eq!(
                    ours,
                    input[..len],
                    "ifma open, {len} bytes, {aad_len} of AAD"
                );
            }
        }
    }

    // valgrind cannot run AVX-512, so `admin/ct-sde` checks the IFMA passes:
    // the key and the message are secret, and their lengths public. The
    // message runs past one chunk into a second whose last block is partial,
    // after AAD whose last block is too, sealed and then opened.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_chacha20_poly1305_ifma_passes() {
        let mut rng = Rng(ct_sde::seed());
        let ifma = HaveAvx512Ifma::check().expect("AVX-512 IFMA");
        let key: [u8; 32] = core::array::from_fn(|_| rng.next() as u8);
        let nonce: [u8; 12] = core::array::from_fn(|_| rng.next() as u8);
        let aad: Vec<u8> = (0..29).map(|_| rng.next() as u8).collect();
        let mut msg: Vec<u8> = (0..IFMA_CHUNK + 512 + 64 + 9)
            .map(|_| rng.next() as u8)
            .collect();
        ct_sde::traced(|| {
            ifma_passes(ifma, &key, &nonce, &aad, &mut msg, true);
            ifma_passes(ifma, &key, &nonce, &aad, &mut msg, false)
        });
    }
}
