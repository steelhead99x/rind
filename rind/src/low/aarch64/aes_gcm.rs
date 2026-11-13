// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::arch::aarch64::*;
use core::mem;

use super::aes::HwKey;
use super::aes128_gcm_dec::aes128_gcm_dec;
use super::aes128_gcm_dec_alt::aes128_gcm_dec_alt;
use super::aes128_gcm_enc::aes128_gcm_enc;
use super::aes128_gcm_enc_alt::aes128_gcm_enc_alt;
use super::aes256_gcm_dec::aes256_gcm_dec;
use super::aes256_gcm_dec_alt::aes256_gcm_dec_alt;
use super::aes256_gcm_enc::aes256_gcm_enc;
use super::aes256_gcm_enc_alt::aes256_gcm_enc_alt;
use super::ghash::{Aggregate, PmullTable};
use crate::low::ghash::{Ghash, GhashTable};
use crate::low::{AesKey, aes_ctr, ct_equal};

/// Encrypts `cipher_inout` in place under `nonce`, and returns its tag.
pub(crate) fn seal(
    key: &AesKey,
    table: &GhashTable,
    nonce: &[u8; 12],
    aad: &[u8],
    cipher_inout: &mut [u8],
) -> [u8; 16] {
    tagged::<true>(key, table, nonce, aad, cipher_inout)
}

/// Decrypts `cipher_inout` in place under `nonce`, and returns whether `tag`
/// is its tag, a secret.
pub(crate) fn open(
    key: &AesKey,
    table: &GhashTable,
    nonce: &[u8; 12],
    aad: &[u8],
    cipher_inout: &mut [u8],
    tag: &[u8; 16],
) -> bool {
    ct_equal(&tagged::<false>(key, table, nonce, aad, cipher_inout), tag)
}

fn tagged<const ENC: bool>(
    key: &AesKey,
    table: &GhashTable,
    nonce: &[u8; 12],
    aad: &[u8],
    cipher_inout: &mut [u8],
) -> [u8; 16] {
    tagged_from::<ENC>(key, table, counter_block(nonce), aad, cipher_inout)
}

/// GCM's first counter block for a 96-bit nonce: the nonce, then 1.
fn counter_block(nonce: &[u8; 12]) -> [u8; 16] {
    let mut y0 = [0u8; 16];
    y0[..12].copy_from_slice(nonce);
    y0[15] = 0x01;
    y0
}

/// GCM's first counter block for `iv`, of any length but zero: the 96-bit
/// nonce's, or else the GHASH of `iv` and its bit length.
pub(crate) fn initial_counter(table: &GhashTable, iv: &[u8]) -> [u8; 16] {
    if let Ok(nonce) = iv.try_into() {
        return counter_block(nonce);
    }
    let mut ghash = Ghash::new(table);
    ghash.add(iv);
    ghash.add(&lengths(0, iv.len()));
    ghash.into_bytes()
}

/// GCM's last GHASH block: the bit lengths of the AAD and the message.
fn lengths(aad: usize, msg: usize) -> [u8; 16] {
    (((aad as u128 * 8) << 64) | (msg as u128 * 8)).to_be_bytes()
}

/// Encrypts (if `ENC`) or decrypts `cipher_inout` in place from the counter
/// block `y0`, and returns its tag.
///
/// Inlined, as is `cipher`, so `tagged` compiles as when it was the only
/// caller.
#[inline(always)]
pub(crate) fn tagged_from<const ENC: bool>(
    key: &AesKey,
    table: &GhashTable,
    y0: [u8; 16],
    aad: &[u8],
    cipher_inout: &mut [u8],
) -> [u8; 16] {
    let short_blocks = if ENC {
        SHORT_SEAL_BLOCKS
    } else {
        SHORT_OPEN_BLOCKS
    };
    if let (AesKey::Hw(key), GhashTable::Pmull(table)) = (key, table)
        && aad.len().div_ceil(16) + cipher_inout.len().div_ceil(16) <= short_blocks
    {
        // SAFETY: only a `HaveCryptoExt` token builds a `HwKey`, proving the
        // `aes` cpu feature.
        return unsafe {
            match key {
                HwKey::Aes128(k) => short::<ENC, 11>(k.round_keys(), table, y0, aad, cipher_inout),
                HwKey::Aes192(k) => short::<ENC, 13>(k.round_keys(), table, y0, aad, cipher_inout),
                HwKey::Aes256(k) => short::<ENC, 15>(k.round_keys(), table, y0, aad, cipher_inout),
            }
        };
    }

    let mut ghash = Ghash::new(table);
    cipher::<ENC>(key, &mut ghash, &y0, aad, cipher_inout);
    ghash.add(&lengths(aad.len(), cipher_inout.len()));

    let mut tag = key.encrypt_block(&y0);
    for (t, x) in tag.iter_mut().zip(ghash.into_bytes()) {
        *t ^= x;
    }
    tag
}

/// The most AAD and message blocks [`short`] seals and opens, past which the
/// stitched kernels were faster on Neoverse N2. With the lengths block, each
/// fills whole groups of eight. Sealing stops sooner, as it hashes each block
/// only once its AES is done.
const SHORT_SEAL_BLOCKS: usize = 15;
const SHORT_OPEN_BLOCKS: usize = 31;

/// Encrypts (if `ENC`) or decrypts a short message in one pass, and returns
/// its tag: its counter blocks and `y0` encrypt together, and one GHASH
/// reduction per eight blocks hashes the AAD, the message, and the lengths
/// block, where the kernels' path hashes each of them in a separate call.
///
/// Cortex-A78 issues two AES instructions a cycle and fuses an adjacent
/// `AESE`/`AESMC` pair that shares a register, so the counters go out up to
/// four at a time. One block at a time leaves the second pipeline idle,
/// which is most of a 32-byte seal: the tag mask and two message blocks.
#[target_feature(enable = "aes")]
fn short<const ENC: bool, const ROUND_KEYS: usize>(
    round_keys: &[uint8x16_t; ROUND_KEYS],
    table: &PmullTable,
    y0: [u8; 16],
    aad: &[u8],
    cipher_inout: &mut [u8],
) -> [u8; 16] {
    let blocks = aad.len().div_ceil(16) + cipher_inout.len().div_ceil(16) + 1;
    let mut ghash = Aggregate::new(table, blocks);

    let y0_block = load(&y0);
    for chunk in aad.chunks(16) {
        ghash.add(load(chunk));
    }

    let y0_ctr = u32::from_be_bytes([y0[12], y0[13], y0[14], y0[15]]);
    let y0_words = vreinterpretq_u32_u8(y0_block);
    let msg_len = cipher_inout.len();
    let mut index = 1u32;
    let mut rest = cipher_inout;
    let mut tag_mask = y0_block;
    let mut tag_left = true;
    loop {
        let data_blocks = rest.len().div_ceil(16);
        if data_blocks == 0 {
            if tag_left {
                let mut block = [y0_block];
                encrypt_lanes(round_keys, &mut block);
                tag_mask = block[0];
            }
            break;
        }
        // The tag mask takes a free lane of a short group. A full group of
        // four message blocks keeps every lane, and the mask joins the tail.
        // `TAG` is const so each arm's counters and block loop unroll.
        if tag_left && data_blocks < 4 {
            let n = data_blocks;
            let take = rest.len().min(n * 16);
            let (chunk, tail) = rest.split_at_mut(take);
            rest = tail;
            tag_mask = match n {
                1 => crypt_batch::<ENC, ROUND_KEYS, 2, true>(
                    round_keys, &mut ghash, y0_block, y0_words, y0_ctr, index, chunk,
                ),
                2 => crypt_batch::<ENC, ROUND_KEYS, 3, true>(
                    round_keys, &mut ghash, y0_block, y0_words, y0_ctr, index, chunk,
                ),
                _ => crypt_batch::<ENC, ROUND_KEYS, 4, true>(
                    round_keys, &mut ghash, y0_block, y0_words, y0_ctr, index, chunk,
                ),
            };
            tag_left = false;
            index += n as u32;
        } else {
            let n = data_blocks.min(4);
            let take = rest.len().min(n * 16);
            let (chunk, tail) = rest.split_at_mut(take);
            rest = tail;
            match n {
                1 => crypt_batch::<ENC, ROUND_KEYS, 1, false>(
                    round_keys, &mut ghash, y0_block, y0_words, y0_ctr, index, chunk,
                ),
                2 => crypt_batch::<ENC, ROUND_KEYS, 2, false>(
                    round_keys, &mut ghash, y0_block, y0_words, y0_ctr, index, chunk,
                ),
                3 => crypt_batch::<ENC, ROUND_KEYS, 3, false>(
                    round_keys, &mut ghash, y0_block, y0_words, y0_ctr, index, chunk,
                ),
                _ => crypt_batch::<ENC, ROUND_KEYS, 4, false>(
                    round_keys, &mut ghash, y0_block, y0_words, y0_ctr, index, chunk,
                ),
            };
            index += n as u32;
        }
    }
    ghash.add(load(&lengths(aad.len(), msg_len)));

    let mut tag = [0u8; 16];
    store(&mut tag, veorq_u8(tag_mask, ghash.finish()));
    tag
}

/// Encrypts the tag mask (when `TAG`) and `data`'s counter blocks, `N` of
/// them together, then folds `data` into `ghash`. Returns the tag mask when
/// `TAG`, and an unused lane otherwise.
#[target_feature(enable = "aes")]
#[inline]
fn crypt_batch<const ENC: bool, const KEYS: usize, const N: usize, const TAG: bool>(
    round_keys: &[uint8x16_t; KEYS],
    ghash: &mut Aggregate<'_>,
    y0_block: uint8x16_t,
    y0_words: uint32x4_t,
    y0_ctr: u32,
    index: u32,
    data: &mut [u8],
) -> uint8x16_t {
    let mut counters = [y0_block; N];
    let start = usize::from(TAG);
    let mut ctr = index;
    for counter in &mut counters[start..] {
        *counter = gcm_counter(y0_words, y0_ctr, ctr);
        ctr = ctr.wrapping_add(1);
    }
    encrypt_lanes(round_keys, &mut counters);

    let (blocks, rest) = data.as_chunks_mut::<16>();
    let mut streams = counters[start..].iter().copied();
    for (chunk, keystream) in blocks.iter_mut().zip(streams.by_ref()) {
        apply_block::<ENC>(ghash, chunk, keystream);
    }
    if !rest.is_empty() {
        // `N - start` is the block count, so a short tail has a lane.
        let Some(keystream) = streams.next() else {
            unreachable!()
        };
        apply_block::<ENC>(ghash, rest, keystream);
    }
    counters[0]
}

/// Xors one counter block into `chunk` and folds the ciphertext into `ghash`.
#[target_feature(enable = "aes")]
#[inline]
fn apply_block<const ENC: bool>(
    ghash: &mut Aggregate<'_>,
    chunk: &mut [u8],
    keystream: uint8x16_t,
) {
    let input = load(chunk);
    if !ENC {
        ghash.add(input);
    }
    let output = veorq_u8(input, keystream);
    store(chunk, output);
    if ENC {
        // The keystream past a short chunk is no ciphertext.
        let width = chunk.len();
        let block = if width == 16 {
            output
        } else {
            vandq_u8(output, load(&KEEP[16 - width..][..16]))
        };
        ghash.add(block);
    }
}

/// The counter block `i` after `y0`, GCM's big-endian increment of its last word.
#[target_feature(enable = "neon")]
#[inline]
fn gcm_counter(y0_words: uint32x4_t, y0_ctr: u32, i: u32) -> uint8x16_t {
    vreinterpretq_u8_u32(vsetq_lane_u32::<3>(
        y0_ctr.wrapping_add(i).to_be(),
        y0_words,
    ))
}

/// AES of `N` independent blocks under any key size.
///
/// Each round is an `AESE`/`AESMC` pair per block before the next round, the
/// shape Cortex-A78 fuses and dual-issues. `N` is 1, 2, 3, or 4.
///
/// Out of line so the round keys and the lanes get the register file to
/// themselves. Inlined into [`short`], the live GHASH state made LLVM spill
/// the lanes to the stack between rounds.
#[target_feature(enable = "aes")]
#[inline(never)]
fn encrypt_lanes<const KEYS: usize, const N: usize>(
    round_keys: &[uint8x16_t; KEYS],
    block: &mut [uint8x16_t; N],
) {
    // A local copy, so the rounds stay in registers. Writing each round
    // through `block` reloads it.
    let mut lanes = *block;
    let [rounds @ .., penultimate, last] = round_keys.as_slice() else {
        unreachable!()
    };
    let penultimate = *penultimate;
    let last = *last;
    for rk in rounds {
        let rk = *rk;
        for lane in &mut lanes {
            *lane = vaesmcq_u8(vaeseq_u8(*lane, rk));
        }
    }
    for lane in &mut lanes {
        *lane = veorq_u8(vaeseq_u8(*lane, penultimate), last);
    }
    *block = lanes;
}

/// Sixteen ones then sixteen zeros: the 16 bytes from `16 - n` keep the
/// first `n` bytes of a block.
static KEEP: [u8; 32] = {
    let mut keep = [0; 32];
    let mut i = 0;
    while i < 16 {
        keep[i] = 0xff;
        i += 1;
    }
    keep
};

/// Loads up to 16 bytes, zero-padded.
#[target_feature(enable = "neon")]
#[inline]
fn load(bytes: &[u8]) -> uint8x16_t {
    if let Ok(block) = <&[u8; 16]>::try_from(bytes) {
        // SAFETY: `block` is 16 readable bytes.
        return unsafe { vld1q_u8(block.as_ptr()) };
    }

    // A shorter one in at most four moves through general registers, as a
    // `memcpy` call would spill every vector register, and its bytes stored
    // to the stack would not forward to one vector load.
    let mut word = 0u128;
    let mut at = 0;
    for size in [8, 4, 2, 1] {
        if bytes.len() & size != 0 {
            let mut part = [0u8; 8];
            part[..size].copy_from_slice(&bytes[at..at + size]);
            word |= u128::from(u64::from_le_bytes(part)) << (8 * at);
            at += size;
        }
    }
    // SAFETY: u128 and uint8x16_t have the same size, and both are little
    // endian.
    unsafe { mem::transmute(word) }
}

/// Stores the first `bytes.len()` bytes of `block`, up to 16.
#[target_feature(enable = "neon")]
#[inline]
fn store(bytes: &mut [u8], block: uint8x16_t) {
    if let Ok(out) = <&mut [u8; 16]>::try_from(&mut *bytes) {
        // SAFETY: `out` is 16 writable bytes.
        return unsafe { vst1q_u8(out.as_mut_ptr(), block) };
    }

    // SAFETY: as in `load`.
    let word: u128 = unsafe { mem::transmute(block) };
    let mut at = 0;
    for size in [8, 4, 2, 1] {
        if bytes.len() & size != 0 {
            let part = ((word >> (8 * at)) as u64).to_le_bytes();
            bytes[at..at + size].copy_from_slice(&part[..size]);
            at += size;
        }
    }
}

// AES-GCM encrypt (if `ENC` is `true`) or decrypt.
#[inline(always)]
fn cipher<const ENC: bool>(
    key: &AesKey,
    ghash: &mut Ghash<'_>,
    initial_counter: &[u8; 16],
    aad: &[u8],
    cipher_inout: &mut [u8],
) {
    ghash.add(aad);

    let mut counter = *initial_counter;
    inc32(&mut counter);

    // s2n-bignum's stitched kernels take AES-128 and AES-256 keys, and
    // aws-lc's AES-192 one needs SHA3.
    let (AesKey::Hw(hw_key), GhashTable::Pmull(table)) = (key, ghash.table) else {
        return composed::<ENC>(key, ghash, &counter, cipher_inout);
    };
    if let (HwKey::Aes192(_), None) = (hw_key, table.eight_way) {
        return composed::<ENC>(key, ghash, &counter, cipher_inout);
    }

    let (blocks, remainder) = cipher_inout.as_chunks_mut::<16>();

    if !blocks.is_empty() {
        let mut tag = ghash.state();
        let htable = &table.htable;
        let [htable4 @ .., _, _, _, _, _, _] = htable;
        let (inout, len) = (blocks.as_mut_ptr(), blocks.len());
        // SAFETY: only a `HaveCryptoExt` token builds a `HwKey`, proving the
        // `aes` cpu feature, `eight_way` proves `sha3`, and `inout` is valid
        // for reads and writes of `len` blocks. s2n-bignum's kernels' proofs
        // assume the input and output do not overlap, but every path through
        // them loads each input block before storing its output block and
        // never reads an output back, so in place they compute the same, as
        // `admin/parse-asm/inplace.py` checks. aws-lc runs its AES-192
        // routines in place too.
        unsafe {
            match (hw_key, ENC, table.eight_way) {
                (HwKey::Aes128(k), true, None) => {
                    aes128_gcm_enc(inout, len, &mut tag, &mut counter, k.round_keys(), htable4)
                }
                (HwKey::Aes128(k), false, None) => {
                    aes128_gcm_dec(inout, len, &mut tag, &mut counter, k.round_keys(), htable4)
                }
                (HwKey::Aes128(k), true, Some(_)) => {
                    aes128_gcm_enc_alt(inout, len, &mut tag, &mut counter, k.round_keys(), htable)
                }
                (HwKey::Aes128(k), false, Some(_)) => {
                    aes128_gcm_dec_alt(inout, len, &mut tag, &mut counter, k.round_keys(), htable)
                }
                (HwKey::Aes256(k), true, None) => {
                    aes256_gcm_enc(inout, len, &mut tag, &mut counter, k.round_keys(), htable4)
                }
                (HwKey::Aes256(k), false, None) => {
                    aes256_gcm_dec(inout, len, &mut tag, &mut counter, k.round_keys(), htable4)
                }
                (HwKey::Aes256(k), true, Some(_)) => {
                    aes256_gcm_enc_alt(inout, len, &mut tag, &mut counter, k.round_keys(), htable)
                }
                (HwKey::Aes256(k), false, Some(_)) => {
                    aes256_gcm_dec_alt(inout, len, &mut tag, &mut counter, k.round_keys(), htable)
                }
                (HwKey::Aes192(k), true, Some(_)) => {
                    let (key, ivec, xi) = (k.round_keys(), &mut counter, &mut tag);
                    asm_call!(unsafe extern "C" aesv8_gcm_8x_enc_192(inout, len * 128, inout, xi, ivec, key, htable));
                }
                (HwKey::Aes192(k), false, Some(_)) => {
                    let (key, ivec, xi) = (k.round_keys(), &mut counter, &mut tag);
                    asm_call!(unsafe extern "C" aesv8_gcm_8x_dec_192(inout, len * 128, inout, xi, ivec, key, htable));
                }
                (HwKey::Aes192(_), _, None) => unreachable!("composed above"),
            }
        }

        ghash.set_state(tag);
    }

    if !remainder.is_empty() {
        if !ENC {
            ghash.add(remainder);
        }

        for (c, k) in remainder.iter_mut().zip(key.encrypt_block(&counter)) {
            *c ^= k;
        }

        if ENC {
            ghash.add(remainder);
        }
    }
}

/// Defines a naked function running aws-lc's stitched AES-192-GCM, imported
/// by `admin/import-aws-lc`: from the counter block `ivec`, it encrypts or
/// decrypts the `bits / 8` bytes at `input` into `output`, hashes the
/// ciphertext into `xi`, the running GHASH in `Ghash::state`'s byte order,
/// and advances `ivec` past them. `bits` is a whole number of blocks.
///
/// The aws-lc assembly is not formally verified: its correctness rests on
/// its use and testing in OpenSSL and aws-lc, and on rind's tests of it
/// against vpaes and NEON GHASH, Wycheproof, and aws-lc-rs.
macro_rules! gcm_8x {
    ($name:ident) => {
        #[unsafe(naked)]
        unsafe extern "C" fn $name(
            input: *const [u8; 16],
            bits: usize,
            output: *mut [u8; 16],
            xi: &mut [u8; 16],
            ivec: &mut [u8; 16],
            round_keys: &[uint8x16_t; 13],
            htable: &[uint64x2_t; 12],
        ) -> usize {
            // A naked function can't enable a target feature, so the
            // assembler is told of `aes` here. The extension stays on for
            // the assembly after it, which it only lets assemble more.
            #[cfg(not(target_vendor = "apple"))]
            core::arch::naked_asm!(
                ".arch_extension aes",
                include_str!(concat!("aws_lc/", stringify!($name), ".linux.s"))
            );
            #[cfg(target_vendor = "apple")]
            core::arch::naked_asm!(
                ".arch_extension aes",
                include_str!(concat!("aws_lc/", stringify!($name), ".apple.s"))
            );
        }
    };
}

gcm_8x!(aesv8_gcm_8x_enc_192);
gcm_8x!(aesv8_gcm_8x_dec_192);

/// AES-CTR and GHASH in separate passes over each eight blocks, for keys
/// without the stitched kernels, as aws-lc composes vpaes and NEON GHASH.
fn composed<const ENC: bool>(
    key: &AesKey,
    ghash: &mut Ghash<'_>,
    counter: &[u8; 16],
    cipher_inout: &mut [u8],
) {
    let (nonce, ctr) = counter.split_at(12);
    let nonce = nonce.try_into().unwrap();
    let mut ctr = u32::from_be_bytes(ctr.try_into().unwrap());

    let (chunks, remainder) = cipher_inout.as_chunks_mut::<128>();
    for chunk in chunks {
        if !ENC {
            ghash.add(chunk);
        }
        aes_ctr::apply(key, nonce, ctr, chunk);
        if ENC {
            ghash.add(chunk);
        }
        ctr = ctr.wrapping_add(8);
    }

    if !ENC {
        ghash.add(remainder);
    }
    aes_ctr::apply(key, nonce, ctr, remainder);
    if ENC {
        ghash.add(remainder);
    }
}

/// Increments the big-endian 32-bit counter in the last four bytes of `block`.
fn inc32(block: &mut [u8; 16]) {
    let b = u128::from_be_bytes(*block);
    let ctr = (b as u32).wrapping_add(1);
    *block = (b & !0xffff_ffff | ctr as u128).to_be_bytes();
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::aarch64::cpu::HaveCryptoExt;
    use crate::low::aarch64::ghash::PmullTable;
    use crate::low::aarch64::ghash_neon_armv8::NeonTable;
    use crate::low::aarch64::vpaes_armv8::VpaesKey;
    use crate::low::ct;
    use crate::low::generic::ghash::gcm_model;

    // Every other test sees only the path the CPU picks, so the stitched
    // kernels and the one-pass short path are checked against vpaes and NEON
    // GHASH here, under a key `admin/ctgrind` keeps secret: each key size,
    // and AAD and message lengths around the block, eight-block, and short
    // path's boundaries, with AAD long enough that the kernels take a single
    // block, both ways, with a tag wrong in either half.
    #[test]
    fn kernels_match_composed() {
        let Some(token) = HaveCryptoExt::check() else {
            return;
        };
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for key_len in [16, 24, 32] {
            let key = bytes(key_len, 1);
            ct::secret_slice(&key);
            let hw = AesKey::new(&key);
            let vpaes = AesKey::Vpaes(VpaesKey::new(&key));
            let h = vpaes.encrypt_block(&[0; 16]);
            let pmull = GhashTable::Pmull(PmullTable::new(u128::from_be_bytes(h), token));
            let neon = GhashTable::Neon(NeonTable::new(&h));

            for aad_len in [0, 1, 13, 16, 17, 32, 33, 112, 400] {
                for msg_len in [
                    0, 1, 3, 15, 16, 17, 35, 64, 80, 81, 95, 96, 97, 112, 113, 127, 128, 129, 224,
                    225, 240, 255, 256, 480, 481, 496, 1000,
                ] {
                    let nonce = bytes(12, msg_len as u32).try_into().unwrap();
                    let aad = bytes(aad_len, 2);
                    let plain = bytes(msg_len, 3);
                    let what = format!("{key_len} {aad_len} {msg_len}");

                    let mut want = plain.clone();
                    let want_tag = ct::into_public(seal(&vpaes, &neon, &nonce, &aad, &mut want));
                    ct::public_slice(&want);
                    let mut got = plain.clone();
                    let tag = ct::into_public(seal(&hw, &pmull, &nonce, &aad, &mut got));
                    ct::public_slice(&got);
                    assert_eq!(got, want, "{what}");
                    assert_eq!(tag, want_tag, "{what}");

                    let valid = open(&hw, &pmull, &nonce, &aad, &mut got, &want_tag);
                    ct::public_slice(&got);
                    assert!(ct::into_public(valid), "{what}");
                    assert_eq!(got, plain, "{what}");

                    for byte in [0, 15] {
                        let mut wrong = want_tag;
                        wrong[byte] ^= 1;
                        let mut got = want.clone();
                        let valid = open(&hw, &pmull, &nonce, &aad, &mut got, &wrong);
                        assert!(!ct::into_public(valid), "{what}, byte {byte}");
                    }
                }
            }
        }
    }

    // Valgrind hides SHA3, so `admin/ctgrind` never reaches the eight-way
    // kernels; `admin/ct-qemu` traces them here instead, under qemu-aarch64's
    // `max` CPU: key and GHASH table setup, then each key size both ways with
    // a secret key, nonce or IV, AAD, and message, at lengths that take the
    // one-pass short path, and the kernels' eight-block loop with tails of
    // seven blocks and a partial one, five blocks, and eight.
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_aes_gcm() {
        use crate::low::aarch64::ct_qemu;

        let seed = ct_qemu::seed().to_le_bytes();
        let bytes = |n| seed.iter().cycle().take(n).copied().collect::<Vec<u8>>();
        let token = HaveCryptoExt::check().expect("the crypto extension");
        for key_len in [16, 24, 32] {
            let key = bytes(key_len);
            let (key, table) = ct_qemu::traced(|| {
                let key = AesKey::new(&key);
                let h = key.encrypt_block(&[0; 16]);
                (key, PmullTable::new(u128::from_be_bytes(h), token))
            });
            assert!(matches!(key, AesKey::Hw(_)), "the crypto extension");
            assert!(table.eight_way.is_some(), "SHA3");
            let table = GhashTable::Pmull(table);

            let nonce = bytes(12).try_into().unwrap();
            let iv = bytes(17);
            for (aad_len, msg_len) in [
                (13, 100),
                (300, 128 * 3 + 16 * 7 + 5),
                (0, 128 * 2 + 16 * 5),
                (13, 1024),
            ] {
                let aad = bytes(aad_len);
                let mut msg = bytes(msg_len);
                let tag = ct_qemu::traced(|| seal(&key, &table, &nonce, &aad, &mut msg));
                ct_qemu::traced(|| open(&key, &table, &nonce, &aad, &mut msg, &tag));

                // An IV other than 96 bits, which hashes to a secret counter
                // block.
                ct_qemu::traced(|| {
                    let y0 = initial_counter(&table, &iv);
                    tagged_from::<true>(&key, &table, y0, &aad, &mut msg)
                });
            }
        }
    }

    // An IV other than 96 bits hashes to a counter block whose 32-bit
    // counter may wrap within one message, as GCM's increment does mod 2^32
    // without carrying into the rest of the block: on both paths, at lengths
    // that wrap within the short path, the kernels' eight- and four-block
    // loops, and their tails, or not at all.
    #[test]
    fn counter_wraps() {
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for key_len in [16, 24, 32] {
            let key = bytes(key_len, 1);
            let vpaes = AesKey::Vpaes(VpaesKey::new(&key));
            let h = vpaes.encrypt_block(&[0; 16]);
            let mut paths = vec![(vpaes, GhashTable::Neon(NeonTable::new(&h)))];
            if let Some(token) = HaveCryptoExt::check() {
                let pmull = PmullTable::new(u128::from_be_bytes(h), token);
                paths.push((AesKey::new(&key), GhashTable::Pmull(pmull)));
            }

            for (key, table) in &paths {
                for start in [0xffff_ffffu32, 0xffff_fffe, 0xffff_fff9, 0xffff_ff00, 7] {
                    for msg_len in [3, 16, 17, 48, 100, 128, 200, 300, 1000] {
                        let mut y0: [u8; 16] = bytes(16, msg_len as u32).try_into().unwrap();
                        y0[12..].copy_from_slice(&start.to_be_bytes());
                        let aad = bytes(17, 2);
                        let plain = bytes(msg_len, 3);
                        let what = format!("{key_len} {start:x} {msg_len}");
                        let (want, want_tag) =
                            gcm_model(|b| key.encrypt_block(b), &y0, &aad, &plain);

                        let mut got = plain.clone();
                        let tag = tagged_from::<true>(key, table, y0, &aad, &mut got);
                        assert_eq!((&got, tag), (&want, want_tag), "{what}");

                        let tag = tagged_from::<false>(key, table, y0, &aad, &mut got);
                        assert_eq!((&got, tag), (&plain, want_tag), "{what}");
                    }
                }
            }
        }
    }
}
