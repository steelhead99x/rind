// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//
//! Ref. <https://www.intel.com/content/dam/www/public/us/en/documents/white-papers/communications-ia-cryptographic-paper.pdf>

use core::arch::x86_64::*;
use core::mem;

use super::aes::{AesKey, HwKey};
use super::aes_ctr;
use super::aes_gcm_avx::AvxKernel;
use super::aes_gcm_vg::VgKey;
use super::cpu::HaveAvx512ForAesGcm;
use super::ghash::{self, ClmulTable, Ghash, GhashTable, GhashTableAvx512};
use crate::low::ct_equal;

/// Encrypts `cipher_inout` in place under `nonce`, and returns its tag.
pub(crate) fn seal(
    key: &AesKey,
    table: &GhashTable,
    nonce: &[u8; 12],
    aad: &[u8],
    cipher_inout: &mut [u8],
) -> [u8; 16] {
    if let Some((hw_key, kernel)) = vale::<true>(key, table, aad, cipher_inout) {
        return kernel.seal(hw_key, nonce, aad, cipher_inout);
    }
    if let Some(vg) = vg(key, table, cipher_inout.len()) {
        return vg.seal(nonce, aad, cipher_inout);
    }
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
    if let Some((hw_key, kernel)) = vale::<false>(key, table, aad, cipher_inout) {
        return kernel.open(hw_key, nonce, aad, cipher_inout, tag);
    }
    if let Some(vg) = vg(key, table, cipher_inout.len()) {
        return vg.open(nonce, aad, cipher_inout, tag);
    }
    ct_equal(&tagged::<false>(key, table, nonce, aad, cipher_inout), tag)
}

/// Vale's AES-GCM, where the CPU runs it, it has a routine for the key size,
/// its proof covers the lengths, and it is the fastest path to encrypt (if
/// `ENC`) or decrypt the message.
fn vale<'a, const ENC: bool>(
    key: &'a AesKey,
    table: &'a GhashTable,
    aad: &[u8],
    cipher_inout: &[u8],
) -> Option<(&'a HwKey, &'a AvxKernel)> {
    let len = cipher_inout.len();
    if !(u32::try_from(aad.len()).is_ok() && u32::try_from(len).is_ok())
        || matches!(key, AesKey::Hw(HwKey::Aes192(_)))
    {
        return None;
    }
    let (avx_from, vaes_avx2_below) = if ENC {
        (AVX_VALE_SEAL_FROM, VAES_AVX2_VALE_SEAL_BELOW)
    } else {
        (0, VAES_AVX2_VALE_OPEN_BELOW)
    };
    match (key, table) {
        (AesKey::Hw(hw_key), GhashTable::Avx(_, kernel)) if len >= avx_from => {
            Some((hw_key, kernel))
        }
        (AesKey::Hw(hw_key), GhashTable::VaesAvx2(.., kernel)) if len < vaes_avx2_below => {
            Some((hw_key, kernel))
        }
        _ => None,
    }
}

/// pyca/verified-garbage's AES-GCM, where the CPU is one it is faster on
/// and the message is long enough, with its key context, made on the first
/// such message.
fn vg<'a>(key: &'a AesKey, table: &'a GhashTable, len: usize) -> Option<&'a VgKey> {
    match (key, table) {
        (AesKey::Hw(hw_key), GhashTable::Avx512(GhashTableAvx512 { vg: Some(vg), .. }))
            if len >= VG_FROM =>
        {
            Some(vg.get(hw_key))
        }
        _ => None,
    }
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

/// GCM's first counter block for `iv`, of any length but zero: the 96-bit
/// nonce's, or else the GHASH of `iv` and its bit length.
pub(crate) fn initial_counter(table: &GhashTable, iv: &[u8]) -> [u8; 16] {
    if let Ok(nonce) = iv.try_into() {
        return counter_block(nonce);
    }
    let mut ghash = Ghash::new(table);
    ghash.add(iv);
    ghash.add_lengths(0, iv.len());
    ghash.tag(&[0; 16])
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
    let mut ghash = Ghash::new(table);
    cipher::<ENC>(key, &mut ghash, &y0, aad, cipher_inout);
    ghash.add_lengths(aad.len(), cipher_inout.len());

    // Last, so its AES overlaps the GHASH before it.
    ghash.tag(&key.encrypt_block(&y0))
}

/// GCM's first counter block for a 96-bit nonce: the nonce, then 1.
fn counter_block(nonce: &[u8; 12]) -> [u8; 16] {
    let lo = u64::from_le_bytes(nonce[..8].try_into().unwrap());
    let hi = u64::from(u32::from_le_bytes(nonce[8..].try_into().unwrap())) | 1 << 56;
    let mut y0 = [0u8; 16];
    // SAFETY: every x86_64 CPU has SSE2, and `y0` is 16 writable bytes. One
    // vector store, so the 16-byte loads that read it are forwarded, where
    // separate stores of its parts would stall them.
    unsafe { _mm_storeu_si128(y0.as_mut_ptr().cast(), _mm_set_epi64x(hi as i64, lo as i64)) };
    y0
}

// AES-GCM encrypt (if `ENC` is `true`) or decrypt, on the fastest path for
// the CPU the key and GHASH table were made on and the message's length.
#[inline(always)]
fn cipher<const ENC: bool>(
    key: &AesKey,
    ghash: &mut Ghash<'_>,
    initial_counter: &[u8; 16],
    aad: &[u8],
    cipher_inout: &mut [u8],
) {
    let len = cipher_inout.len();
    let AesKey::Hw(hw_key) = key else {
        return composed::<ENC>(key, ghash, initial_counter, aad, cipher_inout);
    };
    let table = match ghash.table {
        GhashTable::Avx512(GhashTableAvx512 { vaes, .. })
            if len >= AVX512_KERNEL_MINIMUM_CIPHER_LEN =>
        {
            ghash.add(aad);
            return vaes.cipher::<ENC>(hw_key, initial_counter, ghash, cipher_inout);
        }
        GhashTable::Avx512(GhashTableAvx512 { token, .. }) if len >= AVX512_MINIMUM_CIPHER_LEN => {
            // SAFETY: only a `HaveAesHardware` token builds `hw_key`, and
            // `token` proves the remaining features were dynamically checked
            return unsafe {
                _cipher_avx512::<ENC>(hw_key, ghash, initial_counter, aad, cipher_inout, *token)
            };
        }
        GhashTable::VaesAvx2(_, vaes, _) if len >= VAES_AVX2_MINIMUM_CIPHER_LEN => {
            ghash.add(aad);
            return vaes.cipher::<ENC>(hw_key, initial_counter, ghash, cipher_inout);
        }
        GhashTable::Clmul(table)
        | GhashTable::VaesAvx2(table, ..)
        | GhashTable::Avx(table, _)
        | GhashTable::Avx512(GhashTableAvx512 { clmul: table, .. }) => table,
        GhashTable::Ssse3(_) | GhashTable::Nohw(_) => {
            return composed::<ENC>(key, ghash, initial_counter, aad, cipher_inout);
        }
    };
    // SAFETY: only a `HaveAesHardware` token builds `hw_key` and `table`,
    // proving AES-NI, PCLMULQDQ, and SSSE3.
    unsafe { by8::<ENC>(hw_key, table, ghash, initial_counter, aad, cipher_inout) }
}

/// AES-CTR and GHASH in separate passes, for a key without AES-NI, as aws-lc
/// composes vpaes and SSSE3 GHASH, or its SSE2 AES and integer GHASH: they
/// take turns over 3 KB at a time, as aws-lc's `GHASH_CHUNK`, which stays in
/// L1 and spreads each routine's setup.
fn composed<const ENC: bool>(
    key: &AesKey,
    ghash: &mut Ghash<'_>,
    initial_counter: &[u8; 16],
    aad: &[u8],
    cipher_inout: &mut [u8],
) {
    ghash.add(aad);

    let (nonce, ctr) = initial_counter.split_at(12);
    let nonce = nonce.try_into().unwrap();
    // The first counter block encrypts the tag.
    let mut ctr = u32::from_be_bytes(ctr.try_into().unwrap()).wrapping_add(1);

    let (chunks, remainder) = cipher_inout.as_chunks_mut::<128>();
    for group in chunks.chunks_mut(24) {
        if !ENC {
            ghash.add(group.as_flattened());
        }
        aes_ctr::apply(key, nonce, ctr, group.as_flattened_mut());
        if ENC {
            ghash.add(group.as_flattened());
        }
        ctr = ctr.wrapping_add(8 * group.len() as u32);
    }

    if !ENC {
        ghash.add(remainder);
    }
    aes_ctr::apply(key, nonce, ctr, remainder);
    if ENC {
        ghash.add(remainder);
    }
}

/// Encrypts (if `ENC`) or decrypts eight blocks at a time with AES-CTR and
/// GHASH stitched.
///
/// It is SSE-encoded on every CPU: VEX encoding measured no faster where the
/// CPU has AVX, and the 256- and 512-bit kernels that may run before it leave
/// the upper vector state clean.
#[target_feature(enable = "aes,ssse3,pclmulqdq")]
fn by8<const ENC: bool>(
    key: &HwKey,
    table: &ClmulTable,
    ghash: &mut Ghash<'_>,
    initial_counter: &[u8; 16],
    aad: &[u8],
    cipher_inout: &mut [u8],
) {
    ghash.add(aad);

    let (rk_first, rks, rk_last) = key.round_keys();

    let mut counter = Counter::new(initial_counter);
    let (by8_iter, remainder) = cipher_inout.as_chunks_mut::<128>();

    for blocks in by8_iter {
        // prefetch to avoid any stall later
        super::cpu::prefetch(blocks, 64);

        let c1 = counter.next();
        let c2 = counter.next();
        let c3 = counter.next();
        let c4 = counter.next();
        let c5 = counter.next();
        let c6 = counter.next();
        let c7 = counter.next();
        let c8 = counter.next();

        let mut c1 = _mm_xor_si128(c1, rk_first);
        let mut c2 = _mm_xor_si128(c2, rk_first);
        let mut c3 = _mm_xor_si128(c3, rk_first);
        let mut c4 = _mm_xor_si128(c4, rk_first);
        let mut c5 = _mm_xor_si128(c5, rk_first);
        let mut c6 = _mm_xor_si128(c6, rk_first);
        let mut c7 = _mm_xor_si128(c7, rk_first);
        let mut c8 = _mm_xor_si128(c8, rk_first);

        for rk in rks {
            c1 = _mm_aesenc_si128(c1, *rk);
            c2 = _mm_aesenc_si128(c2, *rk);
            c3 = _mm_aesenc_si128(c3, *rk);
            c4 = _mm_aesenc_si128(c4, *rk);
            c5 = _mm_aesenc_si128(c5, *rk);
            c6 = _mm_aesenc_si128(c6, *rk);
            c7 = _mm_aesenc_si128(c7, *rk);
            c8 = _mm_aesenc_si128(c8, *rk);
        }

        let c1 = _mm_aesenclast_si128(c1, rk_last);
        let c2 = _mm_aesenclast_si128(c2, rk_last);
        let c3 = _mm_aesenclast_si128(c3, rk_last);
        let c4 = _mm_aesenclast_si128(c4, rk_last);
        let c5 = _mm_aesenclast_si128(c5, rk_last);
        let c6 = _mm_aesenclast_si128(c6, rk_last);
        let c7 = _mm_aesenclast_si128(c7, rk_last);
        let c8 = _mm_aesenclast_si128(c8, rk_last);

        // SAFETY: `blocks` is 128 bytes and readable
        let (p1, p2, p3, p4, p5, p6, p7, p8) = unsafe {
            (
                _mm_loadu_si128(blocks.as_ptr().add(0).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(16).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(32).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(48).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(64).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(80).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(96).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(112).cast()),
            )
        };

        let c1 = _mm_xor_si128(c1, p1);
        let c2 = _mm_xor_si128(c2, p2);
        let c3 = _mm_xor_si128(c3, p3);
        let c4 = _mm_xor_si128(c4, p4);
        let c5 = _mm_xor_si128(c5, p5);
        let c6 = _mm_xor_si128(c6, p6);
        let c7 = _mm_xor_si128(c7, p7);
        let c8 = _mm_xor_si128(c8, p8);

        // SAFETY: `blocks` is 128 bytes and writable, due to `as_chunks_mut`
        unsafe {
            _mm_storeu_si128(blocks.as_mut_ptr().add(0).cast(), c1);
            _mm_storeu_si128(blocks.as_mut_ptr().add(16).cast(), c2);
            _mm_storeu_si128(blocks.as_mut_ptr().add(32).cast(), c3);
            _mm_storeu_si128(blocks.as_mut_ptr().add(48).cast(), c4);
            _mm_storeu_si128(blocks.as_mut_ptr().add(64).cast(), c5);
            _mm_storeu_si128(blocks.as_mut_ptr().add(80).cast(), c6);
            _mm_storeu_si128(blocks.as_mut_ptr().add(96).cast(), c7);
            _mm_storeu_si128(blocks.as_mut_ptr().add(112).cast(), c8);
        }

        let (a1, a2, a3, a4, a5, a6, a7, a8) = if ENC {
            (c1, c2, c3, c4, c5, c6, c7, c8)
        } else {
            (p1, p2, p3, p4, p5, p6, p7, p8)
        };

        let a1 = _mm_shuffle_epi8(a1, BYTESWAP);
        let a2 = _mm_shuffle_epi8(a2, BYTESWAP);
        let a3 = _mm_shuffle_epi8(a3, BYTESWAP);
        let a4 = _mm_shuffle_epi8(a4, BYTESWAP);
        let a5 = _mm_shuffle_epi8(a5, BYTESWAP);
        let a6 = _mm_shuffle_epi8(a6, BYTESWAP);
        let a7 = _mm_shuffle_epi8(a7, BYTESWAP);
        let a8 = _mm_shuffle_epi8(a8, BYTESWAP);

        let a1 = _mm_xor_si128(ghash.current, a1);
        ghash.current = ghash::_mul8(table, a1, a2, a3, a4, a5, a6, a7, a8);
    }

    let cipher_inout = remainder;

    if !ENC {
        ghash.add(cipher_inout);
    }

    {
        let (blocks_iter, remainder) = cipher_inout.as_chunks_mut::<16>();
        for block in blocks_iter {
            let c1 = counter.next();

            let mut c1 = _mm_xor_si128(c1, rk_first);

            for rk in rks {
                c1 = _mm_aesenc_si128(c1, *rk);
            }

            let c1 = _mm_aesenclast_si128(c1, rk_last);

            // SAFETY: `block` is 16 bytes due to `as_chunks_mut`
            let p1 = unsafe { _mm_loadu_si128(block.as_ptr().cast()) };
            let c1 = _mm_xor_si128(c1, p1);

            // SAFETY: `block` is 16 bytes and writable, due to `as_chunks_mut`
            unsafe { _mm_storeu_si128(block.as_mut_ptr().cast(), c1) };
        }

        let cipher_inout = remainder;
        if !cipher_inout.is_empty() {
            let c1 = counter.next();
            let mut c1 = _mm_xor_si128(c1, rk_first);

            for rk in rks {
                c1 = _mm_aesenc_si128(c1, *rk);
            }

            let c1 = _mm_aesenclast_si128(c1, rk_last);
            let c1 = _mm_xor_si128(c1, ghash::load_partial(cipher_inout));
            ghash::store_partial(cipher_inout, c1);
        }
    }

    if ENC {
        ghash.add(cipher_inout);
    }
}

#[target_feature(
    enable = "aes,avx,avx2,avx512bw,avx512f,avx512vl,sse3,ssse3,pclmulqdq,vaes,vpclmulqdq"
)]
fn _cipher_avx512<const ENC: bool>(
    key: &HwKey,
    ghash: &mut Ghash<'_>,
    initial_counter: &[u8; 16],
    aad: &[u8],
    cipher_inout: &mut [u8],
    _feature_token: HaveAvx512ForAesGcm,
) {
    ghash.add(aad);

    let round_keys = key.round_keys_512();
    let (rk_first, rks, rk_last) = round_keys.split();

    let mut counter = Counter512::new(initial_counter);
    let (by16_iter, remainder) = cipher_inout.as_chunks_mut::<AVX512_MINIMUM_CIPHER_LEN>();

    let ghash_avx512 = match ghash.table {
        GhashTable::Avx512(ghash_avx512) => ghash_avx512,
        _ => panic!("unexpected ghash table variant"),
    };

    for blocks in by16_iter {
        // prefetch to avoid any stall later
        super::cpu::prefetch(blocks, 256);

        let c0123 = counter.next4();
        let c4567 = counter.next4();
        let c89ab = counter.next4();
        let ccdef = counter.next4();

        let mut c0123 = _mm512_xor_epi32(c0123, rk_first);
        let mut c4567 = _mm512_xor_epi32(c4567, rk_first);
        let mut c89ab = _mm512_xor_epi32(c89ab, rk_first);
        let mut ccdef = _mm512_xor_epi32(ccdef, rk_first);

        for rk in rks {
            c0123 = _mm512_aesenc_epi128(c0123, *rk);
            c4567 = _mm512_aesenc_epi128(c4567, *rk);
            c89ab = _mm512_aesenc_epi128(c89ab, *rk);
            ccdef = _mm512_aesenc_epi128(ccdef, *rk);
        }

        let c0123 = _mm512_aesenclast_epi128(c0123, rk_last);
        let c4567 = _mm512_aesenclast_epi128(c4567, rk_last);
        let c89ab = _mm512_aesenclast_epi128(c89ab, rk_last);
        let ccdef = _mm512_aesenclast_epi128(ccdef, rk_last);

        // SAFETY: `blocks` is 256 bytes due to `as_chunks_mut`
        let (p0123, p4567, p89ab, pcdef) = unsafe {
            (
                _mm512_loadu_si512(blocks.as_ptr().add(0).cast()),
                _mm512_loadu_si512(blocks.as_ptr().add(64).cast()),
                _mm512_loadu_si512(blocks.as_ptr().add(128).cast()),
                _mm512_loadu_si512(blocks.as_ptr().add(192).cast()),
            )
        };

        let c0123 = _mm512_xor_epi32(c0123, p0123);
        let c4567 = _mm512_xor_epi32(c4567, p4567);
        let c89ab = _mm512_xor_epi32(c89ab, p89ab);
        let ccdef = _mm512_xor_epi32(ccdef, pcdef);

        // SAFETY: `blocks` is 256 bytes and writable due to `as_chunks_mut`
        unsafe {
            _mm512_storeu_si512(blocks.as_mut_ptr().add(0).cast(), c0123);
            _mm512_storeu_si512(blocks.as_mut_ptr().add(64).cast(), c4567);
            _mm512_storeu_si512(blocks.as_mut_ptr().add(128).cast(), c89ab);
            _mm512_storeu_si512(blocks.as_mut_ptr().add(192).cast(), ccdef);
        }

        let (a0123, a4567, a89ab, acdef) = if ENC {
            (c0123, c4567, c89ab, ccdef)
        } else {
            (p0123, p4567, p89ab, pcdef)
        };

        let a0123 = _mm512_shuffle_epi8(a0123, BYTESWAP_512);
        let a4567 = _mm512_shuffle_epi8(a4567, BYTESWAP_512);
        let a89ab = _mm512_shuffle_epi8(a89ab, BYTESWAP_512);
        let acdef = _mm512_shuffle_epi8(acdef, BYTESWAP_512);

        let c0___ = _mm512_inserti32x4::<0>(_mm512_setzero_si512(), ghash.current);
        let a0123 = _mm512_xor_epi64(a0123, c0___);

        ghash.current = ghash::_mul16(ghash_avx512, a0123, a4567, a89ab, acdef);
    }

    if remainder.is_empty() {
        return;
    }

    // The tail, under 256 bytes, in one pass of four vectors masked to its
    // length. AES is latency-bound here, so the unused vectors cost little.
    let mut ks = [
        counter.next4(),
        counter.next4(),
        counter.next4(),
        counter.next4(),
    ];
    for k in &mut ks {
        *k = _mm512_xor_epi32(*k, rk_first);
    }
    for rk in rks {
        for k in &mut ks {
            *k = _mm512_aesenc_epi128(*k, *rk);
        }
    }

    let mut tail = [_mm512_setzero_si512(); 4];
    for ((t, k), chunk) in tail.iter_mut().zip(ks).zip(remainder.chunks_mut(64)) {
        // The first `chunk.len()` bytes, at least one.
        let mask = u64::MAX >> (64 - chunk.len());
        // SAFETY: the mask covers `chunk`, and masked-off bytes are not read
        let p = unsafe { _mm512_maskz_loadu_epi8(mask, chunk.as_ptr().cast()) };
        let c = _mm512_xor_epi32(
            _mm512_maskz_mov_epi8(mask, _mm512_aesenclast_epi128(k, rk_last)),
            p,
        );
        // SAFETY: the mask covers `chunk`, and masked-off bytes are not written
        unsafe { _mm512_mask_storeu_epi8(chunk.as_mut_ptr().cast(), mask, c) };
        *t = _mm512_shuffle_epi8(if ENC { c } else { p }, BYTESWAP_512);
    }
    ghash.current = ghash::_mul_tail(ghash_avx512, ghash.current, tail, remainder.len());
}

/// How many message bytes needed to benefit from the AVX512 by-16 impl
///
/// `cipher_avx512` _works_ for shorter lengths, but is not worth it.
const AVX512_MINIMUM_CIPHER_LEN: usize = 16 * 16;

/// How many message bytes BoringSSL's 512-bit kernel needs to beat the AVX512
/// by-16 impl: its interleaved AES and GHASH win on long messages, but its
/// setup costs more on short ones.
const AVX512_KERNEL_MINIMUM_CIPHER_LEN: usize = 2048;

/// The message length from which pyca/verified-garbage's AES-GCM seals and
/// opens on the AVX-512 tier, where it runs. On Zen 5 (a Ryzen 9 9950X),
/// under rind's glue and a 32-byte AAD, its seals took 1.05-1.10x the time of
/// BoringSSL's 512-bit kernel at 4 and 5 KB and 0.85-1.01x from 6 to 64 KB,
/// and its opens 0.96-1.07x and 0.87-1.00x; at 2 and 3 KB both took
/// 1.02-1.25x, and below 2 KB, against rind's by-16 path, up to 1.56x.
/// Preparing its key context doubles key setup (75-95 to 160-190 ns), so a
/// key makes it on its first message this long. On Granite Rapids
/// ([kixel-ai/rind#955](https://github.com/kixel-ai/rind/pull/955)) it lost
/// below 12 KB and won above only with AES-128 and AES-192, so it runs on no
/// other CPU.
const VG_FROM: usize = 6144;

/// How many message bytes BoringSSL's 256-bit kernel needs to beat the AVX
/// path, whose single blocks are quicker for short messages.
const VAES_AVX2_MINIMUM_CIPHER_LEN: usize = 16 * 16;

/// The message length from which Vale's AES-GCM seals on the AVX tier, which
/// opens with it at every length. On Coffee Lake (an i7-8700 and two
/// i7-8700Bs), under AADs of 5 to 32 bytes, its seals measured 0.94-1.19x
/// the by-8 path's time from 1 to 128 bytes (medians 1.04-1.06x), 0.93-0.98x
/// at 0, and 0.75-1.08x from 129 to 512 bytes (medians 0.90-0.91x), and its
/// opens 0.72-1.02x at every length.
const AVX_VALE_SEAL_FROM: usize = 129;

/// The message lengths below which Vale's AES-GCM runs on the VAES-AVX2
/// tier, to decrypt and to encrypt. Below 256 bytes its opens measured
/// 0.83-1.09x the by-8 path's time on Zen 3 (median 0.95x), and 0.74-1.06x
/// on Arrow Lake's P-cores and 0.70-1.08x on its E-cores (medians 0.88x and
/// 0.90x), under an AAD of a partial block, as QUIC's and TLS's are, or of
/// whole ones. From 16 bytes its seals measured 1.04-1.46x on Zen 3 and
/// 0.94-1.38x on Arrow Lake, losing below 176 bytes on both.
///
/// The AVX-512 tier runs no Vale. Below 256 bytes its opens measured
/// 0.95-1.44x the by-8 path's time on Zen 5 (median 1.03x), 0.96-1.37x on
/// Granite Rapids (median 1.07x), and 0.70-1.14x on Zen 4 (median 1.00x),
/// and its seals lost on all three.
const VAES_AVX2_VALE_OPEN_BELOW: usize = 256;
const VAES_AVX2_VALE_SEAL_BELOW: usize = 0;

/// This stores the current four counter values, in big endian.
#[derive(Debug)]
struct Counter512(__m512i);

impl Counter512 {
    #[inline]
    #[target_feature(enable = "sse3,ssse3,avx,avx2,avx512f")]
    fn new(bytes: &[u8; 16]) -> Self {
        // SAFETY: `bytes` is a 128-bits and can be loaded from
        Self(unsafe {
            let mut cnt = Counter::new(bytes);
            let a = cnt.next();
            let b = cnt.next();
            let c = cnt.next();
            let d = cnt.next();

            let r: __m512i = mem::transmute(_mm512_undefined());
            let r = _mm512_inserti32x4::<0>(r, _mm_shuffle_epi8(a, BYTESWAP_EPI64));
            let r = _mm512_inserti32x4::<1>(r, _mm_shuffle_epi8(b, BYTESWAP_EPI64));
            let r = _mm512_inserti32x4::<2>(r, _mm_shuffle_epi8(c, BYTESWAP_EPI64));
            _mm512_inserti32x4::<3>(r, _mm_shuffle_epi8(d, BYTESWAP_EPI64))
        })
    }

    #[target_feature(enable = "sse3,ssse3,avx,avx2,avx512f,avx512bw")]
    #[must_use]
    #[inline]
    fn next4(&mut self) -> __m512i {
        let r = _mm512_shuffle_epi8(self.0, BYTESWAP_512_EPI64);
        // 32-bit lanes, so each counter wraps within its last four bytes, as
        // GCM's from any IV must.
        self.0 = _mm512_add_epi32(self.0, COUNTER_512_4);
        r
    }
}

/// This stores the current counter value, in big endian.
#[derive(Clone, Copy, Debug)]
struct Counter(__m128i);

impl Counter {
    #[inline]
    #[target_feature(enable = "sse2,sse3,ssse3")]
    fn new(bytes: &[u8; 16]) -> Self {
        // SAFETY: `bytes` is a 128-bit value and can be loaded from
        let c = unsafe { _mm_lddqu_si128(bytes.as_ptr().cast()) };
        let c = _mm_shuffle_epi8(c, BYTESWAP_EPI64);
        let c = _mm_add_epi32(c, COUNTER_1); // skip first counter (it was already used as y0)

        Self(c)
    }

    #[target_feature(enable = "sse2,ssse3")]
    #[must_use]
    #[inline]
    fn next(&mut self) -> __m128i {
        let r = _mm_shuffle_epi8(self.0, BYTESWAP_EPI64);
        self.0 = _mm_add_epi32(self.0, COUNTER_1);
        r
    }
}

// SAFETY: both u128 and __m128i have the same size and all bits mean the same thing
const COUNTER_1: __m128i = unsafe { mem::transmute(1u128 << 64) };

// SAFETY: [u8; 64] and __m512i have the same size
const COUNTER_512_4: __m512i = unsafe {
    mem::transmute([
        0u8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, //
        0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, //
        0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, //
        0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, //
    ])
};

// SAFETY: both u128 and __m128i have the same size and all bits mean the same thing
const BYTESWAP: __m128i = unsafe { mem::transmute(0x00010203_04050607_08090a0b_0c0d0e0fu128) };

// SAFETY: both u128 and __m128i have the same size and all bits mean the same thing
const BYTESWAP_EPI64: __m128i =
    unsafe { mem::transmute(0x08090a0b_0c0d0e0f_00010203_04050607u128) };

// SAFETY: [u8; 64] and __m512i have the same size
const BYTESWAP_512: __m512i = unsafe {
    mem::transmute([
        15u8, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, //
        31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, //
        47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, //
        63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, //
    ])
};

// SAFETY: [u8; 64] and __m512i have the same size
const BYTESWAP_512_EPI64: __m512i = unsafe {
    mem::transmute([
        7, 6, 5, 4, 3, 2, 1, 0, 15u8, 14, 13, 12, 11, 10, 9, 8, //
        23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24, //
        39, 38, 37, 36, 35, 34, 33, 32, 47, 46, 45, 44, 43, 42, 41, 40, //
        55, 54, 53, 52, 51, 50, 49, 48, 63, 62, 61, 60, 59, 58, 57, 56,
    ])
};

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;
    use crate::low::generic::ghash::gcm_model;
    use crate::low::x86_64::adx_mux::tests::Rng;
    use crate::low::x86_64::aes_gcm_vg::LazyVgKey;
    use crate::low::x86_64::aes_nohw::NohwKey;
    use crate::low::x86_64::cpu::{HaveAesHardware, HaveAvxMovbeForAesGcm, HaveSsse3};
    use crate::low::x86_64::ct_sde;
    use crate::low::x86_64::ghash_nohw::NohwTable;
    use crate::low::x86_64::ghash_ssse3_x86_64::Ssse3Table;
    use crate::low::x86_64::vpaes_x86_64::VpaesKey;

    // Every other test sees only the path the CPU picks, so the slower ones
    // are checked against it here, under a key `admin/ctgrind` keeps secret:
    // the by-8 PCLMULQDQ kernel, which a CPU with AVX and MOVBE runs only for
    // short messages, Vale's AES-GCM, vpaes with SSSE3 GHASH, SSE2 AES
    // with integer GHASH, and on an AVX-512 CPU, VG's AES-GCM, which only
    // Zen 5 picks, and BoringSSL's kernel, which it replaces there. Each key size, and AAD and message lengths around
    // the block, six-, eight-, and sixteen-block boundaries, the minimums of
    // Vale's six-block loop, and where the AVX and VAES-AVX2 tiers hand over
    // between Vale and by-8, both ways, with a tag wrong in either half, and
    // one long enough to carry out of the counter's low byte.
    #[test]
    fn paths_match() {
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for key_len in [16, 24, 32] {
            let key = bytes(key_len, 1);
            ct::secret_slice(&key);
            let fast = AesKey::new(&key);
            let h = fast.encrypt_block(&[0; 16]);
            let fast_table = GhashTable::new(u128::from_be_bytes(h));
            let mut slow = vec![(
                AesKey::Nohw(NohwKey::new(&key)),
                GhashTable::Nohw(NohwTable::new(&h)),
            )];
            if let Some(token) = HaveSsse3::check() {
                slow.push((
                    AesKey::Vpaes(VpaesKey::new(&key, token)),
                    GhashTable::Ssse3(Ssse3Table::new(&h, token)),
                ));
            }
            if let Some(hw) = HaveAesHardware::check() {
                let clmul = ClmulTable::new(u128::from_be_bytes(h), hw);
                slow.push((AesKey::new(&key), GhashTable::Clmul(clmul)));
                if let Some(token) = HaveAvxMovbeForAesGcm::check() {
                    let h = u128::from_be_bytes(h);
                    let clmul = ClmulTable::new(h, hw);
                    let kernel = AvxKernel::new(&clmul, h, token);
                    slow.push((AesKey::new(&key), GhashTable::Avx(clmul, kernel)));
                }
                // The AVX-512 tier with VG's AES-GCM and without, whichever
                // the CPU picks.
                if let Some(token) = HaveAvx512ForAesGcm::check() {
                    for vg in [None, Some(token.vg_anywhere())] {
                        let mut table = GhashTableAvx512::new(u128::from_be_bytes(h), hw, token);
                        table.vg = vg.map(LazyVgKey::with);
                        slow.push((AesKey::new(&key), GhashTable::Avx512(table)));
                    }
                }
            }

            // Around where the AVX and VAES-AVX2 tiers hand over between
            // Vale's AES-GCM and their own paths, and the AVX-512 tier
            // between BoringSSL's kernel and VG's.
            let crossovers = [
                AVX_VALE_SEAL_FROM,
                VAES_AVX2_VALE_OPEN_BELOW,
                VAES_AVX2_VALE_SEAL_BELOW,
                VG_FROM,
            ]
            .into_iter()
            .flat_map(|n| [n.saturating_sub(1), n, n + 1]);
            let mut msg_lens = vec![
                0, 1, 15, 16, 17, 95, 96, 97, 112, 127, 128, 129, 255, 256, 257, 287, 288, 289,
                1000, 5000,
            ];
            // A TLS record's 16 KB, and a partial block, on VG's side.
            msg_lens.push(16384 + 17);
            msg_lens.extend(crossovers);
            msg_lens.sort_unstable();
            msg_lens.dedup();

            for aad_len in [0, 1, 16, 17] {
                for &msg_len in &msg_lens {
                    let nonce = bytes(12, msg_len as u32).try_into().unwrap();
                    let aad = bytes(aad_len, 2);
                    let plain = bytes(msg_len, 3);

                    let mut want = plain.clone();
                    let want_tag =
                        ct::into_public(seal(&fast, &fast_table, &nonce, &aad, &mut want));
                    ct::public_slice(&want);
                    for (key, table) in &slow {
                        let mut got = plain.clone();
                        let tag = ct::into_public(seal(key, table, &nonce, &aad, &mut got));
                        ct::public_slice(&got);
                        let what = format!("{key_len} {aad_len} {msg_len}");
                        assert_eq!(got, want, "{what}");
                        assert_eq!(tag, want_tag, "{what}");

                        let valid = open(key, table, &nonce, &aad, &mut got, &want_tag);
                        ct::public_slice(&got);
                        assert!(ct::into_public(valid), "{what}");
                        assert_eq!(got, plain, "{what}");

                        for byte in [0, 15] {
                            let mut wrong = want_tag;
                            wrong[byte] ^= 1;
                            let mut got = want.clone();
                            let valid = open(key, table, &nonce, &aad, &mut got, &wrong);
                            assert!(!ct::into_public(valid), "{what}, byte {byte}");
                        }
                    }
                }
            }
        }
    }

    // An IV other than 96 bits hashes to a counter block whose 32-bit
    // counter may wrap within one message, as GCM's increment does mod 2^32
    // without carrying into the rest of the block: on every path, at lengths
    // that wrap within each kernel's loop and tail, or not at all. Last, a
    // 17-byte IV's counter block, which is secret, as it hashes under the
    // key, for `admin/ctgrind`.
    #[test]
    fn counter_wraps() {
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for key_len in [16, 24, 32] {
            let key = bytes(key_len, 1);
            ct::secret_slice(&key);
            let fast = AesKey::new(&key);
            let h = fast.encrypt_block(&[0; 16]);
            let mut paths = vec![(
                AesKey::Nohw(NohwKey::new(&key)),
                GhashTable::Nohw(NohwTable::new(&h)),
            )];
            if let Some(token) = HaveSsse3::check() {
                paths.push((
                    AesKey::Vpaes(VpaesKey::new(&key, token)),
                    GhashTable::Ssse3(Ssse3Table::new(&h, token)),
                ));
            }
            if let Some(hw) = HaveAesHardware::check() {
                let clmul = ClmulTable::new(u128::from_be_bytes(h), hw);
                paths.push((AesKey::new(&key), GhashTable::Clmul(clmul)));
            }
            paths.push((fast, GhashTable::new(u128::from_be_bytes(h))));

            for (key, table) in &paths {
                let starts = [0xffff_ffffu32, 0xffff_fffe, 0xffff_ff00, 0xffff_f000, 7];
                for start in starts.map(Some).into_iter().chain([None]) {
                    for msg_len in [16, 17, 100, 128, 300, 1000, 2400, 5000] {
                        let y0 = match start {
                            Some(start) => {
                                let mut y0: [u8; 16] =
                                    bytes(16, msg_len as u32).try_into().unwrap();
                                y0[12..].copy_from_slice(&start.to_be_bytes());
                                y0
                            }
                            None => initial_counter(table, &bytes(17, msg_len as u32)),
                        };
                        let aad = bytes(17, 2);
                        let plain = bytes(msg_len, 3);
                        let what = format!("{key_len} {start:x?} {msg_len}");
                        let (want, want_tag) =
                            gcm_model(|b| key.encrypt_block(b), &y0, &aad, &plain);
                        ct::public_slice(&want);

                        let mut got = plain.clone();
                        let tag = tagged_from::<true>(key, table, y0, &aad, &mut got);
                        ct::public_slice(&got);
                        assert_eq!(got, want, "{what}");
                        assert_eq!(ct::into_public(tag), ct::into_public(want_tag), "{what}");

                        let tag = tagged_from::<false>(key, table, y0, &aad, &mut got);
                        ct::public_slice(&got);
                        assert_eq!(got, plain, "{what}");
                        assert_eq!(ct::into_public(tag), ct::into_public(want_tag), "{what}");
                    }
                }
            }
        }
    }

    // The AVX-512 key setup, by-16 loop, BoringSSL kernel, and VG's AES-GCM
    // with its key preparation, both ways, with a secret key, nonce, AAD, and
    // message, for `admin/ct-sde`. Each message takes its path's 16-block
    // loop and a masked tail of 12 blocks and 8 bytes, and the AAD the 512-bit
    // GHASH and then a partial block.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_aes128_gcm() {
        trace_avx512(16);
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_aes192_gcm() {
        trace_avx512(24);
    }

    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_aes256_gcm() {
        trace_avx512(32);
    }

    fn trace_avx512(key_len: usize) {
        let mut rng = Rng(ct_sde::seed());
        let (key, mut table) = traced_key(&mut rng, key_len);
        let GhashTable::Avx512(avx512) = &mut table else {
            panic!("AVX-512 VAES");
        };
        // VG's, from its length, as on Zen 5, whichever CPU SDE emulates.
        avx512.vg = Some(LazyVgKey::with(avx512.token.vg_anywhere()));
        for len in [
            AVX512_MINIMUM_CIPHER_LEN,
            AVX512_KERNEL_MINIMUM_CIPHER_LEN,
            VG_FROM,
        ] {
            traced_seal_open(&mut rng, &key, &table, len + 200);
        }
    }

    // The VAES-AVX2 key setup and BoringSSL's 256-bit kernel, both ways, for
    // each key size, as `trace_avx512`. The message takes the kernel's 8-block
    // loop and a tail of 7 blocks, then a partial block of 8 bytes.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_aes_gcm_vaes_avx2() {
        let mut rng = Rng(ct_sde::seed());
        let len = VAES_AVX2_MINIMUM_CIPHER_LEN + 7 * 16 + 8;
        for key_len in [16, 24, 32] {
            let (key, table) = traced_key(&mut rng, key_len);
            assert!(matches!(table, GhashTable::VaesAvx2(..)), "VAES-AVX2");
            traced_seal_open(&mut rng, &key, &table, len);
        }
    }

    fn bytes(rng: &mut Rng, n: usize) -> Vec<u8> {
        (0..n).map(|_| rng.next() as u8).collect()
    }

    /// Makes the key and GHASH table for a secret key, traced.
    fn traced_key(rng: &mut Rng, key_len: usize) -> (AesKey, GhashTable) {
        let key = bytes(rng, key_len);
        ct_sde::traced(|| {
            let key = AesKey::new(&key);
            let h = key.encrypt_block(&[0; 16]);
            (key, GhashTable::new(u128::from_be_bytes(h)))
        })
    }

    /// Seals and opens a secret message of `len` bytes, under a secret nonce
    /// and 300 bytes of secret AAD, each traced.
    fn traced_seal_open(rng: &mut Rng, key: &AesKey, table: &GhashTable, len: usize) {
        let nonce = bytes(rng, 12).try_into().unwrap();
        let aad = bytes(rng, 300);
        let mut msg = bytes(rng, len);
        let tag = ct_sde::traced(|| seal(key, table, &nonce, &aad, &mut msg));
        ct_sde::traced(|| open(key, table, &nonce, &aad, &mut msg, &tag));
    }
}
