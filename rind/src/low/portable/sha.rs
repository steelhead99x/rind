// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1 on rind's portable code in `generic`, as armv7 runs it without the
//! crypto extension, and SHA-256 on HACL*'s verified `Hacl_Hash_SHA2`, as
//! libcrux-sha2 ships it. HACL*'s SHA-256 took 0.67-0.93 of `generic`'s time
//! at 16 KB on x86_64. SHA-384/512 is that HACL* body on 64-bit targets and
//! the rolled loop in `generic::sha512` on 32-bit targets, where the unrolled
//! body is about 47 KiB and misses a 16 KiB instruction cache. SHA-256 stays
//! on HACL* at every length: a rolled loop beside that ~12 KiB body made long
//! hashes slower on an ESP32-S3.

#[cfg(not(all(target_arch = "xtensa", target_os = "espidf")))]
use libcrux_sha2::hacl::sha256_update_nblocks;
#[cfg(target_pointer_width = "64")]
use libcrux_sha2::hacl::sha512_update_nblocks;

pub(crate) use crate::low::generic::sha1::sha1_compress_blocks;

/// HACL* takes a 32-bit length, so longer input goes in pieces of whole
/// blocks below it.
#[cfg_attr(all(target_arch = "xtensa", target_os = "espidf"), allow(dead_code))]
const PIECE: usize = 1 << 31;

/// Compresses whole 64-byte `blocks` into `state`.
///
/// One loop of HACL*'s `sha256_update_nblocks` on every pointer width.
/// 32-bit portable does not keep a rolled compressor beside it: on an
/// ESP32-S3 that second body made long hashes slower.
pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    #[cfg(all(target_arch = "xtensa", target_os = "espidf"))]
    {
        iram::sha256_update_nblocks(state, blocks);
    }
    #[cfg(not(all(target_arch = "xtensa", target_os = "espidf")))]
    for piece in blocks.chunks(PIECE) {
        sha256_update_nblocks(piece.len() as u32, piece, state);
    }
}

/// HACL*'s SHA-256 block function from libcrux-sha2 0.0.9 (`hacl.rs`,
/// `sha256_update`, Apache-2.0), in internal RAM on ESP-IDF Xtensa.
///
/// The ESP32-S3 runs flash code through a 16 KiB instruction cache, and the
/// unrolled HACL* body is about 12 KiB of it, so its speed there depends on
/// where the linker happens to put it relative to the caller: an unrelated
/// 1.2 KiB change elsewhere in the image made 16-byte `update` calls 1.7×
/// slower with the same instructions. ESP-IDF maps `.iram1.*` sections into
/// IRAM, which is fetched without the cache. The rounds, the message schedule
/// and their order are HACL*'s; only the slices are fixed-size arrays, so the
/// body has no bounds checks and calls nothing outside IRAM. No branch or
/// index depends on the message or the state.
#[cfg(all(target_arch = "xtensa", target_os = "espidf"))]
mod iram {
    use libcrux_macros as krml;
    use libcrux_sha2::hacl::k224_256;

    // The unrolled schedule's last rewrite of `ws` is never read, as in HACL*.
    #[allow(unused_assignments)]
    #[inline(never)]
    #[unsafe(link_section = ".iram1.rind_sha256_update")]
    fn sha256_update(b: &[u8; 64], hash: &mut [u32; 8]) {
        let hash_old: [u32; 8] = *hash;
        let mut ws: [u32; 16] = [0u32; 16];
        krml::unroll_for!(16, "i", 0u32, 1u32, {
            let o = 4 * i as usize;
            ws[i as usize] = u32::from_be_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]]);
        });
        krml::unroll_for!(4, "i", 0u32, 1u32, {
            krml::unroll_for!(16, "i0", 0u32, 1u32, {
                let k_t: u32 = k224_256[16u32.wrapping_mul(i).wrapping_add(i0) as usize];
                let ws_t: u32 = ws[i0 as usize];
                let a0: u32 = hash[0];
                let b0: u32 = hash[1];
                let c0: u32 = hash[2];
                let d0: u32 = hash[3];
                let e0: u32 = hash[4];
                let f0: u32 = hash[5];
                let g0: u32 = hash[6];
                let h02: u32 = hash[7];
                let t1: u32 = h02
                    .wrapping_add(
                        (e0.wrapping_shl(26u32) | e0.wrapping_shr(6u32))
                            ^ ((e0.wrapping_shl(21u32) | e0.wrapping_shr(11u32))
                                ^ (e0.wrapping_shl(7u32) | e0.wrapping_shr(25u32))),
                    )
                    .wrapping_add(e0 & f0 ^ !e0 & g0)
                    .wrapping_add(k_t)
                    .wrapping_add(ws_t);
                let t2: u32 = ((a0.wrapping_shl(30u32) | a0.wrapping_shr(2u32))
                    ^ ((a0.wrapping_shl(19u32) | a0.wrapping_shr(13u32))
                        ^ (a0.wrapping_shl(10u32) | a0.wrapping_shr(22u32))))
                .wrapping_add(a0 & b0 ^ (a0 & c0 ^ b0 & c0));
                hash[0] = t1.wrapping_add(t2);
                hash[1] = a0;
                hash[2] = b0;
                hash[3] = c0;
                hash[4] = d0.wrapping_add(t1);
                hash[5] = e0;
                hash[6] = f0;
                hash[7] = g0
            });
            if i < 3u32 {
                krml::unroll_for!(16, "i0", 0u32, 1u32, {
                    let t16: u32 = ws[i0 as usize];
                    let t15: u32 = ws[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                    let t7: u32 = ws[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                    let t2: u32 = ws[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                    let s1: u32 = (t2.wrapping_shl(15u32) | t2.wrapping_shr(17u32))
                        ^ ((t2.wrapping_shl(13u32) | t2.wrapping_shr(19u32))
                            ^ t2.wrapping_shr(10u32));
                    let s0: u32 = (t15.wrapping_shl(25u32) | t15.wrapping_shr(7u32))
                        ^ ((t15.wrapping_shl(14u32) | t15.wrapping_shr(18u32))
                            ^ t15.wrapping_shr(3u32));
                    ws[i0 as usize] = s1.wrapping_add(t7).wrapping_add(s0).wrapping_add(t16)
                })
            }
        });
        krml::unroll_for!(8, "i", 0u32, 1u32, {
            hash[i as usize] = hash[i as usize].wrapping_add(hash_old[i as usize]);
        })
    }

    /// HACL*'s `sha256_update_nblocks` over whole blocks, also in IRAM.
    #[inline(never)]
    #[unsafe(link_section = ".iram1.rind_sha256_nblocks")]
    pub(super) fn sha256_update_nblocks(st: &mut [u32; 8], blocks: &[u8]) {
        let (blocks, _) = blocks.as_chunks::<64>();
        for b in blocks {
            sha256_update(b, st);
        }
    }
}

/// Compresses `message`, padded and closed by the big-endian bit `length`.
#[inline(never)]
pub(crate) fn sha1_compress_padded(state: &mut [u32; 5], message: &[u8], length: [u8; 8]) {
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    sha1_compress_blocks(state, blocks);
    let mut last = [[0u8; 64]; 2];
    sha1_compress_blocks(state, crate::low::pad(rest, length, &mut last));
}

/// The digest of `state` followed by `message`, padded and closed by `length`.
#[inline]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    let mut h = *state;
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    sha256_compress_blocks(&mut h, blocks);
    let mut last = [[0u8; 64]; 2];
    sha256_compress_blocks(&mut h, crate::low::pad(rest, length, &mut last));
    crate::low::sha256_digest(&h)
}

/// Compresses whole 128-byte `blocks` into `state`.
pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    // HACL*'s `sha512_update` is fully unrolled (~47 KiB on Xtensa), which
    // is several times a 16 KiB instruction cache. On 32-bit targets use
    // the rolled compression in `generic::sha512` instead. 64-bit portable
    // keeps HACL*, which is faster when the code stays cached.
    #[cfg(target_pointer_width = "32")]
    {
        crate::low::generic::sha512::sha512_compress_blocks(state, blocks);
    }
    #[cfg(target_pointer_width = "64")]
    {
        for piece in blocks.chunks(PIECE) {
            sha512_update_nblocks(piece.len() as u32, piece, state);
        }
    }
}
