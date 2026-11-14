// Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
// Copyright (c) 2022-2023 HACL* Contributors
// Copyright 2023 Cryspen Sarl
// SPDX-License-Identifier: Apache-2.0

//! HACL*'s SHA-256 block function from libcrux-sha2 0.0.9 (`hacl.rs`,
//! `sha256_update`, Apache-2.0), in internal RAM on ESP-IDF Xtensa.
//!
//! The ESP32-S3 runs flash code through a 16 KiB instruction cache, and the
//! unrolled HACL* body is about 12 KiB of it, so its speed there depends on
//! where the linker happens to put it relative to the caller: an unrelated
//! 1.2 KiB change elsewhere in the image made 16-byte `update` calls 1.7×
//! slower with the same instructions. ESP-IDF maps `.iram1.*` sections into
//! IRAM, which is fetched without the cache. The rounds, the message schedule
//! and their order are HACL*'s; only the slices are fixed-size arrays, so the
//! body has no bounds checks and calls nothing outside IRAM. No branch or
//! index depends on the message or the state.

use libcrux_macros as krml;
use libcrux_sha2::hacl::k224_256;

// The unrolled schedule's last rewrite of `ws` is never read, as in HACL*.
#[allow(unused_assignments)]
#[inline(never)]
#[cfg_attr(
    all(target_arch = "xtensa", target_os = "espidf"),
    unsafe(link_section = ".iram1.rind_sha256_update")
)]
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
                    ^ ((t2.wrapping_shl(13u32) | t2.wrapping_shr(19u32)) ^ t2.wrapping_shr(10u32));
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
#[cfg_attr(
    all(target_arch = "xtensa", target_os = "espidf"),
    unsafe(link_section = ".iram1.rind_sha256_nblocks")
)]
pub(super) fn sha256_update_nblocks(st: &mut [u32; 8], blocks: &[u8]) {
    let (blocks, _) = blocks.as_chunks::<64>();
    for b in blocks {
        sha256_update(b, st);
    }
}
