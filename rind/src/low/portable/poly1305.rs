// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The portable backend's Poly1305: rind's 26-bit limbs in
//! `generic::poly1305_32` on 32-bit targets, where each limb product is one
//! 32x32->64-bit multiply, and rind's 64-bit limbs in `generic::poly1305` on
//! 64-bit ones, as x86_64 runs without SSE4.1. Neither counts its input, so
//! neither limits the AEADs' message length.
//!
//! HACL*'s verified streaming `Hacl_MAC_Poly1305`, as libcrux-poly1305
//! ships it, is here for armv7 without NEON and for tests. It too uses
//! 26-bit limbs, but keeps them in `u64`s, so a 32-bit core without NEON
//! spends most of its time in 64-bit multiplies and adds, and it takes at
//! most `u32::MAX` bytes.

#[cfg(all(
    rind_backend = "portable",
    any(target_pointer_width = "32", rind_limb = "32")
))]
pub(crate) use crate::low::generic::poly1305_32::Poly1305;
#[cfg(any(rind_backend = "arm", test))]
use libcrux_hacl_rs::streaming_types::error_code;
#[cfg(any(rind_backend = "arm", test))]
use libcrux_poly1305::hacl::mac_poly1305::{self, state_t};

#[cfg(all(
    rind_backend = "portable",
    target_pointer_width = "64",
    not(rind_limb = "32")
))]
pub(crate) use crate::low::generic::poly1305::Poly1305;

#[cfg(any(rind_backend = "arm", test))]
pub(crate) struct Hacl([state_t; 1]);

#[cfg(any(rind_backend = "arm", test))]
impl Hacl {
    pub(crate) fn new(key: &[u8; 32]) -> Self {
        let mut state = [state_t {
            block_state: [0; 25],
            buf: [0; 16],
            total_len: 0,
            p_key: [0; 32],
        }];
        mac_poly1305::reset(&mut state, key);
        Self(state)
    }

    pub(crate) fn add_bytes(&mut self, bytes: &[u8]) {
        // HACL refuses more than `u32::MAX` bytes in total, which the AEADs
        // cannot reach in a 32-bit address space: their AAD and message are
        // disjoint slices in the same address space as this state, plus at
        // most 46 bytes of padding and lengths.
        let len = u32::try_from(bytes.len()).expect("Poly1305 input fits 32 bits");
        let result = mac_poly1305::update(&mut self.0, bytes, len);
        assert!(result == error_code::Success, "Poly1305 input fits 32 bits");
    }

    pub(crate) fn finish(self) -> [u8; 16] {
        let mut tag = [0u8; 16];
        mac_poly1305::digest(&self.0, &mut tag);
        tag
    }
}

#[cfg(all(test, target_pointer_width = "64"))]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;

    // 32-bit targets run HACL*'s Poly1305 and 64-bit ones rind's, so each is
    // checked against the other here: every length up to 200 bytes, plus
    // some longer, each fed whole and in ragged pieces, and all-ones blocks
    // and key, which push the accumulator to its largest values before the
    // final reduction. The key and message are secret, so under
    // `admin/ctgrind` this also checks both are constant time in them.
    #[test]
    fn hacl_matches_generic() {
        let key: [u8; 32] = core::array::from_fn(|i| 0xa5 ^ (i as u8).wrapping_mul(29));
        let msg: Vec<u8> = (0..1100u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        for (key, msg) in [(key, msg), ([0xff; 32], vec![0xff; 1100])] {
            ct::secret_slice(&key);
            ct::secret_slice(&msg);
            for len in (0..=200).chain([255, 256, 257, 1023, 1024, 1025, 1100]) {
                let msg = &msg[..len];
                let mut want = Poly1305::new(&key);
                want.add_bytes(msg);
                let want = ct::into_public(want.finish());

                for piece in [len.max(1), 1, 7, 16, 31, 33] {
                    let mut got = Hacl::new(&key);
                    for chunk in msg.chunks(piece) {
                        got.add_bytes(chunk);
                    }
                    assert_eq!(
                        ct::into_public(got.finish()),
                        want,
                        "{len} bytes in pieces of {piece}"
                    );
                }
            }
        }
    }
}
