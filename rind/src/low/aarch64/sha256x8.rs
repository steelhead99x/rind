// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-256 over up to eight independent chaining values with the SHA-256
//! instructions, several lanes interleaved so that one lane's instructions
//! fill the latency of another's.
//!
//! Each lane runs the instruction sequence Arm gives for one SHA-256 block
//! (the Arm C Language Extensions' `vsha256hq_u32` example, as in aws-lc's
//! `sha256_block_data_order_hw`); only the order across lanes is new. Its
//! correctness rests on rind's tests of it against the serial routine, and
//! through SLH-DSA, against FIPS 205's vectors.

use core::arch::aarch64::*;

use super::cpu::HaveCryptoExt;
use crate::low::generic::sha256_k::K;
use crate::low::{pad, split_tail};

/// Eight SHA-256 hashes, each continuing chaining value `state` over one of
/// `messages`, which are of equal length, padded and closed by `length`.
/// `messages` holds one to eight; the digests past them are unspecified.
///
/// A group of up to `SERIAL` messages runs the serial routine; more run
/// `WIDTH` lanes at a time.
pub(crate) fn sha256_finish_x8(
    state: &[u32; 8],
    messages: &[&[u8]],
    length: [u8; 8],
) -> [[u8; 32]; 8] {
    match HaveCryptoExt::check() {
        Some(token) => finish(state, messages, length, token),
        None => crate::low::generic::sha256x8::sha256_finish_x8(state, messages, length),
    }
}

/// The lanes [`finish_group`] runs at once. On Apple's M5 a block took 30 ns
/// in one lane, 18.5 ns a lane in four, and 31 ns in eight, which spill
/// registers; eight one-block messages took 1.9 times less time than the
/// serial routine's.
const WIDTH: usize = 4;

/// The most messages in a group that the serial routine beats `WIDTH` lanes
/// on: four lanes cost 4 * 18.5 = 74 ns a block on the M5, and the serial
/// routine 30 ns a message, so it wins up to two, and a group that small
/// would repeat messages to fill its lanes.
const SERIAL: usize = 2;

fn finish(
    state: &[u32; 8],
    messages: &[&[u8]],
    length: [u8; 8],
    token: HaveCryptoExt,
) -> [[u8; 32]; 8] {
    assert!((1..=8).contains(&messages.len()));
    let len = messages[0].len();
    assert!(messages.iter().all(|m| m.len() == len));

    let mut digests = [[0u8; 32]; 8];
    for (group, digests) in messages
        .chunks(WIDTH)
        .zip(digests.as_chunks_mut::<WIDTH>().0)
    {
        if group.len() <= SERIAL {
            let serial = crate::low::generic::sha256x8::sha256_finish_x8(state, group, length);
            digests[..group.len()].copy_from_slice(&serial[..group.len()]);
            continue;
        }
        // Unused lanes hash the group's last message again.
        let lanes = core::array::from_fn(|j| group[Ord::min(j, group.len() - 1)]);
        *digests = finish_group(state, lanes, length, token);
    }
    digests
}

/// The digests of `state` over each of `lanes`, of equal length, padded and
/// closed by `length`.
fn finish_group(
    state: &[u32; 8],
    lanes: [&[u8]; WIDTH],
    length: [u8; 8],
    _token: HaveCryptoExt,
) -> [[u8; 32]; WIDTH] {
    let (whole, _) = split_tail::<64, 8>(lanes[0]);
    let whole = whole.len();
    let mut last = [[[0u8; 64]; 2]; WIDTH];
    let mut padded = [&[][..]; WIDTH];
    for ((padded, last), lane) in padded.iter_mut().zip(&mut last).zip(lanes) {
        *padded = pad(&lane[whole..], length, last);
    }
    // SAFETY: `_token` proves the CPU has the SHA-256 instructions, and rind
    // requires NEON.
    unsafe { finish_neon(state, lanes.map(|lane| &lane[..whole]), padded) }
}

/// The digests of `state` over each lane of `whole`, then of `padded`, each
/// lane's a whole number of blocks, as many as the other lanes'.
#[target_feature(enable = "neon,sha2")]
fn finish_neon(
    state: &[u32; 8],
    whole: [&[u8]; WIDTH],
    padded: [&[u8]; WIDTH],
) -> [[u8; 32]; WIDTH] {
    // SAFETY: `state` is 8 readable words.
    let (abcd, efgh) = unsafe {
        (
            vld1q_u32(state[..4].as_ptr()),
            vld1q_u32(state[4..].as_ptr()),
        )
    };
    let (mut abcd, mut efgh) = ([abcd; WIDTH], [efgh; WIDTH]);
    for blocks in [whole, padded] {
        let len = blocks[0].len();
        assert!(len.is_multiple_of(64) && blocks.iter().all(|b| b.len() == len));
        for start in (0..len).step_by(64) {
            (abcd, efgh) = block(abcd, efgh, blocks.map(|b| &b[start..start + 64]));
        }
    }

    let mut digests = [[0u8; 32]; WIDTH];
    for (j, digest) in digests.iter_mut().enumerate() {
        // SAFETY: each digest is 32 writable bytes.
        unsafe {
            vst1q_u8(
                digest[..16].as_mut_ptr(),
                vrev32q_u8(vreinterpretq_u8_u32(abcd[j])),
            );
            vst1q_u8(
                digest[16..].as_mut_ptr(),
                vrev32q_u8(vreinterpretq_u8_u32(efgh[j])),
            );
        }
    }
    digests
}

/// One block of each lane, from chaining values `abcd` and `efgh`.
#[inline]
#[target_feature(enable = "neon,sha2")]
fn block(
    mut abcd: [uint32x4_t; WIDTH],
    mut efgh: [uint32x4_t; WIDTH],
    blocks: [&[u8]; WIDTH],
) -> ([uint32x4_t; WIDTH], [uint32x4_t; WIDTH]) {
    let mut msg = [[vdupq_n_u32(0); 4]; WIDTH];
    for j in 0..WIDTH {
        assert!(blocks[j].len() == 64);
        for (i, msg) in msg[j].iter_mut().enumerate() {
            // SAFETY: each block is 64 readable bytes.
            let bytes = unsafe { vld1q_u8(blocks[j][16 * i..].as_ptr()) };
            *msg = vreinterpretq_u32_u8(vrev32q_u8(bytes));
        }
    }
    let (abcd0, efgh0) = (abcd, efgh);

    // Each step runs four rounds in every lane before the next step, so the
    // lanes' dependency chains overlap.
    for i in 0..16 {
        // SAFETY: `K` holds 64 words, so `4 * i + 4 <= 64`.
        let k = unsafe { vld1q_u32(K[4 * i..].as_ptr()) };
        for j in 0..WIDTH {
            let m = &mut msg[j];
            let wk = vaddq_u32(m[i % 4], k);
            if i < 12 {
                // The message words four steps on.
                m[i % 4] = vsha256su1q_u32(
                    vsha256su0q_u32(m[i % 4], m[(i + 1) % 4]),
                    m[(i + 2) % 4],
                    m[(i + 3) % 4],
                );
            }
            let prev = abcd[j];
            abcd[j] = vsha256hq_u32(abcd[j], efgh[j], wk);
            efgh[j] = vsha256h2q_u32(efgh[j], prev, wk);
        }
    }

    for j in 0..WIDTH {
        abcd[j] = vaddq_u32(abcd[j], abcd0[j]);
        efgh[j] = vaddq_u32(efgh[j], efgh0[j]);
    }
    (abcd, efgh)
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // Checked against the serial routine directly, since a CPU without the
    // SHA-256 instructions never reaches the interleaved one.
    #[test]
    fn interleaved_matches_serial() {
        let Some(token) = HaveCryptoExt::check() else {
            return;
        };
        let _entry = crate::low::Entry::new_secret();
        let state = core::array::from_fn(|i| (i as u32).wrapping_mul(0x9e3779b9));
        let messages: [[u8; 200]; 8] =
            core::array::from_fn(|j| core::array::from_fn(|i| (j * 64 + i * 7) as u8));
        // Under ctgrind, the messages are secret, as SLH-DSA's are.
        crate::low::ct::secret_slice(&messages);
        for len in [0, 1, 54, 55, 56, 63, 64, 65, 119, 120, 128, 200] {
            for lanes in 1..=8 {
                let messages: Vec<&[u8]> = messages[..lanes].iter().map(|m| &m[..len]).collect();
                let length = ((64 + len as u64) * 8).to_be_bytes();
                let want = crate::low::ct::into_public(
                    crate::low::generic::sha256x8::sha256_finish_x8(&state, &messages, length),
                );
                let got = crate::low::ct::into_public(finish(&state, &messages, length, token));
                assert_eq!(got[..lanes], want[..lanes], "{len} bytes, {lanes} lanes");
            }
        }
    }
}
