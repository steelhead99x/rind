// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::aes::AesKey;

/// XORs AES-CTR keystream into `inout`.
///
/// The counter blocks are `nonce` followed by the big-endian `counter`,
/// `counter + 1`, and so on, wrapping within 32 bits.
pub(crate) fn apply(key: &AesKey, nonce: &[u8; 12], counter: u32, inout: &mut [u8]) {
    let mut ivec = [0u8; 16];
    ivec[..12].copy_from_slice(nonce);
    ivec[12..].copy_from_slice(&counter.to_be_bytes());
    key.ctr32(&ivec, inout);
}
