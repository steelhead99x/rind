// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// Eight SHA-256 hashes, each continuing chaining value `state` over one of
/// `messages`, padded and closed by `length`, one at a time. `messages`
/// holds one to eight; the digests past them are zero.
pub(crate) fn sha256_finish_x8(
    state: &[u32; 8],
    messages: &[&[u8]],
    length: [u8; 8],
) -> [[u8; 32]; 8] {
    let mut digests = [[0u8; 32]; 8];
    for (digest, message) in digests.iter_mut().zip(messages) {
        *digest = crate::low::sha256_finish(state, message, length);
    }
    digests
}
