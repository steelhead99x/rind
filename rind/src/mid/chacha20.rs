// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::low::{self, Entry, zeroise};

/// A ChaCha20 key, for the bare stream cipher with a 96-bit nonce and a 32-bit block counter.
///
/// See [RFC8439](https://datatracker.ietf.org/doc/html/rfc8439). Use it only
/// where a protocol specifies ChaCha20 without Poly1305, such as DTLS 1.3
/// record number protection; QUIC header protection has [`crate::aead::quic`].
pub struct ChaCha20 {
    key: [u8; 32],
}

impl ChaCha20 {
    /// Makes a key from 32 bytes of key material.
    pub fn new(key: &[u8; 32]) -> Self {
        Self {
            key: low::ct::into_secret(*key),
        }
    }

    /// XORs the keystream for `nonce`, starting at block `counter`, into `inout`.
    ///
    /// Encryption and decryption are the same operation. The nonce and counter
    /// are not secret. Each call starts at a whole block, so a stream split
    /// after a length that is not a multiple of 64 cannot resume mid-block:
    /// passing that partial block's counter again reuses keystream.
    ///
    /// Fails with [`Error::WrongLength`], leaving `inout` unchanged, if `inout`
    /// needs more blocks than remain before the counter wraps: wrapping would
    /// repeat keystream.
    pub fn apply_keystream(
        &self,
        nonce: &[u8; 12],
        counter: u32,
        inout: &mut [u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        check_counter(counter, inout.len())?;
        low::ct::secret_slice(inout);

        let mut counter_nonce = [0u8; 16];
        counter_nonce[..4].copy_from_slice(&counter.to_le_bytes());
        counter_nonce[4..].copy_from_slice(nonce);
        low::chacha20::ChaCha20::new(&self.key, &counter_nonce).cipher(inout);

        low::ct::public_slice(inout);
        Ok(())
    }

    /// The QUIC header-protection mask for `sample` (RFC 9001 section 5.4.4).
    ///
    /// The sample is a block's little-endian counter then nonce, and one block
    /// never wraps the counter, so this cannot fail.
    pub(crate) fn header_protection_mask(&self, sample: &[u8; 16]) -> [u8; 5] {
        let _entry = Entry::new_secret();
        let block = low::chacha20_block(&self.key, sample);
        let mask = [block[0], block[1], block[2], block[3], block[4]];
        low::ct::public_slice(&mask);
        mask
    }
}

/// Fails with [`Error::WrongLength`] if `len` bytes need more blocks than
/// remain from block `counter` before the 32-bit counter wraps.
pub(super) fn check_counter(counter: u32, len: usize) -> Result<(), Error> {
    if u64::from(counter) + len.div_ceil(64) as u64 > 1 << 32 {
        return Err(Error::WrongLength);
    }
    Ok(())
}

impl fmt::Debug for ChaCha20 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChaCha20").finish_non_exhaustive()
    }
}

impl Drop for ChaCha20 {
    fn drop(&mut self) {
        zeroise(&mut self.key);
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn rfc8439() {
        // section 2.4.2: two blocks and a partial third, from counter 1
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let nonce = hex::decode("000000000000004a00000000").unwrap();
        let mut buf = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.".to_vec();

        ChaCha20::new(&key)
            .apply_keystream(&nonce.try_into().unwrap(), 1, &mut buf)
            .unwrap();

        assert_eq!(
            hex::encode(&buf),
            "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0b\
             f91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d8\
             07ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab7793736\
             5af90bbf74a35be6b40b8eedf2785e42874d"
        );
    }

    /// At the counter's end, a request that `cipher` splits between
    /// verified-garbage's routines and the kernel, where the CPU has AVX2,
    /// matches block-by-block encryption on HACL*'s rounds, and one byte more
    /// is refused with the buffer unchanged.
    #[test]
    fn counter_end() {
        let key = ChaCha20::new(&[7; 32]);
        let nonce = [9; 12];
        let start = u32::MAX - 9;
        let msg: Vec<u8> = (0..641).map(|i| i as u8).collect();

        let mut want = msg[..640].to_vec();
        for (i, block) in want.chunks_mut(64).enumerate() {
            key.apply_keystream(&nonce, start + i as u32, block)
                .unwrap();
        }
        let mut got = msg[..640].to_vec();
        key.apply_keystream(&nonce, start, &mut got).unwrap();
        assert_eq!(got, want);

        let mut past = msg.clone();
        assert_eq!(
            key.apply_keystream(&nonce, start, &mut past),
            Err(Error::WrongLength)
        );
        assert_eq!(past, msg);
    }

    #[test]
    fn counter_limits() {
        assert_eq!(check_counter(u32::MAX, 64), Ok(()));
        assert_eq!(check_counter(u32::MAX, 65), Err(Error::WrongLength));

        // the AEADs start at block 1, after the Poly1305 key's
        #[cfg(target_pointer_width = "64")]
        {
            let max_aead = ((1 << 32) - 1) * 64;
            assert_eq!(check_counter(1, max_aead), Ok(()));
            assert_eq!(check_counter(1, max_aead + 1), Err(Error::WrongLength));
        }
    }
}
