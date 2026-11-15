// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::hint::black_box;
use core::mem::ManuallyDrop;

use crate::Error;
use crate::cipher::Algorithm;
use crate::low::{self, AesDecKey, AesKey, Entry, Zeroable, ct_equal, zeroise_value};

/// RFC 3394's default initial value, which unwrapping checks.
const IV: [u8; 8] = [0xa6; 8];

/// RFC 5649's alternative initial value, which the key's length follows.
const AIV: [u8; 4] = [0xa6, 0x59, 0x59, 0xa6];

/// An AES key-encryption key, which wraps and unwraps other keys with RFC
/// 3394 AES-KW, or with RFC 5649 AES-KWP for keys of any length; wiped on
/// drop.
///
/// Wrapping is deterministic and authenticated: a wrapped key that was
/// altered fails to unwrap.
///
/// Each call expands the schedule it needs, as aws-lc does: a KEK usually
/// wraps or unwraps once, as pyca's functions and JWE use it, and holding
/// both schedules would cost that call a second expansion.
pub struct AesKek {
    key: [u8; 32],
    key_len: usize,
}

impl AesKek {
    /// Expands `key` for `algorithm`, failing with [`Error::WrongLength`] if
    /// it is not that algorithm's key length.
    pub fn new(algorithm: &'static Algorithm, key: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        if key.len() != algorithm.key_len {
            return Err(Error::WrongLength);
        }
        // Mark a copy: the caller's buffer may be shared, or a promoted constant.
        let mut copy = [0u8; 32];
        copy[..key.len()].copy_from_slice(key);
        low::ct::secret_slice(&copy);
        Ok(Self {
            key: copy,
            key_len: key.len(),
        })
    }

    fn key(&self) -> &[u8] {
        &self.key[..self.key_len]
    }

    /// Wraps `key` into `wrapped`, which must be 8 bytes longer.
    ///
    /// Fails with [`Error::WrongLength`], leaving `wrapped` unchanged, if
    /// `key` is shorter than 16 bytes or not a multiple of 8, or `wrapped` is
    /// not 8 bytes longer.
    pub fn wrap(&self, key: &[u8], wrapped: &mut [u8]) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        if key.len() < 16 || !key.len().is_multiple_of(8) || wrapped.len() != key.len() + 8 {
            return Err(Error::WrongLength);
        }
        let (a, r) = wrapped.split_at_mut(8);
        r.copy_from_slice(key);
        low::ct::secret_slice(r);

        // Expanded for this call, so it skips its wipe.
        let aes = ManuallyDrop::new(AesKey::new(self.key()));
        a.copy_from_slice(&wrap_blocks(&aes, IV, r.as_chunks_mut().0));

        low::ct::public_slice(wrapped);
        Ok(())
    }

    /// Unwraps `wrapped` into `key`, which must be 8 bytes shorter.
    ///
    /// Fails with [`Error::DecryptFailed`] if `wrapped` was not wrapped by
    /// this key, clearing `key`, or is shorter than 24 bytes or not a
    /// multiple of 8, and with [`Error::WrongLength`] if `key` is not 8 bytes
    /// shorter; a length failure leaves `key` unchanged.
    pub fn unwrap(&self, wrapped: &[u8], key: &mut [u8]) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        if wrapped.len() < 24 || !wrapped.len().is_multiple_of(8) {
            return Err(Error::DecryptFailed);
        }
        if key.len() != wrapped.len() - 8 {
            return Err(Error::WrongLength);
        }
        let (a, c) = wrapped.split_at(8);
        key.copy_from_slice(c);

        // Expanded for this call, so it skips its wipe.
        let aes = ManuallyDrop::new(AesDecKey::new(self.key()));
        let a = unwrap_blocks(&aes, a.try_into().unwrap(), key.as_chunks_mut().0);

        if low::ct::into_public(ct_equal(&a, &IV)) {
            low::ct::public_slice(key);
            Ok(())
        } else {
            // avoid unauthenticated key leak
            key.fill(0x00);
            Err(Error::DecryptFailed)
        }
    }

    /// Wraps `key`, of any length from 1 byte, into `wrapped`, which must be
    /// `key.len().next_multiple_of(8) + 8` bytes long, with RFC 5649's
    /// padding.
    ///
    /// Fails with [`Error::WrongLength`], leaving `wrapped` unchanged, if
    /// `key` is empty or longer than `u32::MAX` bytes, or `wrapped` is not
    /// that length.
    pub fn wrap_padded(&self, key: &[u8], wrapped: &mut [u8]) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        let Ok(len) = u32::try_from(key.len()) else {
            return Err(Error::WrongLength);
        };
        if key.is_empty() || wrapped.len() != key.len().next_multiple_of(8) + 8 {
            return Err(Error::WrongLength);
        }
        let mut aiv = [0u8; 8];
        aiv[..4].copy_from_slice(&AIV);
        aiv[4..].copy_from_slice(&len.to_be_bytes());

        let (a, r) = wrapped.split_at_mut(8);
        let (r_key, r_pad) = r.split_at_mut(key.len());
        r_key.copy_from_slice(key);
        r_pad.fill(0);
        low::ct::secret_slice(r);

        // Expanded for this call, so it skips its wipe.
        let aes = ManuallyDrop::new(AesKey::new(self.key()));
        if r.len() == 8 {
            // A single padded block is encrypted on its own, not wrapped.
            let mut block = [0u8; 16];
            block[..8].copy_from_slice(&aiv);
            block[8..].copy_from_slice(r);
            wrapped.copy_from_slice(&aes.encrypt_block(&block));
        } else {
            a.copy_from_slice(&wrap_blocks(&aes, aiv, r.as_chunks_mut().0));
        }

        low::ct::public_slice(wrapped);
        Ok(())
    }

    /// Unwraps `wrapped`, wrapped with RFC 5649's padding, into `key`, which
    /// must be 8 bytes shorter, returning the unwrapped key at its start.
    ///
    /// Fails with [`Error::DecryptFailed`] if `wrapped` was not wrapped by
    /// this key, clearing `key`, or is shorter than 16 bytes or not a
    /// multiple of 8, and with [`Error::WrongLength`] if `key` is not 8 bytes
    /// shorter; a length failure leaves `key` unchanged.
    pub fn unwrap_padded<'a>(
        &self,
        wrapped: &[u8],
        key: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        let _entry = Entry::new_secret();
        if wrapped.len() < 16 || !wrapped.len().is_multiple_of(8) {
            return Err(Error::DecryptFailed);
        }
        if key.len() != wrapped.len() - 8 {
            return Err(Error::WrongLength);
        }

        // Expanded for this call, so it skips its wipe.
        let aes = ManuallyDrop::new(AesDecKey::new(self.key()));
        let aiv = if key.len() == 8 {
            let mut block: [u8; 16] = wrapped.try_into().unwrap();
            aes.decrypt_block(&mut block);
            key.copy_from_slice(&block[8..]);
            *block.first_chunk().unwrap()
        } else {
            let (a, c) = wrapped.split_at(8);
            key.copy_from_slice(c);
            unwrap_blocks(&aes, a.try_into().unwrap(), key.as_chunks_mut().0)
        };

        // Valid if the AIV's constant matches, the claimed length ends in the
        // last block, and every byte after it is zero, checked without
        // branching on any. Each folds into the one word revealed, since the
        // compiler splits `a & b` of two bools into a branch on each.
        let claimed = u64::from(u32::from_be_bytes(*aiv.last_chunk().unwrap()));
        let mut bad = black_box((key.len() as u64).wrapping_sub(claimed) >> 3);
        // Indexed rather than iterating `enumerate().skip()`, which Aeneas
        // cannot translate, so `proofs/` can prove it.
        #[allow(clippy::needless_range_loop)]
        for i in key.len() - 8..key.len() {
            // all ones if `i` is at or past the claimed length
            let past = ((i as u64).wrapping_sub(claimed) >> 63).wrapping_sub(1);
            bad |= black_box(past & u64::from(key[i]));
        }
        bad |= black_box(u64::from(!ct_equal(&aiv[..4], &AIV)));

        if low::ct::into_public(black_box(bad)) == 0 {
            low::ct::public_slice(key);
            Ok(&mut key[..low::ct::into_public(claimed) as usize])
        } else {
            // avoid unauthenticated key leak
            key.fill(0x00);
            Err(Error::DecryptFailed)
        }
    }
}

impl fmt::Debug for AesKek {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AesKek")
            .field("algorithm", crate::cipher::aes(self.key_len))
            .finish_non_exhaustive()
    }
}

impl Drop for AesKek {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for AesKek {}

/// RFC 3394's wrapping of `r` in place under the initial value `a`,
/// returning the integrity value.
///
/// A stays in a register and each block is built afresh: copying it through
/// one buffer the cipher returns into put store-to-load round trips on the
/// serial chain, a few nanoseconds a block.
fn wrap_blocks(aes: &AesKey, a: [u8; 8], r: &mut [[u8; 8]]) -> [u8; 8] {
    let n = r.len() as u64;
    let mut a = u64::from_ne_bytes(a);
    for j in 0..6 {
        a = wrap_pass(aes, a, j * n, r);
    }
    a.to_ne_bytes()
}

/// One of wrapping's six passes over `r`, its steps counting from `t + 1`.
///
/// A function of its own, indexing `r`, since Aeneas translates neither a
/// loop nested in another that writes through a reference nor one over
/// `iter_mut`, so `proofs/` can prove it.
#[inline(always)]
#[allow(clippy::needless_range_loop)]
fn wrap_pass(aes: &AesKey, mut a: u64, mut t: u64, r: &mut [[u8; 8]]) -> u64 {
    for i in 0..r.len() {
        t += 1;
        let out = aes.encrypt_block(&block(a, &r[i]));
        a = u64::from_ne_bytes(*out.first_chunk().unwrap()) ^ t.to_be();
        r[i] = *out.last_chunk().unwrap();
    }
    a
}

/// RFC 3394's unwrapping of `r` in place from the integrity value `a`,
/// returning the initial value for the caller to check.
fn unwrap_blocks(aes: &AesDecKey, a: [u8; 8], r: &mut [[u8; 8]]) -> [u8; 8] {
    let n = r.len() as u64;
    let mut a = u64::from_ne_bytes(a);
    for j in 0..6 {
        a = unwrap_pass(aes, a, (6 - j) * n, r);
    }
    a.to_ne_bytes()
}

/// One of unwrapping's six passes over `r`, from its last block, its steps
/// counting down from `t`, as [`wrap_pass`] is shaped for Aeneas.
#[inline(always)]
fn unwrap_pass(aes: &AesDecKey, mut a: u64, mut t: u64, r: &mut [[u8; 8]]) -> u64 {
    for j in 0..r.len() {
        let i = r.len() - 1 - j;
        let mut b = block(a ^ t.to_be(), &r[i]);
        t -= 1;
        aes.decrypt_block(&mut b);
        a = u64::from_ne_bytes(*b.first_chunk().unwrap());
        r[i] = *b.last_chunk().unwrap();
    }
    a
}

/// A, in native byte order, followed by R[i].
#[inline]
fn block(a: u64, r_i: &[u8; 8]) -> [u8; 16] {
    let mut block = [0u8; 16];
    block[..8].copy_from_slice(&a.to_ne_bytes());
    block[8..].copy_from_slice(r_i);
    block
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::cipher::{AES_128, AES_192, AES_256};
    use crate::test::{Acvp, acvp};

    #[test]
    fn acvp_kw() {
        acvp_set("ACVP-AES-KW-1.0", false);
    }

    #[test]
    fn acvp_kwp() {
        acvp_set("ACVP-AES-KWP-1.0", true);
    }

    fn acvp_set(name: &str, padded: bool) {
        for group in acvp(name) {
            assert_eq!(group.str("kwCipher"), "cipher");
            let encrypt = match group.str("direction") {
                "encrypt" => true,
                "decrypt" => false,
                other => panic!("unexpected direction {other}"),
            };
            for test in group.tests() {
                let key = test.hex("key");
                let kek = AesKek::new(crate::cipher::aes(key.len()), &key).unwrap();
                let ct = test.hex("ct");
                if encrypt {
                    let mut wrapped = vec![0; ct.len()];
                    if padded {
                        kek.wrap_padded(&test.hex("pt"), &mut wrapped)
                    } else {
                        kek.wrap(&test.hex("pt"), &mut wrapped)
                    }
                    .unwrap();
                    assert_eq!(wrapped, ct);
                    continue;
                }
                let mut unwrapped = vec![0; ct.len() - 8];
                let result = if padded {
                    kek.unwrap_padded(&ct, &mut unwrapped)
                        .map(|key| key.to_vec())
                } else {
                    kek.unwrap(&ct, &mut unwrapped).map(|()| unwrapped)
                };
                match test.flag("testPassed") {
                    true => assert_eq!(result.unwrap(), test.hex("pt")),
                    false => assert_eq!(result, Err(Error::DecryptFailed)),
                }
            }
        }
    }

    // RFC 3394 sections 4.1, 4.2, 4.4, and 4.6: a key under each KEK size,
    // the smallest and largest among them, both ways.
    #[test]
    fn rfc3394() {
        for (algorithm, kek, key, wrapped) in [
            (
                &AES_128,
                "000102030405060708090a0b0c0d0e0f",
                "00112233445566778899aabbccddeeff",
                "1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe5",
            ),
            (
                &AES_192,
                "000102030405060708090a0b0c0d0e0f1011121314151617",
                "00112233445566778899aabbccddeeff",
                "96778b25ae6ca435f92b5b97c050aed2468ab8a17ad84e5d",
            ),
            (
                &AES_192,
                "000102030405060708090a0b0c0d0e0f1011121314151617",
                "00112233445566778899aabbccddeeff0001020304050607",
                "031d33264e15d33268f24ec260743edce1c6c7ddee725a936ba814915c6762d2",
            ),
            (
                &AES_256,
                "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
                "00112233445566778899aabbccddeeff000102030405060708090a0b0c0d0e0f",
                "28c9f404c4b810f4cbccb35cfb87f8263f5786e2d80ed326cbc7f0e71a99f43bfb988b9b7a02dd21",
            ),
        ] {
            let kek = AesKek::new(algorithm, &hex::decode(kek).unwrap()).unwrap();
            let key = hex::decode(key).unwrap();
            let wrapped = hex::decode(wrapped).unwrap();

            let mut out = vec![0u8; wrapped.len()];
            kek.wrap(&key, &mut out).unwrap();
            assert_eq!(out, wrapped);

            let mut out = vec![0u8; key.len()];
            kek.unwrap(&wrapped, &mut out).unwrap();
            assert_eq!(out, key);
        }
    }

    // RFC 5649's examples, section 6, and Wycheproof's KWP tests 15 and 185:
    // keys that pad to a single block, which is encrypted on its own, and
    // keys that pad to more, which are wrapped.
    #[test]
    fn rfc5649() {
        for (algorithm, kek, key, wrapped) in [
            (
                &AES_192,
                "5840df6e29b02af1ab493b705bf16ea1ae8338f4dcc176a8",
                "c37b7e6492584340bed12207808941155068f738",
                "138bdeaa9b8fa7fc61f97742e72248ee5ae6ae5360d1ae6a5f54f373fa543b6a",
            ),
            (
                &AES_192,
                "5840df6e29b02af1ab493b705bf16ea1ae8338f4dcc176a8",
                "466f7250617369",
                "afbeb0f07dfbf5419200f2ccb50bb24f",
            ),
            (
                &AES_128,
                "1abf4b7fa2bb62a78f09ddab04625dca",
                "0412ab3ec6",
                "0344f7b34ab8ef28aaa843f276b0b3d5",
            ),
            (
                &AES_256,
                "1abf4b7fa2bb62a78f09ddab04625dcacdd9e551d1a69b6b162baa53d2700093",
                "72aaee126a822184806c7d22eed66b",
                "de497acf18a177a3a9b3d8da46d74dfa58dcc537a3a95323",
            ),
        ] {
            let kek = AesKek::new(algorithm, &hex::decode(kek).unwrap()).unwrap();
            let key = hex::decode(key).unwrap();
            let wrapped = hex::decode(wrapped).unwrap();

            let mut out = vec![0u8; wrapped.len()];
            kek.wrap_padded(&key, &mut out).unwrap();
            assert_eq!(out, wrapped);

            let mut out = vec![0u8; wrapped.len() - 8];
            assert_eq!(kek.unwrap_padded(&wrapped, &mut out).unwrap(), key);
        }
    }

    // Every length from 1 to 24 round trips, and any altered byte, a claimed
    // length outside the last block, or a nonzero padding byte fails,
    // clearing the key.
    #[test]
    fn padded() {
        let kek = AesKek::new(&AES_128, &[0x42; 16]).unwrap();
        let enc = AesKey::new(&[0x42; 16]);
        let _entry = Entry::new_secret();
        for len in 1..=24usize {
            let key: Vec<u8> = (1..=len as u8).collect();
            let mut wrapped = vec![0u8; len.next_multiple_of(8) + 8];
            kek.wrap_padded(&key, &mut wrapped).unwrap();
            let mut out = vec![0xaa; wrapped.len() - 8];
            assert_eq!(kek.unwrap_padded(&wrapped, &mut out).unwrap(), key);

            for i in [0, 3, 4, 7, 8, wrapped.len() - 1] {
                let mut tampered = wrapped.clone();
                tampered[i] ^= 1;
                let mut out = vec![0xaa; wrapped.len() - 8];
                assert_eq!(
                    kek.unwrap_padded(&tampered, &mut out),
                    Err(Error::DecryptFailed)
                );
                assert!(out.iter().all(|b| *b == 0), "len {len} byte {i}");
            }

            // Rewrap the plaintext with a forged AIV, claiming each length
            // and the padding nonzero, as an attacker holding the KEK could.
            let padded = len.next_multiple_of(8);
            for claimed in [0, len - 1, len + 1, padded, padded + 1, padded - 8] {
                for pad_byte in [0u8, 1] {
                    let mut plain = key.clone();
                    plain.resize(padded, pad_byte);
                    let mut aiv = [0u8; 8];
                    aiv[..4].copy_from_slice(&AIV);
                    aiv[4..].copy_from_slice(&(claimed as u32).to_be_bytes());
                    let mut forged = vec![0u8; padded + 8];
                    if padded == 8 {
                        let mut block = [0u8; 16];
                        block[..8].copy_from_slice(&aiv);
                        block[8..].copy_from_slice(&plain);
                        forged.copy_from_slice(&enc.encrypt_block(&block));
                    } else {
                        forged[8..].copy_from_slice(&plain);
                        let a = wrap_blocks(&enc, aiv, forged[8..].as_chunks_mut().0);
                        forged[..8].copy_from_slice(&a);
                    }
                    // the forgery is well formed, and only the claimed
                    // length and padding decide
                    let valid = claimed > padded - 8
                        && claimed <= padded
                        && plain[claimed..].iter().all(|b| *b == 0);
                    let mut out = vec![0xaa; padded];
                    let result = kek.unwrap_padded(&forged, &mut out);
                    assert_eq!(
                        result.is_ok(),
                        valid,
                        "len {len} claimed {claimed} pad {pad_byte}"
                    );
                    if !valid {
                        assert!(out.iter().all(|b| *b == 0));
                    }
                }
            }
        }
    }

    #[test]
    fn unwrap_failure_clears_key() {
        let kek = AesKek::new(&AES_128, &[0x42; 16]).unwrap();
        let mut wrapped = [0u8; 40];
        kek.wrap(&[0x24; 32], &mut wrapped).unwrap();

        // every byte is covered, the integrity value and each key block
        for i in [0, 7, 8, 39] {
            let mut tampered = wrapped;
            tampered[i] ^= 1;
            let mut key = [0xaa; 32];
            assert_eq!(kek.unwrap(&tampered, &mut key), Err(Error::DecryptFailed));
            assert_eq!(key, [0; 32], "byte {i}");
        }
    }

    #[test]
    fn lengths() {
        let kek = AesKek::new(&AES_256, &[0x42; 32]).unwrap();
        let buf = [0x55u8; 64];
        for len in 0..=48usize {
            let valid = len >= 16 && len.is_multiple_of(8);
            let mut wrapped = vec![0xaa; len + 8];
            let result = kek.wrap(&buf[..len], &mut wrapped);
            assert_eq!(result.is_ok(), valid, "wrap {len}");
            if !valid {
                assert!(wrapped.iter().all(|b| *b == 0xaa), "refused wrap wrote");
            }

            // malformed, or well formed but not wrapped by this key
            let mut key = vec![0xaa; len.saturating_sub(8)];
            let result = kek.unwrap(&buf[..len], &mut key);
            assert_eq!(result, Err(Error::DecryptFailed), "unwrap {len}");
            if len < 24 || !len.is_multiple_of(8) {
                assert!(key.iter().all(|b| *b == 0xaa), "refused unwrap wrote");
            }
        }

        // the other buffer's length must match
        let mut wrapped = [0u8; 32];
        assert_eq!(kek.wrap(&buf[..16], &mut wrapped), Err(Error::WrongLength));
        kek.wrap(&buf[..24], &mut wrapped).unwrap();
        let mut key = [0u8; 16];
        assert_eq!(kek.unwrap(&wrapped, &mut key), Err(Error::WrongLength));

        // RFC 5649 wraps any key but an empty one, into exactly its padded
        // length plus 8.
        for len in 0..=48usize {
            let wanted = len.next_multiple_of(8) + 8;
            for out_len in [wanted - 1, wanted, wanted + 1, wanted + 8] {
                let mut wrapped = vec![0xaa; out_len];
                let result = kek.wrap_padded(&buf[..len], &mut wrapped);
                let valid = len > 0 && out_len == wanted;
                assert_eq!(result.is_ok(), valid, "wrap_padded {len} into {out_len}");
                if !valid {
                    assert_eq!(result, Err(Error::WrongLength));
                    assert!(
                        wrapped.iter().all(|b| *b == 0xaa),
                        "refused wrap_padded wrote"
                    );
                }
            }

            let mut key = vec![0xaa; len.saturating_sub(8)];
            let result = kek.unwrap_padded(&buf[..len], &mut key);
            assert_eq!(result, Err(Error::DecryptFailed), "unwrap_padded {len}");
            if len < 16 || !len.is_multiple_of(8) {
                assert!(
                    key.iter().all(|b| *b == 0xaa),
                    "refused unwrap_padded wrote"
                );
            }
        }
        let mut wrapped = [0u8; 16];
        kek.wrap_padded(&buf[..1], &mut wrapped).unwrap();
        for key_len in [7, 9, 16] {
            let mut key = vec![0u8; key_len];
            assert_eq!(
                kek.unwrap_padded(&wrapped, &mut key),
                Err(Error::WrongLength)
            );
        }

        assert!(AesKek::new(&AES_128, &[0; 32]).is_err());
        assert!(AesKek::new(&AES_256, &[0; 16]).is_err());
    }

    // armv7's AES-KW on the crypto extension, which valgrind hides, for each
    // key size, with a secret KEK and key, for `admin/ct-qemu`.
    #[cfg(rind_backend = "arm")]
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu-arm"]
    fn ct_qemu_aes_kw() {
        use crate::low::ct_qemu;

        let seed = ct_qemu::seed().to_le_bytes();
        let bytes = |n| seed.iter().cycle().take(n).copied().collect::<Vec<u8>>();
        for algorithm in [&AES_128, &AES_192, &AES_256] {
            let kek_bytes = bytes(algorithm.key_len);
            let kek = ct_qemu::traced(|| AesKek::new(algorithm, &kek_bytes).unwrap());
            assert!(
                matches!(AesDecKey::new(kek.key()), AesDecKey::Hw(_)),
                "the crypto extension"
            );

            let key = bytes(32);
            let mut wrapped = [0u8; 40];
            ct_qemu::traced(|| kek.wrap(&key, &mut wrapped)).unwrap();
            let mut unwrapped = [0u8; 32];
            ct_qemu::traced(|| kek.unwrap(&wrapped, &mut unwrapped)).unwrap();

            // one block, encrypted on its own, and several, wrapped
            for len in [5usize, 31] {
                let mut wrapped = [0u8; 40];
                let wrapped = &mut wrapped[..len.next_multiple_of(8) + 8];
                ct_qemu::traced(|| kek.wrap_padded(&key[..len], wrapped)).unwrap();
                let mut unwrapped = [0u8; 32];
                let unwrapped = &mut unwrapped[..wrapped.len() - 8];
                ct_qemu::traced(|| kek.unwrap_padded(wrapped, unwrapped).map(|k| k.len())).unwrap();
            }
        }
    }
}
