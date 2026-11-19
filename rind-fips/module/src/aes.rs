// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES: the block cipher, CTR, and CBC (SP 800-38A), key wrapping (SP
//! 800-38F), QUIC header protection, and AES-GCM (SP 800-38D).
//!
//! AES-GCM seals here only under an IV the module generates, as IG C.H
//! requires: one drawn whole from the DRBG (scenario 2), or a TLS 1.3
//! record's, whose sequence number the module manages (scenario 5).
//! Opening takes the sender's IV, to which IG C.H does not apply.
//!
//! A seal that fails zeroes its buffer, as aws-lc's does, so a caller that
//! ignores the error sends no plaintext.

use core::sync::atomic::{AtomicU64, Ordering};

use rind::aead::{self, gcm, quic};
use rind::cipher::{self, Aes, AesCbcDecryptingKey, AesCbcEncryptingKey, AesCtr, CbcIv};
use rind::key_wrap::{AesKek, Mode};
use rind::{Error, hkdf};

use crate::abi::{Bytes, Status, byte_list, bytes, bytes_mut, free, handle, put, status};
use crate::ids;
use crate::scrub::{Depth, scrubbed};
use crate::selftest::{SelfTest, ensure};

/// The AES key size `id` names, after the block cipher's self-test.
fn cipher_algorithm(id: u32) -> Result<&'static cipher::Algorithm, Error> {
    let algorithm = aes_key_size(id)?;
    ensure(&[SelfTest::Aes]);
    Ok(algorithm)
}

/// The AES key size `id` names.
fn aes_key_size(id: u32) -> Result<&'static cipher::Algorithm, Error> {
    match id {
        ids::aes::AES_128 => Ok(&cipher::AES_128),
        ids::aes::AES_192 => Ok(&cipher::AES_192),
        ids::aes::AES_256 => Ok(&cipher::AES_256),
        _ => Err(Error::Unsupported),
    }
}

/// The AES-GCM algorithm `id` names, after its self-test.
fn aead_algorithm(id: u32) -> Option<&'static aead::Algorithm> {
    let algorithm = match id {
        ids::aead::AES_128_GCM => &aead::AES_128_GCM,
        ids::aead::AES_192_GCM => &aead::AES_192_GCM,
        ids::aead::AES_256_GCM => &aead::AES_256_GCM,
        _ => return None,
    };
    ensure(&[SelfTest::AesGcm]);
    Some(algorithm)
}

/// The QUIC header-protection algorithm the AES key size `id` names, after
/// the block cipher's self-test.
fn quic_algorithm(id: u32) -> Option<&'static quic::Algorithm> {
    let algorithm = match id {
        ids::aes::AES_128 => &quic::AES_128,
        ids::aes::AES_256 => &quic::AES_256,
        _ => return None,
    };
    ensure(&[SelfTest::Aes]);
    Some(algorithm)
}

/// The AES-GCM tag length of `bytes`.
fn tag_length(bytes: usize) -> Result<gcm::TagLength, Error> {
    use gcm::TagLength::*;
    Ok(match bytes {
        16 => Full,
        15 => Truncated120,
        14 => Truncated112,
        13 => Truncated104,
        12 => Truncated96,
        8 => Truncated64,
        4 => Truncated32,
        _ => return Err(Error::WrongLength),
    })
}

/// Writes a handle to what `make` returns to `out`, zeroing the stack it
/// used, or the status of its error.
///
/// # Safety
/// `out` must be valid for a write.
unsafe fn new_handle<T>(out: *mut *mut T, make: impl FnOnce() -> Result<T, Error>) -> Status {
    scrubbed(Depth::Small, || {
        status(make().map(|value| {
            // SAFETY: the caller's contract.
            unsafe { put(out, handle(value)) }
        }))
    })
}

/// Expands the `len` bytes at `key` with `make` for the AES key size `id`,
/// writing the handle to `out`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
unsafe fn new_cipher<T>(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut T,
    make: impl FnOnce(&'static cipher::Algorithm, &[u8]) -> Result<T, Error>,
) -> Status {
    let algorithm = match cipher_algorithm(id) {
        Ok(algorithm) => algorithm,
        Err(error) => return status(Err(error)),
    };
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    // SAFETY: the caller's contract.
    unsafe { new_handle(out, || make(algorithm, key)) }
}

/// An AES key that encrypts single blocks, for the AES key size `id`, from
/// the `len` bytes at `key`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut Aes,
) -> Status {
    // SAFETY: the caller's contract.
    unsafe { new_cipher(id, key, len, out, Aes::new) }
}

/// Encrypts the 16 bytes at `block` in place.
///
/// # Safety
/// `key` must be live, and `block` valid for 16 reads and writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_encrypt_block(key: *const Aes, block: *mut [u8; 16]) {
    // SAFETY: the caller's contract.
    let (key, block) = unsafe { (&*key, &mut *block) };
    scrubbed(Depth::Small, || key.encrypt_block(block))
}

/// An AES-CTR key for the AES key size `id`, from the `len` bytes at `key`,
/// counting over the rightmost `counter_bits` bits of each counter block.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_ctr_new(
    id: u32,
    key: *const u8,
    len: usize,
    counter_bits: u8,
    out: *mut *mut AesCtr,
) -> Status {
    // SAFETY: the caller's contract.
    unsafe {
        new_cipher(id, key, len, out, |algorithm, key| {
            AesCtr::new(algorithm, key, counter_bits)
        })
    }
}

/// XORs the keystream from the 16 bytes at `counter_block` into the `len`
/// bytes at `in_out`.
///
/// # Safety
/// `key` must be live, `counter_block` valid for 16 reads, and `in_out` for
/// `len` reads and writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_ctr_apply(
    key: *const AesCtr,
    counter_block: *const [u8; 16],
    in_out: *mut u8,
    len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, counter_block, in_out) = unsafe { (&*key, &*counter_block, bytes_mut(in_out, len)) };
    scrubbed(Depth::Small, || {
        status(key.apply_keystream(counter_block, in_out))
    })
}

/// An AES-CBC encrypting key for the AES key size `id`, from the `len`
/// bytes at `key`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_cbc_encrypting_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut AesCbcEncryptingKey,
) -> Status {
    // SAFETY: the caller's contract.
    unsafe { new_cipher(id, key, len, out, AesCbcEncryptingKey::new) }
}

/// Encrypts the `len` bytes at `in_out`, whole blocks, in place under the
/// 16-byte IV at `iv`, without padding.
///
/// # Safety
/// `key` must be live, `iv` valid for 16 reads, and `in_out` for `len`
/// reads and writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_cbc_encrypt_blocks(
    key: *const AesCbcEncryptingKey,
    iv: *const [u8; 16],
    in_out: *mut u8,
    len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, iv, in_out) = unsafe { (&*key, *iv, bytes_mut(in_out, len)) };
    scrubbed(Depth::Small, || {
        status(key.encrypt_blocks(CbcIv::assume_unpredictable(iv), in_out))
    })
}

/// An AES-CBC decrypting key for the AES key size `id`, from the `len`
/// bytes at `key`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_cbc_decrypting_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut AesCbcDecryptingKey,
) -> Status {
    // SAFETY: the caller's contract.
    unsafe { new_cipher(id, key, len, out, AesCbcDecryptingKey::new) }
}

/// Decrypts the `len` bytes at `in_out` in place under the 16-byte IV at
/// `iv`, checks and removes its PKCS#7 padding, and writes the plaintext's
/// length to `plaintext_len`.
///
/// # Safety
/// `key` must be live, `iv` valid for 16 reads, `in_out` for `len` reads
/// and writes, and `plaintext_len` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_cbc_decrypt(
    key: *const AesCbcDecryptingKey,
    iv: *const [u8; 16],
    in_out: *mut u8,
    len: usize,
    plaintext_len: *mut usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, iv, in_out) = unsafe { (&*key, &*iv, bytes_mut(in_out, len)) };
    scrubbed(Depth::Small, || {
        status(key.decrypt(iv, in_out).map(|plaintext| {
            // SAFETY: the caller's contract.
            unsafe { put(plaintext_len, plaintext.len()) }
        }))
    })
}

/// Decrypts the `len` bytes at `in_out`, whole blocks, in place under the
/// 16-byte IV at `iv`, without padding.
///
/// # Safety
/// `key` must be live, `iv` valid for 16 reads, and `in_out` for `len`
/// reads and writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_cbc_decrypt_blocks(
    key: *const AesCbcDecryptingKey,
    iv: *const [u8; 16],
    in_out: *mut u8,
    len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, iv, in_out) = unsafe { (&*key, &*iv, bytes_mut(in_out, len)) };
    scrubbed(Depth::Small, || status(key.decrypt_blocks(iv, in_out)))
}

free!(rind_fips_aes_free, Aes);
free!(rind_fips_aes_ctr_free, AesCtr);
free!(rind_fips_aes_cbc_encrypting_free, AesCbcEncryptingKey);
free!(rind_fips_aes_cbc_decrypting_free, AesCbcDecryptingKey);

/// An AES key-encryption key for the AES key size `id`, from the `len`
/// bytes at `key`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_kek_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut AesKek,
) -> Status {
    // SAFETY: the caller's contract.
    unsafe { new_cipher(id, key, len, out, AesKek::new) }
}

/// Wraps the `key_len` bytes at `key` into the `wrapped_len` bytes at
/// `wrapped` with AES-KW.
///
/// # Safety
/// `kek` must be live, `key` valid for `key_len` reads, and `wrapped` for
/// `wrapped_len` writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_kek_wrap(
    kek: *const AesKek,
    key: *const u8,
    key_len: usize,
    wrapped: *mut u8,
    wrapped_len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (kek, key, wrapped) =
        unsafe { (&*kek, bytes(key, key_len), bytes_mut(wrapped, wrapped_len)) };
    scrubbed(Depth::Small, || {
        status(kek.wrap_key(Mode::Kw, key, wrapped))
    })
}

/// Unwraps the `wrapped_len` bytes at `wrapped` into the `key_len` bytes
/// at `key` with AES-KW.
///
/// # Safety
/// `kek` must be live, `wrapped` valid for `wrapped_len` reads, and `key`
/// for `key_len` writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_kek_unwrap(
    kek: *const AesKek,
    wrapped: *const u8,
    wrapped_len: usize,
    key: *mut u8,
    key_len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (kek, wrapped, key) =
        unsafe { (&*kek, bytes(wrapped, wrapped_len), bytes_mut(key, key_len)) };
    scrubbed(Depth::Small, || {
        status(kek.unwrap_key(Mode::Kw, wrapped, key).map(|_| ()))
    })
}

/// Wraps the `key_len` bytes at `key` into the `wrapped_len` bytes at
/// `wrapped` with AES-KWP.
///
/// # Safety
/// As for [`rind_fips_aes_kek_wrap`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_kek_wrap_padded(
    kek: *const AesKek,
    key: *const u8,
    key_len: usize,
    wrapped: *mut u8,
    wrapped_len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (kek, key, wrapped) =
        unsafe { (&*kek, bytes(key, key_len), bytes_mut(wrapped, wrapped_len)) };
    scrubbed(Depth::Small, || {
        status(kek.wrap_key(Mode::Kwp, key, wrapped))
    })
}

/// Unwraps the `wrapped_len` bytes at `wrapped` into the `key_len` bytes
/// at `key` with AES-KWP, writing the unwrapped key's length to
/// `unwrapped_len`.
///
/// # Safety
/// As for [`rind_fips_aes_kek_unwrap`], and `unwrapped_len` must be valid
/// for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aes_kek_unwrap_padded(
    kek: *const AesKek,
    wrapped: *const u8,
    wrapped_len: usize,
    key: *mut u8,
    key_len: usize,
    unwrapped_len: *mut usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (kek, wrapped, key) =
        unsafe { (&*kek, bytes(wrapped, wrapped_len), bytes_mut(key, key_len)) };
    scrubbed(Depth::Small, || {
        status(kek.unwrap_key(Mode::Kwp, wrapped, key).map(|unwrapped| {
            // SAFETY: the caller's contract.
            unsafe { put(unwrapped_len, unwrapped.len()) }
        }))
    })
}

free!(rind_fips_aes_kek_free, AesKek);

/// An AES-GCM key for the algorithm `id` names, from the `len` bytes at
/// `key`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aead_key_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut aead::Key,
) -> Status {
    let Some(algorithm) = aead_algorithm(id) else {
        return status(Err(Error::Unsupported));
    };
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    // SAFETY: the caller's contract.
    unsafe { new_handle(out, || aead::Key::new(algorithm, key)) }
}

/// Decrypts and verifies the `len` bytes at `in_out` in place against the
/// 16-byte tag at `tag`, under the 12-byte nonce at `nonce` and the
/// `aad_len` bytes at `aad`.
///
/// # Safety
/// `key` must be live, `nonce` valid for 12 reads, `aad` for `aad_len`,
/// `tag` for 16, and `in_out` for `len` reads and writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aead_open(
    key: *const aead::Key,
    nonce: *const [u8; 12],
    aad: *const u8,
    aad_len: usize,
    tag: *const [u8; 16],
    in_out: *mut u8,
    len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, nonce, aad, tag, in_out) = unsafe {
        (
            &*key,
            *nonce,
            bytes(aad, aad_len),
            &*tag,
            bytes_mut(in_out, len),
        )
    };
    scrubbed(Depth::Small, || status(open(key, nonce, aad, tag, in_out)))
}

/// Opens `in_out` under `key`, as every AES-GCM key with 96-bit nonces does.
fn open(
    key: &aead::Key,
    nonce: [u8; 12],
    aad: &[u8],
    tag: &[u8; 16],
    in_out: &mut [u8],
) -> Result<(), Error> {
    let nonce = aead::Nonce::assume_unique_for_key(nonce);
    let tag = aead::Tag::try_from(&tag[..])?;
    key.open_in_place_separate_tag(nonce, aad, tag, in_out)
        .map(|_| ())
}

/// Seals `in_out` under `key` and `nonce`, writing the tag to `tag`.
fn seal(
    key: &aead::Key,
    nonce: [u8; 12],
    aad: &[u8],
    in_out: &mut [u8],
    tag: &mut [u8; 16],
) -> Result<(), Error> {
    let nonce = aead::Nonce::assume_unique_for_key(nonce);
    let sealed = key.seal_in_place_separate_tag(nonce, aad, in_out)?;
    tag.copy_from_slice(sealed.as_ref());
    Ok(())
}

/// `result`'s status, zeroing `in_out` if it failed.
fn sealed(result: Result<(), Error>, in_out: &mut [u8]) -> Status {
    if result.is_err() {
        in_out.fill(0);
    }
    status(result)
}

free!(rind_fips_aead_key_free, aead::Key);

/// How many messages one key may seal under random IVs: SP 800-38D section
/// 8.3's bound, which keeps the chance that two 96-bit IVs collide near
/// 2^-32 (IG C.H, additional comment 3). The break build lowers it so a
/// test reaches it.
const RANDOM_IV_SEALS: u64 = if cfg!(rind_fips_break) {
    1 << 10
} else {
    1 << 32
};

/// An AES-GCM key that seals only under IVs drawn whole from the DRBG (IG
/// C.H scenario 2), counting its seals to refuse those past
/// [`RANDOM_IV_SEALS`].
pub struct RandomIvKey {
    key: aead::Key,
    sealed: AtomicU64,
}

/// An AES-GCM key that seals under random IVs, for the algorithm `id`
/// names, from the `len` bytes at `key`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aead_random_key_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut RandomIvKey,
) -> Status {
    let Some(algorithm) = aead_algorithm(id) else {
        return status(Err(Error::Unsupported));
    };
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    // SAFETY: the caller's contract.
    unsafe {
        new_handle(out, || {
            Ok(RandomIvKey {
                key: aead::Key::new(algorithm, key)?,
                sealed: AtomicU64::new(0),
            })
        })
    }
}

/// Encrypts the `len` bytes at `in_out` in place under a 96-bit IV drawn
/// from the DRBG and the `aad_len` bytes at `aad`, writing the IV to
/// `nonce` and the tag to `tag`.
///
/// # Safety
/// `key` must be live, `aad` valid for `aad_len` reads, `in_out` for `len`
/// reads and writes, `nonce` for 12 writes, and `tag` for 16.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aead_random_seal(
    key: *const RandomIvKey,
    aad: *const u8,
    aad_len: usize,
    in_out: *mut u8,
    len: usize,
    nonce: *mut [u8; 12],
    tag: *mut [u8; 16],
) -> Status {
    // SAFETY: the caller's contract.
    let (key, aad, in_out) = unsafe { (&*key, bytes(aad, aad_len), bytes_mut(in_out, len)) };
    // The draw reaches the DRBG, whose stack is deeper than AES-GCM's.
    scrubbed(Depth::Medium, || {
        // Counted before sealing, so threads sealing at once never pass the
        // bound between them; a seal that then fails spends its count.
        if key.sealed.fetch_add(1, Ordering::Relaxed) >= RANDOM_IV_SEALS {
            return sealed(Err(Error::MessageLimitReached), in_out);
        }
        let mut iv = [0u8; 12];
        let mut sealed_tag = [0u8; 16];
        let result = rind::rand::fill(&mut iv)
            .and_then(|()| seal(&key.key, iv, aad, in_out, &mut sealed_tag));
        if result.is_ok() {
            // SAFETY: the caller's contract.
            unsafe {
                put(nonce, iv);
                put(tag, sealed_tag);
            }
        }
        sealed(result, in_out)
    })
}

/// Decrypts and verifies the `len` bytes at `in_out` in place, as
/// [`rind_fips_aead_open`] does, under a key that seals with random IVs.
///
/// # Safety
/// As for [`rind_fips_aead_open`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_aead_random_open(
    key: *const RandomIvKey,
    nonce: *const [u8; 12],
    aad: *const u8,
    aad_len: usize,
    tag: *const [u8; 16],
    in_out: *mut u8,
    len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, nonce, aad, tag, in_out) = unsafe {
        (
            &(*key).key,
            *nonce,
            bytes(aad, aad_len),
            &*tag,
            bytes_mut(in_out, len),
        )
    };
    scrubbed(Depth::Small, || status(open(key, nonce, aad, tag, in_out)))
}

free!(rind_fips_aead_random_key_free, RandomIvKey);

/// A TLS 1.3 record sealing key, the IV unit of IG C.H scenario 5: it
/// seals a record only if its sequence number, the nonce's last eight
/// bytes XORed with the first nonce's, is above every one sealed before
/// and below 2^64 - 1, so the sequence never repeats or wraps (RFC 8446
/// section 5.3).
///
/// As aws-lc's TLS 1.3 AEAD does, it learns `write_iv` from the first
/// nonce, whose sequence number is 0, rather than taking it, so a caller
/// that builds each nonce from the IV, as rustls does, makes no other call.
pub struct Tls13SealingKey {
    key: aead::Key,
    /// `write_iv`'s last eight bytes, once the first record is sealed.
    mask: Option<u64>,
    /// The lowest sequence number the next record may take.
    next: u64,
}

impl Tls13SealingKey {
    /// Takes `nonce`'s sequence number, refusing one not above the last.
    fn take(&mut self, nonce: &[u8; 12]) -> Result<(), Error> {
        let given = u64::from_be_bytes(*nonce.last_chunk().unwrap());
        let seq = given ^ *self.mask.get_or_insert(given);
        if seq == u64::MAX || seq < self.next {
            return Err(Error::MessageLimitReached);
        }
        self.next = seq + 1;
        Ok(())
    }
}

/// A TLS 1.3 record sealing key for the algorithm `id` names, AES-128-GCM
/// or AES-256-GCM as TLS 1.3's cipher suites take them, from the `len`
/// bytes at `key`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_tls13_sealing_key_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut Tls13SealingKey,
) -> Status {
    let algorithm = match id {
        ids::aead::AES_128_GCM | ids::aead::AES_256_GCM => aead_algorithm(id),
        _ => None,
    };
    let Some(algorithm) = algorithm else {
        return status(Err(Error::Unsupported));
    };
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    // SAFETY: the caller's contract.
    unsafe {
        new_handle(out, || {
            Ok(Tls13SealingKey {
                key: aead::Key::new(algorithm, key)?,
                mask: None,
                next: 0,
            })
        })
    }
}

/// Encrypts the `len` bytes at `in_out` in place under the 12-byte nonce
/// at `nonce` and the `aad_len` bytes at `aad`, writing the tag to `tag`,
/// if the nonce's sequence number is above the last one sealed.
///
/// # Safety
/// `key` must be live and in no other call, `nonce` valid for 12 reads,
/// `aad` for `aad_len`, `in_out` for `len` reads and writes, and `tag` for
/// 16 writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_tls13_seal(
    key: *mut Tls13SealingKey,
    nonce: *const [u8; 12],
    aad: *const u8,
    aad_len: usize,
    in_out: *mut u8,
    len: usize,
    tag: *mut [u8; 16],
) -> Status {
    // SAFETY: the caller's contract.
    let (key, nonce, aad, in_out) = unsafe {
        (
            &mut *key,
            *nonce,
            bytes(aad, aad_len),
            bytes_mut(in_out, len),
        )
    };
    scrubbed(Depth::Small, || {
        // As in aws-lc, a seal that then fails spends its sequence number.
        let mut sealed_tag = [0u8; 16];
        let result = key
            .take(&nonce)
            .and_then(|()| seal(&key.key, nonce, aad, in_out, &mut sealed_tag));
        if result.is_ok() {
            // SAFETY: the caller's contract.
            unsafe { put(tag, sealed_tag) };
        }
        sealed(result, in_out)
    })
}

free!(rind_fips_tls13_sealing_key_free, Tls13SealingKey);

/// A QUIC packet sealing key: AES-GCM under the nonce the module builds
/// itself, the packet protection IV XORed with the packet number (RFC 9001
/// section 5.3), for each packet number once.
///
/// QUIC may seal packets out of order (a sender seals packet `n + 1` while
/// another thread still seals `n`), so the module does not demand increasing
/// packet numbers, as [`Tls13SealingKey`] does. It remembers instead which of
/// the last [`Self::WINDOW`] packet numbers it has sealed and refuses a
/// repeat, and any packet number that far below the highest, which it can no
/// longer vouch for. Under one key a nonce is therefore never used twice,
/// whatever the order of calls: SP 800-38D section 8.2.1's requirement that
/// the invocation field is unique, which holds for any bijective mapping
/// from packet number to nonce, as XOR with a fixed IV is.
pub struct QuicSealingKey {
    key: aead::Key,
    iv: [u8; 12],
    /// The highest packet number sealed, if any.
    top: Option<u64>,
    /// Bit `n % WINDOW` is set if packet number `n`, within `WINDOW` of
    /// `top`, was sealed.
    seen: [u64; Self::WINDOW / 64],
}

impl QuicSealingKey {
    /// How far below the highest packet number sealed one may still be.
    const WINDOW: usize = 1024;

    /// Takes packet number `pn`, refusing one sealed before, one too far
    /// below the highest.
    fn take(&mut self, pn: u64) -> Result<(), Error> {
        let window = Self::WINDOW as u64;
        let slot = (pn % window) as usize;
        let (word, bit) = (slot / 64, 1u64 << (slot % 64));
        match self.top {
            None => {
                self.seen = [0; Self::WINDOW / 64];
                self.top = Some(pn);
            }
            Some(top) if pn > top => {
                // Slide the window: forget the packet numbers it leaves.
                let gone = (pn - top).min(window);
                for old in (top + 1)..=(top + gone) {
                    let slot = (old % window) as usize;
                    self.seen[slot / 64] &= !(1u64 << (slot % 64));
                }
                self.top = Some(pn);
            }
            Some(top) => {
                if top - pn >= window || self.seen[word] & bit != 0 {
                    return Err(Error::MessageLimitReached);
                }
            }
        }
        self.seen[word] |= bit;
        Ok(())
    }
}

/// A QUIC packet sealing key for the algorithm `id` names, AES-128-GCM or
/// AES-256-GCM, from the `len` bytes at `key`, with packet protection IV
/// `iv`.
///
/// # Safety
/// `key` must be valid for `len` reads, `iv` for 12, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_quic_sealing_key_new(
    id: u32,
    key: *const u8,
    len: usize,
    iv: *const [u8; 12],
    out: *mut *mut QuicSealingKey,
) -> Status {
    let algorithm = match id {
        ids::aead::AES_128_GCM | ids::aead::AES_256_GCM => aead_algorithm(id),
        _ => None,
    };
    let Some(algorithm) = algorithm else {
        return status(Err(Error::Unsupported));
    };
    // SAFETY: the caller's contract.
    let (key, iv) = unsafe { (bytes(key, len), *iv) };
    // SAFETY: the caller's contract.
    unsafe {
        new_handle(out, || {
            Ok(QuicSealingKey {
                key: aead::Key::new(algorithm, key)?,
                iv,
                top: None,
                seen: [0; QuicSealingKey::WINDOW / 64],
            })
        })
    }
}

/// Encrypts the `len` bytes at `in_out` in place for packet number `pn`
/// and the `aad_len` bytes at `aad`, writing the tag to `tag`, if no
/// packet of `pn` was sealed under the key and `pn` is within 1024 of the
/// highest sealed.
///
/// # Safety
/// `key` must be live and in no other call, `aad` valid for `aad_len`
/// reads, `in_out` for `len` reads and writes, and `tag` for 16 writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_quic_seal(
    key: *mut QuicSealingKey,
    pn: u64,
    aad: *const u8,
    aad_len: usize,
    in_out: *mut u8,
    len: usize,
    tag: *mut [u8; 16],
) -> Status {
    // SAFETY: the caller's contract.
    let (key, aad, in_out) = unsafe { (&mut *key, bytes(aad, aad_len), bytes_mut(in_out, len)) };
    scrubbed(Depth::Small, || {
        // As for a TLS record, a seal that then fails spends its number.
        let mut sealed_tag = [0u8; 16];
        let result = key.take(pn).and_then(|()| {
            let mut nonce = key.iv;
            for (n, p) in nonce[4..].iter_mut().zip(pn.to_be_bytes()) {
                *n ^= p;
            }
            seal(&key.key, nonce, aad, in_out, &mut sealed_tag)
        });
        if result.is_ok() {
            // SAFETY: the caller's contract.
            unsafe { put(tag, sealed_tag) };
        }
        sealed(result, in_out)
    })
}

free!(rind_fips_quic_sealing_key_free, QuicSealingKey);

/// An AES-GCM key of any IV length for the AES key size `id`, from the
/// `len` bytes at `key`, with tags of `tag_len` bytes.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_gcm_key_new(
    id: u32,
    key: *const u8,
    len: usize,
    tag_len: usize,
    out: *mut *mut gcm::Key,
) -> Status {
    let algorithm = match aes_key_size(id).and_then(|a| tag_length(tag_len).map(|t| (a, t))) {
        Ok(algorithm) => algorithm,
        Err(error) => return status(Err(error)),
    };
    ensure(&[SelfTest::AesGcm]);
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    // SAFETY: the caller's contract.
    unsafe { new_handle(out, || gcm::Key::new(algorithm.0, key, algorithm.1)) }
}

/// Decrypts and verifies the `len` bytes at `in_out` in place against the
/// `tag_len` bytes at `tag`, under the `iv_len`-byte IV at `iv` and the
/// `aad_len` bytes at `aad`.
///
/// # Safety
/// `key` must be live, `iv`, `aad`, and `tag` valid for their lengths'
/// reads, and `in_out` for `len` reads and writes.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn rind_fips_gcm_open(
    key: *const gcm::Key,
    iv: *const u8,
    iv_len: usize,
    aad: *const u8,
    aad_len: usize,
    tag: *const u8,
    tag_len: usize,
    in_out: *mut u8,
    len: usize,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, iv, aad, tag, in_out) = unsafe {
        (
            &*key,
            bytes(iv, iv_len),
            bytes(aad, aad_len),
            bytes(tag, tag_len),
            bytes_mut(in_out, len),
        )
    };
    scrubbed(Depth::Small, || {
        status(
            gcm::Iv::assume_unique_for_key(iv)
                .and_then(|iv| key.open_in_place_separate_tag(iv, aad, tag, in_out))
                .map(|_| ()),
        )
    })
}

free!(rind_fips_gcm_key_free, gcm::Key);

/// A QUIC header-protection key for the AES key size `id`, from the `len`
/// bytes at `key`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_quic_hp_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut quic::HeaderProtectionKey,
) -> Status {
    let Some(algorithm) = quic_algorithm(id) else {
        return status(Err(Error::Unsupported));
    };
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    // SAFETY: the caller's contract.
    unsafe { new_handle(out, || quic::HeaderProtectionKey::new(algorithm, key)) }
}

/// Writes the 5-byte mask `key` derives from the 16-byte sample at
/// `sample` to `mask`.
///
/// # Safety
/// `key` must be live, `sample` valid for 16 reads, and `mask` for 5
/// writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_quic_hp_mask(
    key: *const quic::HeaderProtectionKey,
    sample: *const [u8; quic::SAMPLE_LEN],
    mask: *mut [u8; 5],
) {
    // SAFETY: the caller's contract.
    let (key, sample) = unsafe { (&*key, &*sample) };
    // SAFETY: the caller's contract.
    scrubbed(Depth::Small, || unsafe { put(mask, key.mask(sample)) })
}

free!(rind_fips_quic_hp_free, quic::HeaderProtectionKey);

/// The AES-GCM key for the algorithm `id` names that `prk` expands to for
/// the concatenation of the `info_len` strings at `info`, or null for an
/// unknown `id` or an empty `info`.
///
/// # Safety
/// `prk` must be live, and `info` valid as `abi::byte_list` requires.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hkdf_expand_aead(
    prk: *const hkdf::Prk,
    info: *const Bytes,
    info_len: usize,
    id: u32,
) -> *mut aead::Key {
    let Some(algorithm) = aead_algorithm(id) else {
        return core::ptr::null_mut();
    };
    // SAFETY: the caller's contract.
    let (prk, info) = unsafe { (&*prk, byte_list(info, info_len)) };
    let Ok(okm) = crate::mac::expand(prk, &info, algorithm) else {
        return core::ptr::null_mut();
    };
    scrubbed(Depth::Small, || handle(aead::Key::from(okm)))
}

/// The QUIC header-protection key for the AES key size `id` that `prk`
/// expands to for `info`, as [`rind_fips_hkdf_expand_aead`] takes it, or
/// null for an unknown `id` or an empty `info`.
///
/// # Safety
/// As for [`rind_fips_hkdf_expand_aead`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_hkdf_expand_quic_hp(
    prk: *const hkdf::Prk,
    info: *const Bytes,
    info_len: usize,
    id: u32,
) -> *mut quic::HeaderProtectionKey {
    let Some(algorithm) = quic_algorithm(id) else {
        return core::ptr::null_mut();
    };
    // SAFETY: the caller's contract.
    let (prk, info) = unsafe { (&*prk, byte_list(info, info_len)) };
    let Ok(okm) = crate::mac::expand(prk, &info, algorithm) else {
        return core::ptr::null_mut();
    };
    scrubbed(Depth::Small, || {
        handle(quic::HeaderProtectionKey::from(okm))
    })
}
