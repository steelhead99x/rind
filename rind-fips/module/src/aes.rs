// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES: the block cipher, CTR, and CBC (SP 800-38A), key wrapping (SP
//! 800-38F), QUIC header protection, and AES-GCM opening (SP 800-38D).
//!
//! AES-GCM seals here only with an IV the module generates, as IG C.H
//! requires, which is not offered yet, so these services only open.

use rind::aead::{self, gcm, quic};
use rind::cipher::{self, Aes, AesCbcDecryptingKey, AesCbcEncryptingKey, AesCtr, CbcIv};
use rind::key_wrap::AesKek;
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
    scrubbed(Depth::Small, || status(kek.wrap(key, wrapped)))
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
    scrubbed(Depth::Small, || status(kek.unwrap(wrapped, key)))
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
    scrubbed(Depth::Small, || status(kek.wrap_padded(key, wrapped)))
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
        status(kek.unwrap_padded(wrapped, key).map(|unwrapped| {
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
    scrubbed(Depth::Small, || {
        let nonce = aead::Nonce::assume_unique_for_key(nonce);
        status(
            aead::Tag::try_from(&tag[..])
                .and_then(|tag| key.open_in_place_separate_tag(nonce, aad, tag, in_out))
                .map(|_| ()),
        )
    })
}

free!(rind_fips_aead_key_free, aead::Key);

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
/// unknown `id`.
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
    scrubbed(Depth::Small, || {
        handle(aead::Key::from(prk.expand(&info, algorithm)))
    })
}

/// The QUIC header-protection key for the AES key size `id` that `prk`
/// expands to for `info`, as [`rind_fips_hkdf_expand_aead`] takes it, or
/// null for an unknown `id`.
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
    scrubbed(Depth::Small, || {
        handle(quic::HeaderProtectionKey::from(
            prk.expand(&info, algorithm),
        ))
    })
}
