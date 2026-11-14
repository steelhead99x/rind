// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The numbers the C ABI names algorithms by. `rind-fips` includes this file
//! too, so both sides agree by construction.

/// Hash functions, and the HMACs, HKDFs, and PBKDF2s over them.
pub(crate) mod hash {
    pub(crate) const SHA1: u32 = 1;
    pub(crate) const SHA256: u32 = 2;
    pub(crate) const SHA384: u32 = 3;
    pub(crate) const SHA512: u32 = 4;
    pub(crate) const SHA512_256: u32 = 5;
    pub(crate) const SHA3_256: u32 = 6;
    pub(crate) const SHA3_384: u32 = 7;
    pub(crate) const SHA3_512: u32 = 8;
}

/// AES key sizes, for the block cipher's modes, key wrapping, AES-GCM of
/// any IV length, and QUIC header protection.
pub(crate) mod aes {
    pub(crate) const AES_128: u32 = 1;
    pub(crate) const AES_192: u32 = 2;
    pub(crate) const AES_256: u32 = 3;
}

/// AES-GCM, by key length.
pub(crate) mod aead {
    pub(crate) const AES_128_GCM: u32 = 1;
    pub(crate) const AES_192_GCM: u32 = 2;
    pub(crate) const AES_256_GCM: u32 = 3;
}

/// The NIST curves, for ECDH and ECDSA.
pub(crate) mod curve {
    pub(crate) const P256: u32 = 1;
    pub(crate) const P384: u32 = 2;
    pub(crate) const P521: u32 = 3;
}

/// Key encapsulation mechanisms.
pub(crate) mod kem {
    pub(crate) const ML_KEM_768: u32 = 1;
}

/// ML-DSA's parameter sets.
pub(crate) mod ml_dsa {
    pub(crate) const ML_DSA_44: u32 = 1;
    pub(crate) const ML_DSA_65: u32 = 2;
    pub(crate) const ML_DSA_87: u32 = 3;
}

/// Signature algorithms, by the name of rind's constant: every verify
/// algorithm, of which the ECDSA and RSA ones that also sign name their
/// sign algorithm too.
pub(crate) mod signature {
    pub(crate) const ECDSA_P256_SHA256_ASN1: u32 = 1;
    pub(crate) const ECDSA_P256_SHA384_ASN1: u32 = 2;
    pub(crate) const ECDSA_P256_SHA512_ASN1: u32 = 3;
    pub(crate) const ECDSA_P384_SHA256_ASN1: u32 = 4;
    pub(crate) const ECDSA_P384_SHA384_ASN1: u32 = 5;
    pub(crate) const ECDSA_P384_SHA512_ASN1: u32 = 6;
    pub(crate) const ECDSA_P521_SHA256_ASN1: u32 = 7;
    pub(crate) const ECDSA_P521_SHA384_ASN1: u32 = 8;
    pub(crate) const ECDSA_P521_SHA512_ASN1: u32 = 9;
    pub(crate) const ECDSA_P256_SHA256_FIXED: u32 = 10;
    pub(crate) const ECDSA_P384_SHA384_FIXED: u32 = 11;
    pub(crate) const ECDSA_P521_SHA512_FIXED: u32 = 12;
    pub(crate) const RSA_PKCS1_SHA256: u32 = 13;
    pub(crate) const RSA_PKCS1_SHA384: u32 = 14;
    pub(crate) const RSA_PKCS1_SHA512: u32 = 15;
    pub(crate) const RSA_PSS_SHA256: u32 = 16;
    pub(crate) const RSA_PSS_SHA384: u32 = 17;
    pub(crate) const RSA_PSS_SHA512: u32 = 18;
    pub(crate) const ED25519: u32 = 19;
    pub(crate) const ML_DSA_44: u32 = 20;
    pub(crate) const ML_DSA_65: u32 = 21;
    pub(crate) const ML_DSA_87: u32 = 22;
    pub(crate) const RSA_PKCS1_SHA1: u32 = 23;
    pub(crate) const RSA_PKCS1_1024_SHA1: u32 = 24;
    pub(crate) const RSA_PKCS1_1024_SHA256: u32 = 25;
    pub(crate) const RSA_PKCS1_1024_SHA512: u32 = 26;
    pub(crate) const RSA_PKCS1_3072_SHA384: u32 = 27;
}

/// RSA key sizes to generate.
pub(crate) mod rsa_size {
    pub(crate) const RSA_2048: u32 = 1;
    pub(crate) const RSA_3072: u32 = 2;
    pub(crate) const RSA_4096: u32 = 3;
    pub(crate) const RSA_6144: u32 = 4;
    pub(crate) const RSA_8192: u32 = 5;
}

/// Error kinds, as a status's low byte carries them: rind's `Error`
/// variants that an approved service can return. The rest of a status is
/// rind's own code for the error, which names a refused key's reason.
pub(crate) mod error {
    pub(crate) const WRONG_LENGTH: u32 = 1;
    pub(crate) const KEY_REJECTED: u32 = 2;
    pub(crate) const BAD_SIGNATURE: u32 = 3;
    pub(crate) const DECRYPT_FAILED: u32 = 4;
    pub(crate) const RNG_FAILED: u32 = 5;
    pub(crate) const NOT_EQUAL: u32 = 6;
    pub(crate) const FAULT: u32 = 7;
    pub(crate) const UNSUPPORTED: u32 = 8;
}
