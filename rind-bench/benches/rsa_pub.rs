//! RSA verification and OAEP encryption, the public-key side.

#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, dit};

/// An RSA-2048 PKCS#1 public key, and its PKCS#1 v1.5 SHA-256 signature
/// over [`MESSAGE`].
#[cfg(not(target_arch = "xtensa"))]
const PUBLIC_KEY_2048: &[u8] = b"\x30\x82\x01\x0a\x02\x82\x01\x01\x00\xa2\xb4\x51\xa0\x7d\x0a\xa5\xf9\x6e\x45\x56\x71\x51\x35\x50\x51\x4a\x8a\x5b\x46\x2e\xbe\xf7\x17\x09\x4f\xa1\xfe\xe8\x22\x24\xe6\x37\xf9\x74\x6d\x3f\x7c\xaf\xd3\x18\x78\xd8\x03\x25\xb6\xef\x5a\x17\x00\xf6\x59\x03\xb4\x69\x42\x9e\x89\xd6\xea\xc8\x84\x50\x97\xb5\xab\x39\x31\x89\xdb\x92\x51\x2e\xd8\xa7\x71\x1a\x12\x53\xfa\xcd\x20\xf7\x9c\x15\xe8\x24\x7f\x3d\x3e\x42\xe4\x6e\x48\xc9\x8e\x25\x4a\x2f\xe9\x76\x53\x13\xa0\x3e\xff\x8f\x17\xe1\xa0\x29\x39\x7a\x1f\xa2\x6a\x8d\xce\x26\xf4\x90\xed\x81\x29\x96\x15\xd9\x81\x4c\x22\xda\x61\x04\x28\xe0\x9c\x7d\x96\x58\x59\x42\x66\xf5\xc0\x21\xd0\xfc\xec\xa0\x8d\x94\x5a\x12\xbe\x82\xde\x4d\x1e\xce\x6b\x4c\x03\x14\x5b\x5d\x34\x95\xd4\xed\x54\x11\xeb\x87\x8d\xaf\x05\xfd\x7a\xfc\x3e\x09\xad\xa0\xf1\x12\x64\x22\xf5\x90\x97\x5a\x19\x69\x81\x6f\x48\x69\x8b\xcb\xba\x1b\x4d\x9c\xae\x79\xd4\x60\xd8\xf9\xf8\x5e\x79\x75\x00\x5d\x9b\xc2\x2c\x4e\x5a\xc0\xf7\xc1\xa4\x5d\x12\x56\x9a\x62\x80\x7d\x3b\x9a\x02\xe5\xa5\x30\xe7\x73\x06\x6f\x45\x3d\x1f\x5b\x4c\x2e\x9c\xf7\x82\x02\x83\xf7\x42\xb9\xd5\x02\x03\x01\x00\x01";
#[cfg(not(target_arch = "xtensa"))]
const SIGNATURE_2048: &[u8] = b"\x8a\x1b\x22\x0c\xb2\xab\x41\x5d\xc7\x60\xeb\x7f\x5b\xb1\x03\x35\xa3\xcc\xa2\x69\xd7\xdb\xbf\x7d\x09\x62\xba\x79\xf9\xcf\x7b\x43\xa5\xfc\x09\xc9\x9a\x15\x84\xf0\x74\x03\x47\x3d\x6c\x18\x9a\x83\x68\x97\xa5\xb6\xf8\xea\x9f\xa2\x2d\x60\x1e\x6b\xa5\xf7\x41\x1f\xe2\x7c\x63\x8b\x81\xb1\xa2\x23\x63\x58\x3a\x80\xfc\xe8\xc7\xdf\x3e\x40\xfb\x51\xbd\x0e\x60\xd0\xa6\x65\x3f\x79\xf3\xbc\xb7\xec\x3e\x9d\xc1\x4c\xfb\x5b\x31\xab\x17\x35\xbc\xa6\x92\xd5\x0a\xc0\x3f\x97\x9d\xda\x92\x74\x7c\x64\x30\xf8\x04\x5e\xfa\x35\x13\xba\x6e\x0c\xe3\xe9\xe3\x55\x70\xe1\xc3\x0c\x8e\xbe\x58\x9b\x44\x19\x2e\x13\x44\xca\x83\xdf\xa5\x76\xfc\x6f\xdc\x7b\xf1\xcd\x7c\xee\x87\x5b\x00\x1c\x8c\x02\xce\x8d\x60\x27\x69\xe4\xbd\x9d\x24\x1c\x48\x57\x18\x2a\x00\x89\xa8\xb6\x76\x44\xe7\x3e\xef\x10\x5c\x55\x0e\xfa\x47\xa4\x08\x74\x28\x93\x95\xac\x0c\x4e\x02\xfd\x4b\xa9\x8e\x13\x0a\x4c\x2d\x1b\x95\x52\x1c\x6a\xf4\xa0\x02\xac\x3b\xdc\x6e\x52\x12\x2a\xe4\xc0\x8c\xc3\xda\x1c\x89\x6e\x05\x9a\xcb\xdd\xec\x57\x4a\xc0\x43\x2f\x61\x03\xdd\x97\x27\x3d\x88\x03\xc1\x02";

/// Wycheproof's `rsa_pkcs1_1024_sig_gen_test.json`, the first SHA-1 case,
/// over the empty message.
#[cfg(not(target_arch = "xtensa"))]
const PUBLIC_KEY_1024: &[u8] = b"\x30\x81\x89\x02\x81\x81\x00\xd0\x94\x1e\x63\xa9\x80\xfa\x92\xfb\x25\xed\x4c\x7b\x33\x07\xf8\x27\x02\x30\x34\xae\x7f\x1a\x74\x91\xf0\x69\x9c\xa7\x60\x72\x85\xe6\x2a\xd8\xe9\x94\xba\xc2\x1b\x8b\x6e\x30\x5e\x33\x4f\x48\x74\x06\x7d\x28\xe3\x04\x23\x0d\xca\x7f\x0e\x85\xf7\xce\x59\x57\x70\xb6\xe0\x54\xc9\xf8\x44\xba\x86\xc0\x69\x6e\xeb\xa0\x76\x9d\x8d\x4a\x34\x7e\x8f\xe8\x5c\x72\x4a\xc1\xc4\x49\x94\xaf\x18\xa3\x9e\x71\x9f\x72\x1f\x1b\xc5\x0c\x46\xa3\x9e\x6c\x07\x5f\xcd\x16\x49\xf0\x1f\x22\x60\x8c\xe7\xdc\x69\x55\x50\x22\x58\x33\x69\x87\xd9\x02\x03\x01\x00\x01";
#[cfg(not(target_arch = "xtensa"))]
const SIGNATURE_1024: &[u8] = b"\x03\xe6\x4d\x14\x8e\x05\x20\x1b\x02\x1f\xb5\xd3\xd7\x2a\xb6\xab\xd4\x29\x4b\xe6\xc1\x67\x32\x77\xba\x58\x22\xad\x2f\xe7\xce\x4b\xb2\x9a\xc5\x47\xb2\xfd\xf0\x9c\x28\x94\xea\x0e\x31\xe7\x6f\x1b\x3e\x19\x37\xdb\x91\xc3\x89\x46\x7e\x9a\x8a\xc7\xbe\x0a\x4f\x67\x44\x56\xf0\x1c\x5b\x4f\xa4\x27\x7a\x26\x02\x8b\x49\xb1\x6e\x25\x68\x98\x27\xd0\xa4\xb9\xf1\xc2\x5a\x63\x35\x0d\xc1\x51\x31\xda\x90\x8a\x05\xc7\xcf\xa8\xc0\x8a\x67\xac\x9e\xfe\x3b\x0c\xd0\x4a\xba\x7d\xb1\x20\x64\xcb\xc3\x67\x29\xea\xae\xc5\x40\xc4\xbc\x12";

#[cfg(not(target_arch = "xtensa"))]
const MESSAGE: &[u8] = &[0; 20];

/// The modulus and public exponent of a PKCS#1 public key, as
/// verified-garbage takes them in place of DER.
#[cfg(not(target_arch = "xtensa"))]
fn vg_components(public_key: &[u8]) -> (Vec<u8>, Vec<u8>) {
    use rsa::pkcs1::DecodeRsaPublicKey;
    use rsa::traits::PublicKeyParts;
    let key = rsa::PublicKey::from_pkcs1_der(public_key).unwrap();
    (key.n_bytes().to_vec(), key.e_bytes().to_vec())
}

/// verified-garbage's public key of the modulus and exponent `n_e`.
#[cfg(not(target_arch = "xtensa"))]
fn vg_public((n, e): &(Vec<u8>, Vec<u8>)) -> verified_garbage::rsa::PublicKey {
    use verified_garbage::rsa::{BigUint, PublicKey};
    PublicKey::new(BigUint::from_be_bytes(n), BigUint::from_be_bytes(e)).unwrap()
}

/// A PKCS#1 public key and a signature by it over `message`.
#[cfg(not(target_arch = "xtensa"))]
struct Signed {
    public_key: Vec<u8>,
    signature: Vec<u8>,
}

/// Signs `message` with rind's `key` under `scheme`.
#[cfg(not(target_arch = "xtensa"))]
fn signed(
    key: rind::rsa::KeyPair,
    scheme: &'static rind::rsa::SigningAlgorithm,
    message: &[u8],
) -> Signed {
    Signed {
        public_key: key.public_key().as_ref().to_vec(),
        signature: key.sign(scheme, message).unwrap().as_ref().to_vec(),
    }
}

/// Parses a PKCS#1 public key and verifies a PKCS#1 v1.5 or PSS signature
/// over SHA-256 with it, through OpenSSL.
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
fn openssl_verify(public_key: &[u8], pss: bool, message: &[u8], signature: &[u8]) {
    use openssl::hash::MessageDigest;
    use openssl::pkey::PKey;
    use openssl::rsa::{Padding, Rsa};
    use openssl::sign::{RsaPssSaltlen, Verifier};
    let key = PKey::from_rsa(Rsa::public_key_from_der_pkcs1(public_key).unwrap()).unwrap();
    let mut verifier = Verifier::new(MessageDigest::sha256(), &key).unwrap();
    if pss {
        verifier.set_rsa_padding(Padding::PKCS1_PSS).unwrap();
        verifier
            .set_rsa_pss_saltlen(RsaPssSaltlen::DIGEST_LENGTH)
            .unwrap();
    }
    assert!(verifier.verify_oneshot(signature, message).unwrap());
}

#[cfg(not(target_arch = "xtensa"))]
mod rsa2048_pkcs1_sha256_verify {
    use swole::bench;

    use super::*;

    type Ring = ring::signature::UnparsedPublicKey<&'static [u8]>;
    type Aws = aws_lc_rs::signature::UnparsedPublicKey<&'static [u8]>;
    type RustCrypto = rsa::pkcs1v15::VerifyingKey<sha2::Sha256>;

    fn ring_key() -> Ring {
        Ring::new(
            &ring::signature::RSA_PKCS1_2048_8192_SHA256,
            PUBLIC_KEY_2048,
        )
    }

    #[bench(setup = ring_key)]
    fn ring(key: &Ring) {
        key.verify(MESSAGE, SIGNATURE_2048).unwrap()
    }

    fn aws_key() -> Aws {
        Aws::new(
            &aws_lc_rs::signature::RSA_PKCS1_2048_8192_SHA256,
            PUBLIC_KEY_2048,
        )
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(key: &Aws) {
        key.verify(MESSAGE, SIGNATURE_2048).unwrap()
    }

    fn rustcrypto_key() -> RustCrypto {
        use rsa::pkcs1::DecodeRsaPublicKey;
        RustCrypto::new(rsa::PublicKey::from_pkcs1_der(PUBLIC_KEY_2048).unwrap())
    }

    #[bench(setup = rustcrypto_key)]
    fn rustcrypto(key: &RustCrypto) {
        use rsa::signature::Verifier;
        let signature = rsa::pkcs1v15::Signature::try_from(SIGNATURE_2048).unwrap();
        key.verify(MESSAGE, &signature).unwrap()
    }

    #[bench(setup = dit)]
    fn rind(_: &Dit<()>) {
        use rind::rsa::{PublicKey, verify};
        let key = PublicKey::new(PUBLIC_KEY_2048).unwrap();
        key.verify(&verify::PKCS1_SHA256, MESSAGE, SIGNATURE_2048)
            .unwrap()
    }

    #[cfg(graviola)]
    #[bench]
    fn graviola() {
        use graviola::signing::rsa::VerifyingKey;
        let key = VerifyingKey::from_pkcs1_der(PUBLIC_KEY_2048).unwrap();
        key.verify_pkcs1_sha256(SIGNATURE_2048, MESSAGE).unwrap()
    }

    /// The key's modulus and exponent, after checking verified-garbage
    /// accepts the signature.
    fn vg_input() -> (Vec<u8>, Vec<u8>) {
        use verified_garbage::hashes::sha256::Sha256;
        use verified_garbage::rsa::pkcs1_sig::Hash;
        let components = vg_components(PUBLIC_KEY_2048);
        vg_public(&components)
            .verify_pkcs1v15(SIGNATURE_2048, &Sha256::digest(MESSAGE), Hash::Sha256)
            .unwrap();
        components
    }

    // verified-garbage takes the modulus and exponent rather than DER, so its
    // row skips the DER parse that rind's does, and is given the digest.
    #[bench(setup = vg_input)]
    fn verified_garbage(components: &(Vec<u8>, Vec<u8>)) {
        use verified_garbage::hashes::sha256::Sha256;
        use verified_garbage::rsa::pkcs1_sig::Hash;
        let key = vg_public(components);
        let digest = Sha256::digest(MESSAGE);
        key.verify_pkcs1v15(SIGNATURE_2048, &digest, Hash::Sha256)
            .unwrap()
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench]
    fn openssl() {
        openssl_verify(PUBLIC_KEY_2048, false, MESSAGE, SIGNATURE_2048)
    }
}

/// A key parsed once, as a JWT verifier holds it, keeps its setup.
#[cfg(not(target_arch = "xtensa"))]
mod rsa2048_pkcs1_sha256_verify_parsed {
    use swole::bench;

    use super::*;

    type Aws = aws_lc_rs::signature::ParsedPublicKey;

    fn aws_key() -> Aws {
        Aws::new(
            &aws_lc_rs::signature::RSA_PKCS1_2048_8192_SHA256,
            PUBLIC_KEY_2048,
        )
        .unwrap()
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(key: &Aws) {
        key.verify_sig(MESSAGE, SIGNATURE_2048).unwrap()
    }

    fn rind_key() -> Dit<rind::rsa::PublicKey> {
        Dit::hold(rind::rsa::PublicKey::new(PUBLIC_KEY_2048).unwrap())
    }

    #[bench(setup = rind_key)]
    fn rind(key: &Dit<rind::rsa::PublicKey>) {
        key.verify(&rind::rsa::verify::PKCS1_SHA256, MESSAGE, SIGNATURE_2048)
            .unwrap()
    }

    fn vg_key() -> verified_garbage::rsa::PublicKey {
        vg_public(&vg_components(PUBLIC_KEY_2048))
    }

    #[bench(setup = vg_key)]
    fn verified_garbage(key: &verified_garbage::rsa::PublicKey) {
        use verified_garbage::hashes::sha256::Sha256;
        use verified_garbage::rsa::pkcs1_sig::Hash;
        let digest = Sha256::digest(MESSAGE);
        key.verify_pkcs1v15(SIGNATURE_2048, &digest, Hash::Sha256)
            .unwrap()
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod rsa1024_pkcs1_sha1_verify {
    use swole::bench;

    use super::*;

    type Ring = ring::signature::UnparsedPublicKey<&'static [u8]>;
    type Aws = aws_lc_rs::signature::UnparsedPublicKey<&'static [u8]>;

    fn ring_key() -> Ring {
        Ring::new(
            &ring::signature::RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY,
            PUBLIC_KEY_1024,
        )
    }

    #[bench(setup = ring_key)]
    fn ring(key: &Ring) {
        key.verify(b"", SIGNATURE_1024).unwrap()
    }

    fn aws_key() -> Aws {
        Aws::new(
            &aws_lc_rs::signature::RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY,
            PUBLIC_KEY_1024,
        )
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(key: &Aws) {
        key.verify(b"", SIGNATURE_1024).unwrap()
    }

    #[bench(setup = dit)]
    fn rind(_: &Dit<()>) {
        use rind::rsa::{PublicKey, verify};
        let key = PublicKey::new(PUBLIC_KEY_1024).unwrap();
        key.verify(&verify::legacy::PKCS1_1024_SHA1, b"", SIGNATURE_1024)
            .unwrap()
    }

    fn vg_input() -> (Vec<u8>, Vec<u8>) {
        vg_components(PUBLIC_KEY_1024)
    }

    // Given the modulus and exponent rather than DER, as above.
    #[bench(setup = vg_input)]
    fn verified_garbage(components: &(Vec<u8>, Vec<u8>)) {
        use verified_garbage::hashes::sha1::Sha1;
        use verified_garbage::rsa::pkcs1_sig::Hash;
        let key = vg_public(components);
        let digest = Sha1::digest(b"");
        key.verify_pkcs1v15(SIGNATURE_1024, &digest, Hash::Sha1)
            .unwrap()
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod rsa2048_pss_sha256_verify {
    use swole::bench;

    use super::*;

    type Ring = ring::signature::UnparsedPublicKey<Vec<u8>>;
    type Aws = aws_lc_rs::signature::UnparsedPublicKey<Vec<u8>>;

    /// Signed here, since PSS signatures are randomized.
    fn input() -> Signed {
        signed(
            rind::rsa::KeyPair::from_pkcs1(include_bytes!("../../rind/src/high/rsa/rsa2048.der"))
                .unwrap(),
            &rind::rsa::sign::PSS_SHA256,
            MESSAGE,
        )
    }

    fn ring_key() -> (Ring, Vec<u8>) {
        let Signed {
            public_key,
            signature,
        } = input();
        let key = Ring::new(&ring::signature::RSA_PSS_2048_8192_SHA256, public_key);
        (key, signature)
    }

    #[bench(setup = ring_key)]
    fn ring((key, signature): &(Ring, Vec<u8>)) {
        key.verify(MESSAGE, signature).unwrap()
    }

    fn aws_key() -> (Aws, Vec<u8>) {
        let Signed {
            public_key,
            signature,
        } = input();
        let key = Aws::new(&aws_lc_rs::signature::RSA_PSS_2048_8192_SHA256, public_key);
        (key, signature)
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs((key, signature): &(Aws, Vec<u8>)) {
        key.verify(MESSAGE, signature).unwrap()
    }

    fn rind_input() -> Dit<Signed> {
        Dit::hold(input())
    }

    #[bench(setup = rind_input)]
    fn rind(signed: &Dit<Signed>) {
        use rind::rsa::{PublicKey, verify};
        let key = PublicKey::new(&signed.public_key).unwrap();
        key.verify(&verify::PSS_SHA256, MESSAGE, &signed.signature)
            .unwrap()
    }

    fn vg_verify(
        key: &verified_garbage::rsa::PublicKey,
        signature: &[u8],
    ) -> Result<(), verified_garbage::error::InvalidSignature> {
        use verified_garbage::hashes::sha256::Sha256;
        use verified_garbage::rsa::pss::{Hash, SaltLength};
        let digest = Sha256::digest(MESSAGE);
        key.verify_pss(
            signature,
            &digest,
            Hash::Sha256,
            Hash::Sha256,
            SaltLength::Len(32),
        )
    }

    /// The key's modulus and exponent and the signature, after checking
    /// verified-garbage accepts it.
    fn vg_input() -> ((Vec<u8>, Vec<u8>), Vec<u8>) {
        let signed = input();
        let components = vg_components(&signed.public_key);
        vg_verify(&vg_public(&components), &signed.signature).unwrap();
        (components, signed.signature)
    }

    // Given the modulus and exponent rather than DER, as above.
    #[bench(setup = vg_input)]
    fn verified_garbage((components, signature): &((Vec<u8>, Vec<u8>), Vec<u8>)) {
        vg_verify(&vg_public(components), signature).unwrap()
    }

    #[bench(setup = input)]
    fn rustcrypto(signed: &Signed) {
        use rsa::pkcs1::DecodeRsaPublicKey;
        use rsa::signature::Verifier;
        let key = rsa::pss::VerifyingKey::<sha2::Sha256>::new(
            rsa::PublicKey::from_pkcs1_der(&signed.public_key).unwrap(),
        );
        let signature = rsa::pss::Signature::try_from(&signed.signature[..]).unwrap();
        key.verify(MESSAGE, &signature).unwrap()
    }

    #[cfg(graviola)]
    #[bench(setup = input)]
    fn graviola(signed: &Signed) {
        use graviola::signing::rsa::VerifyingKey;
        let key = VerifyingKey::from_pkcs1_der(&signed.public_key).unwrap();
        key.verify_pss_sha256(&signed.signature, MESSAGE).unwrap()
    }

    /// The bare modulus, which libcrux takes, assuming the exponent 65537,
    /// and the signature.
    fn libcrux_input() -> (Vec<u8>, [u8; 256]) {
        use rsa::pkcs1::DecodeRsaPublicKey;
        use rsa::traits::PublicKeyParts;
        let signed = input();
        let n = rsa::PublicKey::from_pkcs1_der(&signed.public_key)
            .unwrap()
            .n_bytes()
            .to_vec();
        (n, signed.signature.try_into().unwrap())
    }

    #[bench(setup = libcrux_input)]
    fn libcrux((n, signature): &(Vec<u8>, [u8; 256])) {
        let key = libcrux_rsa::PublicKey::<256>::from(<[u8; 256]>::try_from(&n[..]).unwrap());
        libcrux_rsa::verify_2048(
            libcrux_rsa::DigestAlgorithm::Sha2_256,
            &key,
            MESSAGE,
            32,
            signature,
        )
        .unwrap()
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = input)]
    fn openssl(signed: &Signed) {
        openssl_verify(&signed.public_key, true, MESSAGE, &signed.signature)
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod rsa2048_oaep_sha256_encrypt {
    use rind::rsa::{DecryptingKey, EncryptingKey, OAEP_SHA256};
    use swole::bench;

    use super::*;

    const PLAINTEXT: [u8; 32] = [0; 32];

    fn private_key() -> DecryptingKey {
        DecryptingKey::from_pkcs1(
            &OAEP_SHA256,
            include_bytes!("../../rind/src/high/rsa/rsa2048.der"),
        )
        .unwrap()
    }

    fn aws_key() -> aws_lc_rs::rsa::OaepPublicEncryptingKey {
        use aws_lc_rs::rsa::{OaepPublicEncryptingKey, PublicEncryptingKey};
        let spki = private_key().public_key().to_spki();
        OaepPublicEncryptingKey::new(PublicEncryptingKey::from_der(spki.as_ref()).unwrap()).unwrap()
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(key: &aws_lc_rs::rsa::OaepPublicEncryptingKey) -> [u8; 256] {
        let mut ciphertext = [0u8; 256];
        key.encrypt(
            &aws_lc_rs::rsa::OAEP_SHA256_MGF1SHA256,
            &PLAINTEXT,
            &mut ciphertext,
            None,
        )
        .unwrap();
        ciphertext
    }

    fn rind_key() -> Dit<EncryptingKey> {
        let private_key = private_key();
        Dit::hold(EncryptingKey::new(&OAEP_SHA256, private_key.public_key().as_ref()).unwrap())
    }

    #[bench(setup = rind_key)]
    fn rind(key: &Dit<EncryptingKey>) {
        black_box(key.encrypt(&PLAINTEXT, b"").unwrap());
    }

    /// verified-garbage's key, after checking rind decrypts what it encrypts.
    fn vg_key() -> verified_garbage::rsa::PublicKey {
        use verified_garbage::rsa::oaep::Hash;
        let private_key = private_key();
        let key = vg_public(&vg_components(private_key.public_key().as_ref()));
        let ciphertext = key
            .encrypt_oaep(&PLAINTEXT, Hash::Sha256, Hash::Sha256, b"")
            .unwrap();
        assert_eq!(
            private_key.decrypt(&ciphertext, b"").unwrap().as_ref(),
            PLAINTEXT
        );
        key
    }

    #[bench(setup = vg_key)]
    fn verified_garbage(key: &verified_garbage::rsa::PublicKey) {
        use verified_garbage::rsa::oaep::Hash;
        black_box(
            key.encrypt_oaep(&PLAINTEXT, Hash::Sha256, Hash::Sha256, b"")
                .unwrap(),
        );
    }
}

/// Verification at the other sizes, whose moduli take a different Montgomery
/// multiplication from RSA-2048's on some CPUs: 2056 bits for an odd number
/// of words.
macro_rules! verify_size {
    ($name:ident, $pkcs8:literal) => {
        mod $name {
            use swole::bench;

            use super::*;

            type Ring = ring::signature::UnparsedPublicKey<Vec<u8>>;
            type Aws = aws_lc_rs::signature::UnparsedPublicKey<Vec<u8>>;

            const MESSAGE: &[u8] = b"hello";

            fn input() -> Signed {
                signed(
                    rind::rsa::KeyPair::from_pkcs8(include_bytes!($pkcs8)).unwrap(),
                    &rind::rsa::sign::PKCS1_SHA256,
                    MESSAGE,
                )
            }

            fn ring_key() -> (Ring, Vec<u8>) {
                let Signed {
                    public_key,
                    signature,
                } = input();
                let key = Ring::new(&ring::signature::RSA_PKCS1_2048_8192_SHA256, public_key);
                (key, signature)
            }

            #[bench(setup = ring_key)]
            fn ring((key, signature): &(Ring, Vec<u8>)) {
                key.verify(MESSAGE, signature).unwrap()
            }

            fn aws_key() -> (Aws, Vec<u8>) {
                let Signed {
                    public_key,
                    signature,
                } = input();
                let key = Aws::new(
                    &aws_lc_rs::signature::RSA_PKCS1_2048_8192_SHA256,
                    public_key,
                );
                (key, signature)
            }

            #[bench(setup = aws_key)]
            fn aws_lc_rs((key, signature): &(Aws, Vec<u8>)) {
                key.verify(MESSAGE, signature).unwrap()
            }

            fn rind_input() -> Dit<Signed> {
                Dit::hold(input())
            }

            #[bench(setup = rind_input)]
            fn rind(signed: &Dit<Signed>) {
                use rind::rsa::{PublicKey, verify};
                let key = PublicKey::new(&signed.public_key).unwrap();
                key.verify(&verify::PKCS1_SHA256, MESSAGE, &signed.signature)
                    .unwrap()
            }

            /// The key's modulus and exponent and the signature, after
            /// checking verified-garbage accepts it.
            fn vg_input() -> ((Vec<u8>, Vec<u8>), Vec<u8>) {
                use verified_garbage::hashes::sha256::Sha256;
                use verified_garbage::rsa::pkcs1_sig::Hash;
                let signed = input();
                let components = vg_components(&signed.public_key);
                vg_public(&components)
                    .verify_pkcs1v15(&signed.signature, &Sha256::digest(MESSAGE), Hash::Sha256)
                    .unwrap();
                (components, signed.signature)
            }

            // Given the modulus and exponent rather than DER, as above.
            #[bench(setup = vg_input)]
            fn verified_garbage((components, signature): &((Vec<u8>, Vec<u8>), Vec<u8>)) {
                use verified_garbage::hashes::sha256::Sha256;
                use verified_garbage::rsa::pkcs1_sig::Hash;
                let key = vg_public(components);
                let digest = Sha256::digest(MESSAGE);
                key.verify_pkcs1v15(signature, &digest, Hash::Sha256)
                    .unwrap()
            }
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
verify_size!(
    rsa2056_pkcs1_sha256_verify,
    "../../rind/src/high/rsa/rsa2056.pkcs8.der"
);
#[cfg(not(target_arch = "xtensa"))]
verify_size!(
    rsa3072_pkcs1_sha256_verify,
    "../../rind/src/high/rsa/rsa3072.pkcs8.der"
);
#[cfg(not(target_arch = "xtensa"))]
verify_size!(
    rsa4096_pkcs1_sha256_verify,
    "../../rind/src/high/rsa/rsa4096.pkcs8.der"
);
#[cfg(not(target_arch = "xtensa"))]
verify_size!(
    rsa6144_pkcs1_sha256_verify,
    "../../rind/src/high/rsa/rsa6144.pkcs8.der"
);
#[cfg(not(target_arch = "xtensa"))]
verify_size!(
    rsa8192_pkcs1_sha256_verify,
    "../../rind/src/high/rsa/rsa8192.pkcs8.der"
);

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
