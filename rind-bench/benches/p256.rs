#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
mod ossl_ec;
#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, dit};

// verified-garbage has no key generation: a random scalar, drawn again until
// it is in range, and its public key.
#[cfg(not(target_arch = "xtensa"))]
fn vg_generate() -> (
    verified_garbage::ec::PrivateKey<verified_garbage::ec::P256>,
    verified_garbage::ec::PublicKey<verified_garbage::ec::P256>,
) {
    loop {
        let mut d = [0u8; 32];
        getrandom::fill(&mut d).unwrap();
        let key = verified_garbage::ec::PrivateKey::from_bytes(&d);
        if let Ok(public_key) = key.public_key() {
            return (key, public_key);
        }
    }
}

#[cfg(not(target_arch = "xtensa"))]
const PUBLIC_KEY: &[u8; 65] = b"\x04\
\x62\xd5\xbd\x33\x72\xaf\x75\xfe\x85\xa0\x40\x71\x5d\x0f\x50\x24\x28\xe0\x70\x46\x86\x8b\x0b\xfd\xfa\x61\xd7\x31\xaf\xe4\x4f\x26\
\xac\x33\x3a\x93\xa9\xe7\x0a\x81\xcd\x5a\x95\xb5\xbf\x8d\x13\x99\x0e\xb7\x41\xc8\xc3\x88\x72\xb4\xa0\x7d\x27\x5a\x01\x4e\x30\xcf";

// The verification rows' key, message, and signature over it.
#[cfg(not(target_arch = "xtensa"))]
const VERIFY_KEY: &[u8; 65] = b"\x04\
\x29\x27\xb1\x05\x12\xba\xe3\xed\xdc\xfe\x46\x78\x28\x12\x8b\xad\x29\x03\x26\x99\x19\xf7\x08\x60\x69\xc8\xc4\xdf\x6c\x73\x28\x38\
\xc7\x78\x79\x64\xea\xac\x00\xe5\x92\x1f\xb1\x49\x8a\x60\xf4\x60\x67\x66\xb3\xd9\x68\x50\x01\x55\x8d\x1a\x97\x4e\x73\x41\x51\x3e";
#[cfg(not(target_arch = "xtensa"))]
const MESSAGE: &[u8] = b"\x31\x32\x33\x34\x30\x30";
#[cfg(not(target_arch = "xtensa"))]
const SIGNATURE: &[u8; 64] = b"\x2b\xa3\xa8\xbe\x6b\x94\xd5\xec\x80\xa6\xd9\xd1\x19\x0a\x43\x6e\xff\xe5\x0d\x85\xa1\xee\xe8\x59\xb8\xcc\x6a\xf9\xbd\x5c\x2e\x18\x4c\xd6\x0b\x85\x5d\x44\x2f\x5b\x3c\x7b\x11\xeb\x6c\x4e\x0a\xe7\x52\x5f\xe7\x10\xfa\xb9\xaa\x7c\x77\xa6\x7f\x79\xe6\xfa\xdd\x76";

// The stored-key rows' scalar.
#[cfg(not(target_arch = "xtensa"))]
const SCALAR: [u8; 32] = [1; 32];

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
fn openssl_curve() -> ossl_ec::Curve {
    ossl_ec::Curve::new(
        openssl::nid::Nid::X9_62_PRIME256V1,
        openssl::hash::MessageDigest::sha256(),
    )
}

#[cfg(not(target_arch = "xtensa"))]
fn ring_rng() -> ring::rand::SystemRandom {
    ring::rand::SystemRandom::new()
}

#[cfg(not(target_arch = "xtensa"))]
fn aws_rng() -> aws_lc_rs::rand::SystemRandom {
    aws_lc_rs::rand::SystemRandom::new()
}

/// The peer's key as verified-garbage takes it, after checking its key
/// agreement against rind's.
#[cfg(not(target_arch = "xtensa"))]
fn vg_peer() -> [u8; 65] {
    vg_agrees_with_rind();
    *PUBLIC_KEY
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_ecdsa_key() -> rind::ecdsa::KeyPair {
    rind::ecdsa::KeyPair::generate(&rind::ecdsa::sign::P256_SHA256_FIXED).unwrap()
}

/// A verified-garbage signing key, after rind verifies its signature.
#[cfg(not(target_arch = "xtensa"))]
fn vg_signing_key() -> verified_garbage::ec::PrivateKey<verified_garbage::ec::P256> {
    use rind::ecdsa::{PublicKey, verify};
    use verified_garbage::hashes::sha256::Sha256;
    let (signing_key, public_key) = vg_generate();
    let rind_key = PublicKey::new(&verify::P256_SHA256_FIXED, public_key.as_bytes()).unwrap();
    let signature = signing_key.sign::<Sha256>(MESSAGE).unwrap();
    rind_key.verify(MESSAGE, &signature).unwrap();
    signing_key
}

#[cfg(not(target_arch = "xtensa"))]
fn vg_verify_key() -> verified_garbage::ec::PublicKey<verified_garbage::ec::P256> {
    verified_garbage::ec::PublicKey::from_bytes(VERIFY_KEY)
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_digest() -> rind::digest::Digest {
    rind::digest::digest(&rind::digest::SHA256, MESSAGE)
}

#[cfg(not(target_arch = "xtensa"))]
fn vg_digest() -> [u8; 32] {
    rind_digest().as_ref().try_into().unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
mod p256_ecdh {
    use swole::bench;

    use super::*;

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_curve)]
    fn openssl(curve: &mut ossl_ec::Curve) {
        curve.ecdh(PUBLIC_KEY)
    }

    #[bench(setup = ring_rng)]
    fn ring(rng: &ring::rand::SystemRandom) {
        use ring::agreement;
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());

        let peer_public_key = agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, PUBLIC_KEY);

        agreement::agree_ephemeral(our_private_key, &peer_public_key, |key_material| {
            black_box(key_material);
        })
        .unwrap();
    }

    #[bench(setup = aws_rng)]
    fn aws_lc_rs(rng: &aws_lc_rs::rand::SystemRandom) {
        use aws_lc_rs::{agreement, error};
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());

        let peer_public_key = agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, PUBLIC_KEY);

        agreement::agree_ephemeral(
            our_private_key,
            peer_public_key,
            error::Unspecified,
            |key_material| {
                black_box(key_material);
                Ok(())
            },
        )
        .unwrap();
    }

    #[bench]
    fn p256_rustcrypto() {
        use p256::PublicKey;
        use p256::ecdh::EphemeralSecret;
        use p256::elliptic_curve::Generate;

        let our_private_key = EphemeralSecret::generate();
        black_box(our_private_key.public_key());

        let peer = PublicKey::from_sec1_bytes(PUBLIC_KEY).unwrap();
        let secret = our_private_key.diffie_hellman(&peer);
        black_box(secret);
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        use rind::agreement::*;
        let our_private_key = PrivateKey::generate(&ECDH_P256).unwrap();
        let our_public_key = our_private_key.public_key();
        black_box(our_public_key);

        let secret = our_private_key.agree(PUBLIC_KEY).unwrap();
        black_box(secret);
    }

    #[bench(setup = vg_peer)]
    fn verified_garbage(peer_bytes: &[u8; 65]) {
        use verified_garbage::ec::PublicKey;
        let (our_private_key, our_public_key) = vg_generate();
        black_box(our_public_key);

        let peer = PublicKey::from_bytes(peer_bytes);
        black_box(our_private_key.exchange(&peer).unwrap());
    }

    #[cfg(graviola)]
    #[bench]
    fn graviola() {
        use graviola::key_agreement::p256::{PrivateKey, PublicKey};

        let our_private_key = PrivateKey::new_random().unwrap();
        black_box(our_private_key.public_key_uncompressed());

        let peer = PublicKey::from_x962_uncompressed(PUBLIC_KEY).unwrap();
        black_box(our_private_key.diffie_hellman(&peer).unwrap());
    }

    #[bench]
    fn libcrux() {
        use libcrux_ecdh::p256::uncompressed_to_coordinates;
        use libcrux_ecdh::{P256PublicKey, p256_derive, p256_key_gen};

        let (our_private_key, our_public_key) = p256_key_gen(&mut getrandom::SysRng).unwrap();
        black_box(our_public_key);

        let peer = P256PublicKey(uncompressed_to_coordinates(PUBLIC_KEY).unwrap());
        black_box(p256_derive(&peer, &our_private_key).unwrap());
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod p256_keygen {
    use swole::bench;

    use super::*;

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench]
    fn openssl() {
        use openssl::pkey::PKey;

        let priv_key = PKey::ec_gen("prime256v1").unwrap();
        black_box(priv_key.public_key_to_der().unwrap());
    }

    #[bench(setup = ring_rng)]
    fn ring(rng: &ring::rand::SystemRandom) {
        use ring::agreement;
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());
    }

    #[bench(setup = aws_rng)]
    fn aws_lc_rs(rng: &aws_lc_rs::rand::SystemRandom) {
        use aws_lc_rs::agreement;
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());
    }

    #[bench]
    fn p256_rustcrypto() {
        use p256::ecdh::EphemeralSecret;
        use p256::elliptic_curve::Generate;

        let our_private_key = EphemeralSecret::generate();
        black_box(our_private_key.public_key());
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        use rind::agreement::*;
        let our_private_key = PrivateKey::generate(&ECDH_P256).unwrap();
        black_box(our_private_key.public_key());
    }

    #[bench(setup = vg_agrees_with_rind)]
    fn verified_garbage(_: &()) {
        black_box(vg_generate());
    }

    #[cfg(graviola)]
    #[bench]
    fn graviola() {
        let key = graviola::key_agreement::p256::PrivateKey::new_random().unwrap();
        black_box(key.public_key_uncompressed());
    }

    #[bench]
    fn libcrux() {
        black_box(libcrux_ecdh::p256_key_gen(&mut getrandom::SysRng).unwrap());
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod p256_ecdsa_keygen {
    use swole::bench;

    use super::*;

    #[bench]
    fn aws_lc_rs() {
        use aws_lc_rs::signature::{ECDSA_P256_SHA256_FIXED_SIGNING, EcdsaKeyPair, KeyPair};

        let key = EcdsaKeyPair::generate(&ECDSA_P256_SHA256_FIXED_SIGNING).unwrap();
        black_box(key.public_key().as_ref());
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        use rind::ecdsa::{KeyPair, sign};

        let key = KeyPair::generate(&sign::P256_SHA256_FIXED).unwrap();
        black_box(key.public_key().as_ref());
    }

    #[bench(setup = vg_agrees_with_rind)]
    fn verified_garbage(_: &()) {
        black_box(vg_generate());
    }
}

/// rind's verification, parsing the key each call as the other rows do.
#[cfg(not(target_arch = "xtensa"))]
fn rind_verify() {
    use rind::ecdsa::{PublicKey, verify};

    PublicKey::new(&verify::P256_SHA256_FIXED, VERIFY_KEY)
        .unwrap()
        .verify(MESSAGE, SIGNATURE)
        .unwrap();
}

#[cfg(not(target_arch = "xtensa"))]
mod p256_ecdsa_verify {
    use swole::bench;

    use super::*;

    fn ring_key() -> ring::signature::UnparsedPublicKey<&'static [u8]> {
        ring::signature::UnparsedPublicKey::new(
            &ring::signature::ECDSA_P256_SHA256_FIXED,
            VERIFY_KEY,
        )
    }

    #[bench(setup = ring_key)]
    fn ring(public_key: &ring::signature::UnparsedPublicKey<&'static [u8]>) {
        public_key.verify(MESSAGE, SIGNATURE).unwrap();
    }

    fn aws_key() -> aws_lc_rs::signature::UnparsedPublicKey<&'static [u8]> {
        aws_lc_rs::signature::UnparsedPublicKey::new(
            &aws_lc_rs::signature::ECDSA_P256_SHA256_FIXED,
            VERIFY_KEY,
        )
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(public_key: &aws_lc_rs::signature::UnparsedPublicKey<&'static [u8]>) {
        public_key.verify(MESSAGE, SIGNATURE).unwrap();
    }

    fn rustcrypto_key() -> p256::ecdsa::VerifyingKey {
        p256::ecdsa::VerifyingKey::from_sec1_bytes(VERIFY_KEY).unwrap()
    }

    #[bench(setup = rustcrypto_key)]
    fn rustcrypto(verifying_key: &p256::ecdsa::VerifyingKey) {
        use p256::ecdsa::{Signature, signature::Verifier};

        verifying_key
            .verify(MESSAGE, &Signature::from_slice(SIGNATURE).unwrap())
            .unwrap();
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        rind_verify();
    }

    // verified-garbage takes the key's bytes and validates it on every verify.
    #[bench(setup = vg_verify_key)]
    fn verified_garbage(public_key: &verified_garbage::ec::PublicKey<verified_garbage::ec::P256>) {
        use verified_garbage::hashes::sha256::Sha256;

        public_key.verify::<Sha256>(MESSAGE, SIGNATURE).unwrap();
    }

    #[cfg(graviola)]
    #[bench]
    fn graviola() {
        use graviola::hashing::Sha256;
        use graviola::signing::ecdsa::{P256, VerifyingKey};

        VerifyingKey::<P256>::from_x962_uncompressed(VERIFY_KEY)
            .unwrap()
            .verify::<Sha256>(&[MESSAGE], SIGNATURE)
            .unwrap();
    }

    fn libcrux_signature() -> libcrux_ecdsa::p256::Signature {
        libcrux_ecdsa::p256::Signature::from_bytes(*SIGNATURE)
    }

    #[bench(setup = libcrux_signature)]
    fn libcrux(signature: &libcrux_ecdsa::p256::Signature) {
        use libcrux_ecdsa::p256::{PublicKey, uncompressed_to_coordinates, verify};

        let public_key = PublicKey(uncompressed_to_coordinates(VERIFY_KEY).unwrap());
        verify(
            libcrux_sha2::Algorithm::Sha256,
            MESSAGE,
            signature,
            &public_key,
        )
        .unwrap();
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl_input() -> (ossl_ec::Curve, Vec<u8>) {
        (openssl_curve(), ossl_ec::Curve::der(SIGNATURE))
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_input)]
    fn openssl((curve, signature): &mut (ossl_ec::Curve, Vec<u8>)) {
        curve.verify(VERIFY_KEY, MESSAGE, signature)
    }
}

// A key parsed once, as a JWT verifier holds it, keeps its multiplication table.
#[cfg(not(target_arch = "xtensa"))]
mod p256_ecdsa_verify_parsed {
    use swole::bench;

    use super::*;

    fn aws_key() -> aws_lc_rs::signature::ParsedPublicKey {
        use aws_lc_rs::signature;
        signature::ParsedPublicKey::new(&signature::ECDSA_P256_SHA256_FIXED, VERIFY_KEY).unwrap()
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(public_key: &aws_lc_rs::signature::ParsedPublicKey) {
        public_key.verify_sig(MESSAGE, SIGNATURE).unwrap();
    }

    fn rind_key() -> Dit<rind::ecdsa::PublicKey> {
        use rind::ecdsa::{PublicKey, verify};
        Dit::hold(PublicKey::new(&verify::P256_SHA256_FIXED, VERIFY_KEY).unwrap())
    }

    #[bench(setup = rind_key)]
    fn rind(public_key: &Dit<rind::ecdsa::PublicKey>) {
        public_key.verify(MESSAGE, SIGNATURE).unwrap();
    }
}

// A digest the caller computed, as node's `createVerify` holds it.
#[cfg(not(target_arch = "xtensa"))]
mod p256_ecdsa_verify_digest {
    use swole::bench;

    use super::*;

    fn aws_input() -> (
        aws_lc_rs::signature::ParsedPublicKey,
        aws_lc_rs::digest::Digest,
    ) {
        use aws_lc_rs::{digest, signature};
        let public_key =
            signature::ParsedPublicKey::new(&signature::ECDSA_P256_SHA256_FIXED, VERIFY_KEY)
                .unwrap();
        (public_key, digest::digest(&digest::SHA256, MESSAGE))
    }

    #[bench(setup = aws_input)]
    fn aws_lc_rs(
        (public_key, digest): &(
            aws_lc_rs::signature::ParsedPublicKey,
            aws_lc_rs::digest::Digest,
        ),
    ) {
        public_key.verify_digest_sig(digest, SIGNATURE).unwrap();
    }

    fn rind_input() -> Dit<(rind::ecdsa::PublicKey, rind::digest::Digest)> {
        use rind::ecdsa::{PublicKey, verify};
        let public_key = PublicKey::new(&verify::P256_SHA256_FIXED, VERIFY_KEY).unwrap();
        Dit::hold((public_key, rind_digest()))
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Dit<(rind::ecdsa::PublicKey, rind::digest::Digest)>) {
        let (public_key, digest) = &**input;
        public_key.verify_digest(digest, SIGNATURE).unwrap();
    }

    fn vg_input() -> (
        verified_garbage::ec::PublicKey<verified_garbage::ec::P256>,
        [u8; 32],
    ) {
        (vg_verify_key(), vg_digest())
    }

    // verified-garbage validates the key on every verify, which rind's row parses once.
    #[bench(setup = vg_input)]
    fn verified_garbage(
        (public_key, digest): &(
            verified_garbage::ec::PublicKey<verified_garbage::ec::P256>,
            [u8; 32],
        ),
    ) {
        use verified_garbage::hashes::sha256::Sha256;

        public_key
            .verify_prehashed::<Sha256>(digest, SIGNATURE)
            .unwrap();
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod p256_ecdsa_sign {
    use swole::bench;

    use super::*;

    fn ring_key() -> (ring::signature::EcdsaKeyPair, ring::rand::SystemRandom) {
        use ring::signature;
        let rng = ring_rng();

        let private_key = signature::EcdsaKeyPair::generate_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            &rng,
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            private_key.as_ref(),
            &rng,
        )
        .unwrap();
        (private_key, rng)
    }

    #[bench(setup = ring_key)]
    fn ring((private_key, rng): &(ring::signature::EcdsaKeyPair, ring::rand::SystemRandom)) {
        black_box(private_key.sign(rng, MESSAGE).unwrap());
    }

    fn aws_key() -> (
        aws_lc_rs::signature::EcdsaKeyPair,
        aws_lc_rs::rand::SystemRandom,
    ) {
        use aws_lc_rs::signature;
        let rng = aws_rng();

        let private_key = signature::EcdsaKeyPair::generate_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            &rng,
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            private_key.as_ref(),
        )
        .unwrap();
        (private_key, rng)
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(
        (private_key, rng): &(
            aws_lc_rs::signature::EcdsaKeyPair,
            aws_lc_rs::rand::SystemRandom,
        ),
    ) {
        black_box(private_key.sign(rng, MESSAGE).unwrap());
    }

    fn rustcrypto_key() -> p256::ecdsa::SigningKey {
        use p256::elliptic_curve::Generate;
        p256::ecdsa::SigningKey::generate()
    }

    #[bench(setup = rustcrypto_key)]
    fn rustcrypto(signing_key: &p256::ecdsa::SigningKey) {
        use p256::ecdsa::{Signature, signature::Signer};

        let signature: Signature = signing_key.sign(MESSAGE);
        black_box(signature);
    }

    fn rind_key() -> Dit<rind::ecdsa::KeyPair> {
        Dit::hold(rind_ecdsa_key())
    }

    #[bench(setup = rind_key)]
    fn rind(signing_key: &Dit<rind::ecdsa::KeyPair>) {
        black_box(signing_key.sign(MESSAGE).unwrap());
    }

    // verified-garbage signs deterministically (RFC 6979), where rind hedges its nonce.
    #[bench(setup = vg_signing_key)]
    fn verified_garbage(
        signing_key: &verified_garbage::ec::PrivateKey<verified_garbage::ec::P256>,
    ) {
        use verified_garbage::hashes::sha256::Sha256;

        black_box(signing_key.sign::<Sha256>(MESSAGE).unwrap());
    }

    #[cfg(graviola)]
    fn graviola_key() -> (
        graviola::signing::ecdsa::SigningKey<graviola::signing::ecdsa::P256>,
        [u8; 64],
    ) {
        use graviola::signing::ecdsa::{P256, SigningKey};
        (SigningKey::<P256>::generate().unwrap(), [0; 64])
    }

    #[cfg(graviola)]
    #[bench(setup = graviola_key)]
    fn graviola(
        (signing_key, signature): &mut (
            graviola::signing::ecdsa::SigningKey<graviola::signing::ecdsa::P256>,
            [u8; 64],
        ),
    ) {
        use graviola::hashing::Sha256;

        black_box(signing_key.sign::<Sha256>(&[MESSAGE], signature).unwrap());
    }

    fn libcrux_key() -> libcrux_ecdsa::p256::PrivateKey {
        use libcrux_ecdsa::p256::rand::generate_key_pair;
        generate_key_pair(&mut getrandom::SysRng).unwrap().0
    }

    #[bench(setup = libcrux_key)]
    fn libcrux(signing_key: &libcrux_ecdsa::p256::PrivateKey) {
        use libcrux_ecdsa::p256::rand::sign;

        black_box(
            sign(
                libcrux_sha2::Algorithm::Sha256,
                MESSAGE,
                signing_key,
                &mut getrandom::SysRng,
            )
            .unwrap(),
        );
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl_key() -> (ossl_ec::Curve, openssl::pkey::PKey<openssl::pkey::Private>) {
        let curve = openssl_curve();
        let signing_key = curve.generate();
        (curve, signing_key)
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_key)]
    fn openssl(
        (curve, signing_key): &(ossl_ec::Curve, openssl::pkey::PKey<openssl::pkey::Private>),
    ) {
        black_box(curve.sign(signing_key, MESSAGE));
    }
}

// A digest the caller computed, as node's `createSign` holds it.
#[cfg(not(target_arch = "xtensa"))]
mod p256_ecdsa_sign_digest {
    use swole::bench;

    use super::*;

    fn aws_input() -> (
        aws_lc_rs::signature::EcdsaKeyPair,
        aws_lc_rs::digest::Digest,
    ) {
        use aws_lc_rs::{digest, signature};
        let private_key = signature::EcdsaKeyPair::generate_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            &aws_rng(),
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            private_key.as_ref(),
        )
        .unwrap();
        (private_key, digest::digest(&digest::SHA256, MESSAGE))
    }

    #[bench(setup = aws_input)]
    fn aws_lc_rs(
        (private_key, digest): &(
            aws_lc_rs::signature::EcdsaKeyPair,
            aws_lc_rs::digest::Digest,
        ),
    ) {
        black_box(private_key.sign_digest(digest).unwrap());
    }

    fn rind_input() -> Dit<(rind::ecdsa::KeyPair, rind::digest::Digest)> {
        Dit::hold((rind_ecdsa_key(), rind_digest()))
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Dit<(rind::ecdsa::KeyPair, rind::digest::Digest)>) {
        let (signing_key, digest) = &**input;
        black_box(signing_key.sign_digest(digest).unwrap());
    }

    fn vg_input() -> (
        verified_garbage::ec::PrivateKey<verified_garbage::ec::P256>,
        [u8; 32],
    ) {
        (vg_signing_key(), vg_digest())
    }

    // verified-garbage signs deterministically (RFC 6979), where rind hedges its nonce.
    #[bench(setup = vg_input)]
    fn verified_garbage(
        (signing_key, digest): &(
            verified_garbage::ec::PrivateKey<verified_garbage::ec::P256>,
            [u8; 32],
        ),
    ) {
        use verified_garbage::hashes::sha256::Sha256;

        black_box(signing_key.sign_prehashed::<Sha256>(digest).unwrap());
    }
}

// Agree with a stored key, loaded once, as WebCrypto's `deriveBits` and
// node's `ECDH` do: the variable-base multiplication alone.
#[cfg(not(target_arch = "xtensa"))]
mod p256_ecdh_stored {
    use swole::bench;

    use super::*;

    fn aws_key() -> aws_lc_rs::agreement::PrivateKey {
        use aws_lc_rs::agreement;
        agreement::PrivateKey::from_private_key(&agreement::ECDH_P256, &SCALAR).unwrap()
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(key: &aws_lc_rs::agreement::PrivateKey) {
        use aws_lc_rs::{agreement, error};

        let peer = agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, PUBLIC_KEY);
        agreement::agree(key, peer, error::Unspecified, |key_material| {
            black_box(key_material);
            Ok(())
        })
        .unwrap();
    }

    fn rind_key() -> Dit<rind::agreement::PrivateKey> {
        use rind::agreement::*;
        Dit::hold(PrivateKey::from_scalar(&ECDH_P256, &SCALAR).unwrap())
    }

    #[bench(setup = rind_key)]
    fn rind(key: &Dit<rind::agreement::PrivateKey>) {
        black_box(key.agree(PUBLIC_KEY).unwrap());
    }

    fn vg_key() -> (
        verified_garbage::ec::PrivateKey<verified_garbage::ec::P256>,
        [u8; 65],
    ) {
        vg_agrees_with_rind();
        (
            verified_garbage::ec::PrivateKey::from_bytes(&SCALAR),
            *PUBLIC_KEY,
        )
    }

    #[bench(setup = vg_key)]
    fn verified_garbage(
        (key, peer_bytes): &(
            verified_garbage::ec::PrivateKey<verified_garbage::ec::P256>,
            [u8; 65],
        ),
    ) {
        use verified_garbage::ec::PublicKey;

        let peer = PublicKey::from_bytes(peer_bytes);
        black_box(key.exchange(&peer).unwrap());
    }
}

#[cfg(target_arch = "aarch64")]
#[cfg(not(target_arch = "xtensa"))]
mod dit_per_call {
    mod p256_ecdsa_verify {
        use swole::bench;

        #[bench]
        fn rind() {
            crate::rind_verify();
        }
    }

    mod p256_ecdsa_sign {
        use std::hint::black_box;

        use swole::bench;

        #[bench(setup = crate::rind_ecdsa_key)]
        fn rind(signing_key: &rind::ecdsa::KeyPair) {
            black_box(signing_key.sign(crate::MESSAGE).unwrap());
        }
    }
}

// Checks verified-garbage's public key and exchange against rind's, from a
// fixed scalar, before any of its rows times them.
#[cfg(not(target_arch = "xtensa"))]
fn vg_agrees_with_rind() {
    use rind::agreement::{self, ECDH_P256};
    use verified_garbage::ec::{PrivateKey, PublicKey};
    let public_key: &[u8] = PUBLIC_KEY;
    let key = PrivateKey::<verified_garbage::ec::P256>::from_bytes(&SCALAR);
    let rind_key = agreement::PrivateKey::from_scalar(&ECDH_P256, &SCALAR).unwrap();
    assert_eq!(
        key.public_key().unwrap().as_bytes()[..],
        *rind_key.public_key().as_ref()
    );
    assert_eq!(
        key.exchange(&PublicKey::from_bytes(PUBLIC_KEY)).unwrap()[..],
        *rind_key.agree(public_key).unwrap().as_ref()
    );
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
