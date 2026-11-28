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
    verified_garbage::ec::PrivateKey<verified_garbage::ec::P384>,
    verified_garbage::ec::PublicKey<verified_garbage::ec::P384>,
) {
    loop {
        let mut d = [0u8; 48];
        getrandom::fill(&mut d).unwrap();
        let key = verified_garbage::ec::PrivateKey::from_bytes(&d);
        if let Ok(public_key) = key.public_key() {
            return (key, public_key);
        }
    }
}

#[cfg(not(target_arch = "xtensa"))]
const PUBLIC_KEY: &[u8; 97] = &[
    0x04, 0x7a, 0x6e, 0xc8, 0xd3, 0x11, 0xd5, 0xca, 0x58, 0x8b, 0xae, 0xd4, 0x1b, 0xe3, 0xe9, 0x8f,
    0x30, 0xc9, 0x29, 0x48, 0x44, 0xec, 0xbb, 0x62, 0x99, 0x95, 0x65, 0x36, 0x35, 0xdb, 0xc2, 0x2d,
    0xa2, 0xf0, 0x83, 0xf2, 0x97, 0x11, 0xe0, 0xf9, 0xc5, 0x96, 0x3b, 0xc0, 0x21, 0xbd, 0x8c, 0xb2,
    0x10, 0x9d, 0xaf, 0x56, 0xa5, 0x5f, 0x88, 0x3a, 0x72, 0x00, 0xce, 0xa9, 0xc4, 0xde, 0x44, 0x48,
    0x8e, 0x6d, 0xc4, 0x9f, 0xb9, 0xc3, 0x94, 0xf5, 0x1c, 0xb5, 0xa4, 0x9f, 0xc6, 0x9d, 0x7e, 0x8a,
    0x03, 0x47, 0x92, 0x96, 0x3a, 0xe4, 0xea, 0xbc, 0x63, 0x48, 0x3a, 0x2c, 0xf1, 0xa8, 0x99, 0xe8,
    0xc8,
];

// The verification rows' key, message, and signature over it.
#[cfg(not(target_arch = "xtensa"))]
const VERIFY_KEY: &[u8; 97] = &[
    0x04, 0x2d, 0xa5, 0x7d, 0xda, 0x10, 0x89, 0x27, 0x6a, 0x54, 0x3f, 0x9f, 0xfd, 0xac, 0x0b, 0xff,
    0x0d, 0x97, 0x6c, 0xad, 0x71, 0xeb, 0x72, 0x80, 0xe7, 0xd9, 0xbf, 0xd9, 0xfe, 0xe4, 0xbd, 0xb2,
    0xf2, 0x0f, 0x47, 0xff, 0x88, 0x82, 0x74, 0x38, 0x97, 0x72, 0xd9, 0x8c, 0xc5, 0x75, 0x21, 0x38,
    0xaa, 0x4b, 0x6d, 0x05, 0x4d, 0x69, 0xdc, 0xf3, 0xe2, 0x5e, 0xc4, 0x9d, 0xf8, 0x70, 0x71, 0x5e,
    0x34, 0x88, 0x3b, 0x18, 0x36, 0x19, 0x7d, 0x76, 0xf8, 0xad, 0x96, 0x2e, 0x78, 0xf6, 0x57, 0x1b,
    0xbc, 0x74, 0x07, 0xb0, 0xd6, 0x09, 0x1f, 0x9e, 0x4d, 0x88, 0xf0, 0x14, 0x27, 0x44, 0x06, 0x17,
    0x4f,
];
#[cfg(not(target_arch = "xtensa"))]
const MESSAGE: &[u8] = b"\x31\x32\x33\x34\x30\x30";
#[cfg(not(target_arch = "xtensa"))]
const SIGNATURE: &[u8; 96] = &[
    0x12, 0xb3, 0x0a, 0xbe, 0xf6, 0xb5, 0x47, 0x6f, 0xe6, 0xb6, 0x12, 0xae, 0x55, 0x7c, 0x04, 0x25,
    0x66, 0x1e, 0x26, 0xb4, 0x4b, 0x1b, 0xfe, 0x19, 0xda, 0xf2, 0xca, 0x28, 0xe3, 0x11, 0x30, 0x83,
    0xba, 0x8e, 0x4a, 0xe4, 0xcc, 0x45, 0xa0, 0x32, 0x0a, 0xbd, 0x33, 0x94, 0xf1, 0xc5, 0x48, 0xd7,
    0x18, 0x40, 0xda, 0x9f, 0xc1, 0xd2, 0xf8, 0xf8, 0x90, 0x0c, 0xf4, 0x85, 0xd5, 0x41, 0x3b, 0x8c,
    0x25, 0x74, 0xee, 0x3a, 0x8d, 0x4c, 0xa0, 0x39, 0x95, 0xca, 0x30, 0x24, 0x0e, 0x09, 0x51, 0x38,
    0x05, 0xbf, 0x62, 0x09, 0xb5, 0x8a, 0xc7, 0xaa, 0x9c, 0xff, 0x54, 0xee, 0xcd, 0x82, 0xb9, 0xf1,
];

// The stored-key rows' scalar.
#[cfg(not(target_arch = "xtensa"))]
const SCALAR: [u8; 48] = [1; 48];

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
fn openssl_curve() -> ossl_ec::Curve {
    ossl_ec::Curve::new(
        openssl::nid::Nid::SECP384R1,
        openssl::hash::MessageDigest::sha384(),
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
fn vg_peer() -> [u8; 97] {
    vg_agrees_with_rind();
    *PUBLIC_KEY
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_ecdsa_key() -> rind::ecdsa::KeyPair {
    rind::ecdsa::KeyPair::generate(&rind::ecdsa::sign::P384_SHA384_FIXED).unwrap()
}

/// A verified-garbage signing key, after rind verifies its signature.
#[cfg(not(target_arch = "xtensa"))]
fn vg_signing_key() -> verified_garbage::ec::PrivateKey<verified_garbage::ec::P384> {
    use rind::ecdsa::{PublicKey, verify};
    use verified_garbage::hashes::sha384::Sha384;
    let (signing_key, public_key) = vg_generate();
    let rind_key = PublicKey::new(&verify::P384_SHA384_FIXED, public_key.as_bytes()).unwrap();
    let signature = signing_key.sign::<Sha384>(MESSAGE).unwrap();
    rind_key.verify(MESSAGE, &signature).unwrap();
    signing_key
}

#[cfg(not(target_arch = "xtensa"))]
fn vg_verify_key() -> verified_garbage::ec::PublicKey<verified_garbage::ec::P384> {
    verified_garbage::ec::PublicKey::from_bytes(VERIFY_KEY)
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_digest() -> rind::digest::Digest {
    rind::digest::digest(&rind::digest::SHA384, MESSAGE)
}

#[cfg(not(target_arch = "xtensa"))]
fn vg_digest() -> [u8; 48] {
    rind_digest().as_ref().try_into().unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
mod p384_ecdh {
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
            agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P384, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());

        let peer_public_key = agreement::UnparsedPublicKey::new(&agreement::ECDH_P384, PUBLIC_KEY);

        agreement::agree_ephemeral(our_private_key, &peer_public_key, |key_material| {
            black_box(key_material);
        })
        .unwrap();
    }

    #[bench(setup = aws_rng)]
    fn aws_lc_rs(rng: &aws_lc_rs::rand::SystemRandom) {
        use aws_lc_rs::{agreement, error};
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P384, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());

        let peer_public_key = agreement::UnparsedPublicKey::new(&agreement::ECDH_P384, PUBLIC_KEY);

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
    fn p384_rustcrypto() {
        use p384::PublicKey;
        use p384::ecdh::EphemeralSecret;
        use p384::elliptic_curve::Generate;

        let our_private_key = EphemeralSecret::generate();
        black_box(our_private_key.public_key());

        let peer = PublicKey::from_sec1_bytes(PUBLIC_KEY).unwrap();
        let secret = our_private_key.diffie_hellman(&peer);
        black_box(secret);
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        use rind::agreement::*;
        let our_private_key = PrivateKey::generate(&ECDH_P384).unwrap();
        let our_public_key = our_private_key.public_key();
        black_box(our_public_key);

        let secret = our_private_key.agree(PUBLIC_KEY).unwrap();
        black_box(secret);
    }

    #[bench(setup = vg_peer)]
    fn verified_garbage(peer_bytes: &[u8; 97]) {
        use verified_garbage::ec::PublicKey;
        let (our_private_key, our_public_key) = vg_generate();
        black_box(our_public_key);

        let peer = PublicKey::from_bytes(peer_bytes);
        black_box(our_private_key.exchange(&peer).unwrap());
    }

    #[cfg(graviola)]
    #[bench]
    fn graviola() {
        use graviola::key_agreement::p384::{PrivateKey, PublicKey};

        let our_private_key = PrivateKey::new_random().unwrap();
        black_box(our_private_key.public_key_uncompressed());

        let peer = PublicKey::from_x962_uncompressed(PUBLIC_KEY).unwrap();
        black_box(our_private_key.diffie_hellman(&peer).unwrap());
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod p384_keygen {
    use swole::bench;

    use super::*;

    #[bench(setup = ring_rng)]
    fn ring(rng: &ring::rand::SystemRandom) {
        use ring::agreement;
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P384, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());
    }

    #[bench(setup = aws_rng)]
    fn aws_lc_rs(rng: &aws_lc_rs::rand::SystemRandom) {
        use aws_lc_rs::agreement;
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P384, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());
    }

    #[bench]
    fn p384_rustcrypto() {
        use p384::ecdh::EphemeralSecret;
        use p384::elliptic_curve::Generate;

        let our_private_key = EphemeralSecret::generate();
        black_box(our_private_key.public_key());
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        use rind::agreement::*;
        let our_private_key = PrivateKey::generate(&ECDH_P384).unwrap();
        black_box(our_private_key.public_key());
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

    PublicKey::new(&verify::P384_SHA384_FIXED, VERIFY_KEY)
        .unwrap()
        .verify(MESSAGE, SIGNATURE)
        .unwrap();
}

#[cfg(not(target_arch = "xtensa"))]
mod p384_ecdsa_verify {
    use swole::bench;

    use super::*;

    fn ring_key() -> ring::signature::UnparsedPublicKey<&'static [u8]> {
        ring::signature::UnparsedPublicKey::new(
            &ring::signature::ECDSA_P384_SHA384_FIXED,
            VERIFY_KEY,
        )
    }

    #[bench(setup = ring_key)]
    fn ring(public_key: &ring::signature::UnparsedPublicKey<&'static [u8]>) {
        public_key.verify(MESSAGE, SIGNATURE).unwrap();
    }

    fn aws_key() -> aws_lc_rs::signature::UnparsedPublicKey<&'static [u8]> {
        aws_lc_rs::signature::UnparsedPublicKey::new(
            &aws_lc_rs::signature::ECDSA_P384_SHA384_FIXED,
            VERIFY_KEY,
        )
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(public_key: &aws_lc_rs::signature::UnparsedPublicKey<&'static [u8]>) {
        public_key.verify(MESSAGE, SIGNATURE).unwrap();
    }

    fn rustcrypto_key() -> p384::ecdsa::VerifyingKey {
        p384::ecdsa::VerifyingKey::from_sec1_bytes(VERIFY_KEY).unwrap()
    }

    #[bench(setup = rustcrypto_key)]
    fn rustcrypto(verifying_key: &p384::ecdsa::VerifyingKey) {
        use p384::ecdsa::{Signature, signature::Verifier};

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
    fn verified_garbage(public_key: &verified_garbage::ec::PublicKey<verified_garbage::ec::P384>) {
        use verified_garbage::hashes::sha384::Sha384;

        public_key.verify::<Sha384>(MESSAGE, SIGNATURE).unwrap();
    }

    #[cfg(graviola)]
    #[bench]
    fn graviola() {
        use graviola::hashing::Sha384;
        use graviola::signing::ecdsa::{P384, VerifyingKey};

        VerifyingKey::<P384>::from_x962_uncompressed(VERIFY_KEY)
            .unwrap()
            .verify::<Sha384>(&[MESSAGE], SIGNATURE)
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
mod p384_ecdsa_verify_parsed {
    use swole::bench;

    use super::*;

    fn aws_key() -> aws_lc_rs::signature::ParsedPublicKey {
        use aws_lc_rs::signature;
        signature::ParsedPublicKey::new(&signature::ECDSA_P384_SHA384_FIXED, VERIFY_KEY).unwrap()
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(public_key: &aws_lc_rs::signature::ParsedPublicKey) {
        public_key.verify_sig(MESSAGE, SIGNATURE).unwrap();
    }

    fn rind_key() -> Dit<rind::ecdsa::PublicKey> {
        use rind::ecdsa::{PublicKey, verify};
        Dit::hold(PublicKey::new(&verify::P384_SHA384_FIXED, VERIFY_KEY).unwrap())
    }

    #[bench(setup = rind_key)]
    fn rind(public_key: &Dit<rind::ecdsa::PublicKey>) {
        public_key.verify(MESSAGE, SIGNATURE).unwrap();
    }
}

// A digest the caller computed, as node's `createVerify` holds it.
#[cfg(not(target_arch = "xtensa"))]
mod p384_ecdsa_verify_digest {
    use swole::bench;

    use super::*;

    fn aws_input() -> (
        aws_lc_rs::signature::ParsedPublicKey,
        aws_lc_rs::digest::Digest,
    ) {
        use aws_lc_rs::{digest, signature};
        let public_key =
            signature::ParsedPublicKey::new(&signature::ECDSA_P384_SHA384_FIXED, VERIFY_KEY)
                .unwrap();
        (public_key, digest::digest(&digest::SHA384, MESSAGE))
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
        let public_key = PublicKey::new(&verify::P384_SHA384_FIXED, VERIFY_KEY).unwrap();
        Dit::hold((public_key, rind_digest()))
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Dit<(rind::ecdsa::PublicKey, rind::digest::Digest)>) {
        let (public_key, digest) = &**input;
        public_key.verify_digest(digest, SIGNATURE).unwrap();
    }

    fn vg_input() -> (
        verified_garbage::ec::PublicKey<verified_garbage::ec::P384>,
        [u8; 48],
    ) {
        (vg_verify_key(), vg_digest())
    }

    // verified-garbage validates the key on every verify, which rind's row parses once.
    #[bench(setup = vg_input)]
    fn verified_garbage(
        (public_key, digest): &(
            verified_garbage::ec::PublicKey<verified_garbage::ec::P384>,
            [u8; 48],
        ),
    ) {
        use verified_garbage::hashes::sha384::Sha384;

        public_key
            .verify_prehashed::<Sha384>(digest, SIGNATURE)
            .unwrap();
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod p384_ecdsa_sign {
    use swole::bench;

    use super::*;

    fn ring_key() -> (ring::signature::EcdsaKeyPair, ring::rand::SystemRandom) {
        use ring::signature;
        let rng = ring_rng();

        let private_key = signature::EcdsaKeyPair::generate_pkcs8(
            &signature::ECDSA_P384_SHA384_FIXED_SIGNING,
            &rng,
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P384_SHA384_FIXED_SIGNING,
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
            &signature::ECDSA_P384_SHA384_FIXED_SIGNING,
            &rng,
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P384_SHA384_FIXED_SIGNING,
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

    fn rustcrypto_key() -> p384::ecdsa::SigningKey {
        use p384::elliptic_curve::Generate;
        p384::ecdsa::SigningKey::generate()
    }

    #[bench(setup = rustcrypto_key)]
    fn rustcrypto(signing_key: &p384::ecdsa::SigningKey) {
        use p384::ecdsa::{Signature, signature::Signer};

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
        signing_key: &verified_garbage::ec::PrivateKey<verified_garbage::ec::P384>,
    ) {
        use verified_garbage::hashes::sha384::Sha384;

        black_box(signing_key.sign::<Sha384>(MESSAGE).unwrap());
    }

    #[cfg(graviola)]
    fn graviola_key() -> (
        graviola::signing::ecdsa::SigningKey<graviola::signing::ecdsa::P384>,
        [u8; 96],
    ) {
        use graviola::signing::ecdsa::{P384, SigningKey};
        (SigningKey::<P384>::generate().unwrap(), [0; 96])
    }

    #[cfg(graviola)]
    #[bench(setup = graviola_key)]
    fn graviola(
        (signing_key, signature): &mut (
            graviola::signing::ecdsa::SigningKey<graviola::signing::ecdsa::P384>,
            [u8; 96],
        ),
    ) {
        use graviola::hashing::Sha384;

        black_box(signing_key.sign::<Sha384>(&[MESSAGE], signature).unwrap());
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
mod p384_ecdsa_sign_digest {
    use swole::bench;

    use super::*;

    fn aws_input() -> (
        aws_lc_rs::signature::EcdsaKeyPair,
        aws_lc_rs::digest::Digest,
    ) {
        use aws_lc_rs::{digest, signature};
        let private_key = signature::EcdsaKeyPair::generate_pkcs8(
            &signature::ECDSA_P384_SHA384_FIXED_SIGNING,
            &aws_rng(),
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P384_SHA384_FIXED_SIGNING,
            private_key.as_ref(),
        )
        .unwrap();
        (private_key, digest::digest(&digest::SHA384, MESSAGE))
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
        verified_garbage::ec::PrivateKey<verified_garbage::ec::P384>,
        [u8; 48],
    ) {
        (vg_signing_key(), vg_digest())
    }

    // verified-garbage signs deterministically (RFC 6979), where rind hedges its nonce.
    #[bench(setup = vg_input)]
    fn verified_garbage(
        (signing_key, digest): &(
            verified_garbage::ec::PrivateKey<verified_garbage::ec::P384>,
            [u8; 48],
        ),
    ) {
        use verified_garbage::hashes::sha384::Sha384;

        black_box(signing_key.sign_prehashed::<Sha384>(digest).unwrap());
    }
}

// Agree with a stored key, loaded once, as WebCrypto's `deriveBits` and
// node's `ECDH` do: the variable-base multiplication alone.
#[cfg(not(target_arch = "xtensa"))]
mod p384_ecdh_stored {
    use swole::bench;

    use super::*;

    fn aws_key() -> aws_lc_rs::agreement::PrivateKey {
        use aws_lc_rs::agreement;
        agreement::PrivateKey::from_private_key(&agreement::ECDH_P384, &SCALAR).unwrap()
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(key: &aws_lc_rs::agreement::PrivateKey) {
        use aws_lc_rs::{agreement, error};

        let peer = agreement::UnparsedPublicKey::new(&agreement::ECDH_P384, PUBLIC_KEY);
        agreement::agree(key, peer, error::Unspecified, |key_material| {
            black_box(key_material);
            Ok(())
        })
        .unwrap();
    }

    fn rind_key() -> Dit<rind::agreement::PrivateKey> {
        use rind::agreement::*;
        Dit::hold(PrivateKey::from_scalar(&ECDH_P384, &SCALAR).unwrap())
    }

    #[bench(setup = rind_key)]
    fn rind(key: &Dit<rind::agreement::PrivateKey>) {
        black_box(key.agree(PUBLIC_KEY).unwrap());
    }

    fn vg_key() -> (
        verified_garbage::ec::PrivateKey<verified_garbage::ec::P384>,
        [u8; 97],
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
            verified_garbage::ec::PrivateKey<verified_garbage::ec::P384>,
            [u8; 97],
        ),
    ) {
        use verified_garbage::ec::PublicKey;

        let peer = PublicKey::from_bytes(peer_bytes);
        black_box(key.exchange(&peer).unwrap());
    }
}

// Checks verified-garbage's public key and exchange against rind's, from a
// fixed scalar, before any of its rows times them.
#[cfg(not(target_arch = "xtensa"))]
fn vg_agrees_with_rind() {
    use rind::agreement::{self, ECDH_P384};
    use verified_garbage::ec::{PrivateKey, PublicKey};
    let public_key: &[u8] = PUBLIC_KEY;
    let key = PrivateKey::<verified_garbage::ec::P384>::from_bytes(&SCALAR);
    let rind_key = agreement::PrivateKey::from_scalar(&ECDH_P384, &SCALAR).unwrap();
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
