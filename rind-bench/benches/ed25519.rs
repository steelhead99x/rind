#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, dit};

#[cfg(not(target_arch = "xtensa"))]
const PUBLIC_KEY: &[u8; 32] = b"\x7d\x4d\x0e\x7f\x61\x53\xa6\x9b\x62\x42\xb5\x22\xab\xbe\xe6\x85\xfd\xa4\x42\x0f\x88\x34\xb1\x08\xc3\xbd\xae\x36\x9e\xf5\x49\xfa";
#[cfg(not(target_arch = "xtensa"))]
const MESSAGE: &[u8] = b"\x54\x65\x73\x74";
#[cfg(not(target_arch = "xtensa"))]
const SIGNATURE: &[u8; 64] = b"\x7c\x38\xe0\x26\xf2\x9e\x14\xaa\xbd\x05\x9a\x0f\x2d\xb8\xb0\xcd\x78\x30\x40\x60\x9a\x8b\xe6\x84\xdb\x12\xf8\x2a\x27\x77\x4a\xb0\x7a\x91\x55\x71\x1e\xcf\xaf\x7f\x99\xf2\x77\xba\xd0\xc6\xae\x7e\x39\xd4\xee\xf6\x76\x57\x33\x36\xa5\xc5\x1e\xb6\xf9\x46\xb3\x0d";

/// The message the signing rows sign.
#[cfg(not(target_arch = "xtensa"))]
const SIGNED: &[u8] = b"\x31\x32\x33\x34\x30\x30";

#[cfg(not(target_arch = "xtensa"))]
fn rind_public_key() -> rind::ed25519::PublicKey {
    rind::ed25519::PublicKey::new(PUBLIC_KEY).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_verify(public_key: &rind::ed25519::PublicKey) {
    public_key.verify(MESSAGE, SIGNATURE).unwrap();
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_signing_key() -> rind::ed25519::KeyPair {
    rind::ed25519::KeyPair::generate().unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_sign(signing_key: &rind::ed25519::KeyPair) {
    black_box(signing_key.sign(SIGNED));
}

// Generate a fresh key and make a PKCS8 document of it.
#[cfg(not(target_arch = "xtensa"))]
mod ed25519_keygen {
    use swole::bench;

    use super::*;

    fn ring_rng() -> ring::rand::SystemRandom {
        ring::rand::SystemRandom::new()
    }

    #[bench(setup = ring_rng)]
    fn ring(rng: &ring::rand::SystemRandom) {
        black_box(
            ring::signature::Ed25519KeyPair::generate_pkcs8(rng)
                .unwrap()
                .as_ref(),
        );
    }

    fn aws_rng() -> aws_lc_rs::rand::SystemRandom {
        aws_lc_rs::rand::SystemRandom::new()
    }

    #[bench(setup = aws_rng)]
    fn aws_lc_rs(rng: &aws_lc_rs::rand::SystemRandom) {
        black_box(
            aws_lc_rs::signature::Ed25519KeyPair::generate_pkcs8(rng)
                .unwrap()
                .as_ref(),
        );
    }

    #[bench]
    fn dalek() {
        use ed25519_dalek::SigningKey;
        use ed25519_dalek::pkcs8::EncodePrivateKey;
        use getrandom::{SysRng, rand_core::UnwrapErr};

        let key = SigningKey::generate(&mut UnwrapErr(SysRng));
        black_box(key.to_pkcs8_der().unwrap());
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        let our_private_key = rind::ed25519::KeyPair::generate().unwrap();
        black_box(our_private_key.to_pkcs8());
    }

    #[cfg(graviola)]
    fn pkcs8() -> [u8; 128] {
        [0; 128]
    }

    #[cfg(graviola)]
    #[bench(setup = pkcs8)]
    fn graviola(pkcs8: &mut [u8; 128]) {
        let key = graviola::signing::eddsa::Ed25519SigningKey::generate().unwrap();
        black_box(key.to_pkcs8_der(pkcs8).unwrap());
    }

    // libcrux has no PKCS#8 encoding.
    #[bench]
    fn libcrux() {
        black_box(libcrux_ed25519::generate_key_pair(&mut getrandom::SysRng).unwrap());
    }

    /// Checks verified-garbage's public key against rind's, from a fixed seed.
    fn vg_checked() {
        use verified_garbage::ed25519::SigningKey;
        let seed = [7u8; 32];
        assert_eq!(
            SigningKey::from_seed(&seed).verifying_key().as_bytes()[..],
            *rind::ed25519::KeyPair::from_seed(&seed)
                .unwrap()
                .public_key()
                .as_ref()
        );
    }

    // verified-garbage has no key generation or PKCS#8 encoding: a random
    // seed and its public key.
    #[bench(setup = vg_checked)]
    fn verified_garbage(_: &()) {
        use verified_garbage::ed25519::SigningKey;
        let mut seed = [0u8; 32];
        getrandom::fill(&mut seed).unwrap();
        black_box(SigningKey::from_seed(&seed).verifying_key().as_bytes());
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench]
    fn openssl() {
        let key = openssl::pkey::PKey::generate_ed25519().unwrap();
        black_box(key.private_key_to_pkcs8().unwrap());
    }
}

// Each library parses the key once, outside the timed call, where its API
// allows.
#[cfg(not(target_arch = "xtensa"))]
mod ed25519_verify {
    use swole::bench;

    use super::*;

    fn ring_key() -> ring::signature::UnparsedPublicKey<&'static [u8; 32]> {
        ring::signature::UnparsedPublicKey::new(&ring::signature::ED25519, PUBLIC_KEY)
    }

    // ring has no parsed key: `UnparsedPublicKey` parses on every verify.
    #[bench(setup = ring_key)]
    fn ring(public_key: &ring::signature::UnparsedPublicKey<&'static [u8; 32]>) {
        public_key.verify(MESSAGE, SIGNATURE).unwrap();
    }

    fn aws_key() -> aws_lc_rs::signature::ParsedPublicKey {
        aws_lc_rs::signature::ParsedPublicKey::new(&aws_lc_rs::signature::ED25519, PUBLIC_KEY)
            .unwrap()
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(public_key: &aws_lc_rs::signature::ParsedPublicKey) {
        public_key.verify_sig(MESSAGE, SIGNATURE).unwrap();
    }

    fn dalek_key() -> ed25519_dalek::VerifyingKey {
        ed25519_dalek::VerifyingKey::from_bytes(PUBLIC_KEY).unwrap()
    }

    #[bench(setup = dalek_key)]
    fn dalek(verifying_key: &ed25519_dalek::VerifyingKey) {
        use ed25519_dalek::{Signature, Verifier};
        verifying_key
            .verify(MESSAGE, &Signature::from_slice(SIGNATURE).unwrap())
            .unwrap();
    }

    fn rind_key() -> Dit<rind::ed25519::PublicKey> {
        Dit::hold(rind_public_key())
    }

    #[bench(setup = rind_key)]
    fn rind(public_key: &Dit<rind::ed25519::PublicKey>) {
        rind_verify(public_key);
    }

    #[cfg(graviola)]
    fn graviola_key() -> graviola::signing::eddsa::Ed25519VerifyingKey {
        graviola::signing::eddsa::Ed25519VerifyingKey::from_bytes(PUBLIC_KEY).unwrap()
    }

    #[cfg(graviola)]
    #[bench(setup = graviola_key)]
    fn graviola(public_key: &graviola::signing::eddsa::Ed25519VerifyingKey) {
        public_key.verify(SIGNATURE, MESSAGE).unwrap();
    }

    fn vg_key() -> verified_garbage::ed25519::VerifyingKey {
        verified_garbage::ed25519::VerifyingKey::from_bytes(PUBLIC_KEY)
    }

    #[bench(setup = vg_key)]
    fn verified_garbage(public_key: &verified_garbage::ed25519::VerifyingKey) {
        public_key.verify(MESSAGE, SIGNATURE).unwrap();
    }

    // libcrux has no parsed key: `verify` takes the key's bytes.
    #[bench]
    fn libcrux() {
        libcrux_ed25519::verify(MESSAGE, PUBLIC_KEY, SIGNATURE).unwrap();
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl_key() -> openssl::pkey::PKey<openssl::pkey::Public> {
        use openssl::pkey::{Id, PKey};
        PKey::public_key_from_raw_bytes(PUBLIC_KEY, Id::ED25519).unwrap()
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_key)]
    fn openssl(key: &openssl::pkey::PKey<openssl::pkey::Public>) {
        let mut verifier = openssl::sign::Verifier::new_without_digest(key).unwrap();
        assert!(verifier.verify_oneshot(SIGNATURE, MESSAGE).unwrap());
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod ed25519_sign {
    use swole::bench;

    use super::*;

    fn ring_key() -> ring::signature::Ed25519KeyPair {
        use ring::{rand, signature};
        let rng = rand::SystemRandom::new();
        let private_key = signature::Ed25519KeyPair::generate_pkcs8(&rng).unwrap();
        signature::Ed25519KeyPair::from_pkcs8(private_key.as_ref()).unwrap()
    }

    #[bench(setup = ring_key)]
    fn ring(private_key: &ring::signature::Ed25519KeyPair) {
        black_box(private_key.sign(SIGNED));
    }

    fn aws_key() -> aws_lc_rs::signature::Ed25519KeyPair {
        use aws_lc_rs::{rand, signature};
        let rng = rand::SystemRandom::new();
        let private_key = signature::Ed25519KeyPair::generate_pkcs8(&rng).unwrap();
        signature::Ed25519KeyPair::from_pkcs8(private_key.as_ref()).unwrap()
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(private_key: &aws_lc_rs::signature::Ed25519KeyPair) {
        black_box(private_key.sign(SIGNED));
    }

    fn dalek_key() -> ed25519_dalek::SigningKey {
        use getrandom::{SysRng, rand_core::UnwrapErr};
        ed25519_dalek::SigningKey::generate(&mut UnwrapErr(SysRng))
    }

    #[bench(setup = dalek_key)]
    fn dalek(signing_key: &ed25519_dalek::SigningKey) {
        use ed25519_dalek::{Signature, Signer};
        let sig: Signature = signing_key.sign(SIGNED);
        black_box(sig);
    }

    fn rind_key() -> Dit<rind::ed25519::KeyPair> {
        Dit::hold(rind_signing_key())
    }

    #[bench(setup = rind_key)]
    fn rind(signing_key: &Dit<rind::ed25519::KeyPair>) {
        rind_sign(signing_key);
    }

    #[cfg(graviola)]
    fn graviola_key() -> graviola::signing::eddsa::Ed25519SigningKey {
        graviola::signing::eddsa::Ed25519SigningKey::generate().unwrap()
    }

    #[cfg(graviola)]
    #[bench(setup = graviola_key)]
    fn graviola(signing_key: &graviola::signing::eddsa::Ed25519SigningKey) {
        black_box(signing_key.sign(SIGNED));
    }

    /// A random key, after checking it signs as rind's of the same seed
    /// does, and that rind verifies its signature: Ed25519 is deterministic.
    fn vg_key() -> verified_garbage::ed25519::SigningKey {
        use rind::ed25519::{KeyPair, PublicKey};
        let mut seed = [0u8; 32];
        getrandom::fill(&mut seed).unwrap();
        let signing_key = verified_garbage::ed25519::SigningKey::from_seed(&seed);
        let rind_key = KeyPair::from_seed(&seed).unwrap();
        let signature = signing_key.sign(SIGNED);
        assert_eq!(signature[..], *rind_key.sign(SIGNED).as_ref());
        PublicKey::new(signing_key.verifying_key().as_bytes())
            .unwrap()
            .verify(SIGNED, &signature)
            .unwrap();
        signing_key
    }

    #[bench(setup = vg_key)]
    fn verified_garbage(signing_key: &verified_garbage::ed25519::SigningKey) {
        black_box(signing_key.sign(SIGNED));
    }

    fn libcrux_key() -> [u8; 32] {
        let (signing_key, _) = libcrux_ed25519::generate_key_pair(&mut getrandom::SysRng).unwrap();
        signing_key.into_bytes()
    }

    // libcrux signs with the seed alone, deriving the public key each time.
    #[bench(setup = libcrux_key)]
    fn libcrux(signing_key: &[u8; 32]) {
        black_box(libcrux_ed25519::sign(SIGNED, signing_key).unwrap());
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl_key() -> openssl::pkey::PKey<openssl::pkey::Private> {
        openssl::pkey::PKey::generate_ed25519().unwrap()
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_key)]
    fn openssl(signing_key: &openssl::pkey::PKey<openssl::pkey::Private>) {
        let mut signer = openssl::sign::Signer::new_without_digest(signing_key).unwrap();
        black_box(signer.sign_oneshot_to_vec(SIGNED).unwrap());
    }
}

#[cfg(target_arch = "aarch64")]
#[cfg(not(target_arch = "xtensa"))]
mod dit_per_call {
    mod ed25519_verify {
        use swole::bench;

        use super::super::*;

        #[bench(setup = rind_public_key)]
        fn rind(public_key: &rind::ed25519::PublicKey) {
            rind_verify(public_key);
        }
    }

    mod ed25519_sign {
        use swole::bench;

        use super::super::*;

        #[bench(setup = rind_signing_key)]
        fn rind(signing_key: &rind::ed25519::KeyPair) {
            rind_sign(signing_key);
        }
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
