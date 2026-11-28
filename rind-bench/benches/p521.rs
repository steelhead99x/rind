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
    verified_garbage::ec::PrivateKey<verified_garbage::ec::P521>,
    verified_garbage::ec::PublicKey<verified_garbage::ec::P521>,
) {
    loop {
        let mut d = [0u8; 66];
        getrandom::fill(&mut d).unwrap();
        // The order is just under 2^521: keep only the top byte's low bit.
        d[0] &= 1;
        let key = verified_garbage::ec::PrivateKey::from_bytes(&d);
        if let Ok(public_key) = key.public_key() {
            return (key, public_key);
        }
    }
}

// RFC6979 A.2.7's public key, and its SHA-512 signature over "sample".
#[cfg(not(target_arch = "xtensa"))]
const PUBLIC_KEY: &str = "0401894550d0785932e00eaa23b694f213f8c3121f86dc97a04e5a7167db4e5bcd371123d46e45db6b5d5370a7f20fb633155d38ffa16d2bd761dcac474b9a2f5023a400493101c962cd4d2fddf782285e64584139c2f91b47f87ff82354d6630f746a28a0db25741b5b34a828008b22acc23f924faafbd4d33f81ea66956dfeaa2bfdfcf5";
#[cfg(not(target_arch = "xtensa"))]
const MESSAGE: &[u8] = b"sample";
#[cfg(not(target_arch = "xtensa"))]
const SIGNATURE: &str = "00c328fafcbd79dd77850370c46325d987cb525569fb63c5d3bc53950e6d4c5f174e25a1ee9017b5d450606add152b534931d7d4e8455cc91f9b15bf05ec36e377fa00617cce7cf5064806c467f678d3b4080d6f1cc50af26ca209417308281b68af282623eaa63e5b5c0723d8b8c37ff0777b1a20f8ccb1dccc43997f1ee0e44da4a67a";

// The stored-key rows' scalar.
#[cfg(not(target_arch = "xtensa"))]
const SCALAR: [u8; 66] = [1; 66];

#[cfg(not(target_arch = "xtensa"))]
fn public_key() -> Vec<u8> {
    hex::decode(PUBLIC_KEY).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn signature() -> Vec<u8> {
    hex::decode(SIGNATURE).unwrap()
}

/// The public key and the signature over [`MESSAGE`] the verification rows check.
#[cfg(not(target_arch = "xtensa"))]
fn signed() -> (Vec<u8>, Vec<u8>) {
    (public_key(), signature())
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_signed() -> Dit<(Vec<u8>, Vec<u8>)> {
    Dit::hold(signed())
}

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
fn openssl_curve() -> ossl_ec::Curve {
    ossl_ec::Curve::new(
        openssl::nid::Nid::SECP521R1,
        openssl::hash::MessageDigest::sha512(),
    )
}

#[cfg(not(target_arch = "xtensa"))]
fn aws_rng() -> aws_lc_rs::rand::SystemRandom {
    aws_lc_rs::rand::SystemRandom::new()
}

#[cfg(not(target_arch = "xtensa"))]
fn aws_signing_key() -> aws_lc_rs::signature::EcdsaKeyPair {
    use aws_lc_rs::signature;
    let private_key = signature::EcdsaKeyPair::generate_pkcs8(
        &signature::ECDSA_P521_SHA512_FIXED_SIGNING,
        &aws_rng(),
    )
    .unwrap();
    signature::EcdsaKeyPair::from_pkcs8(
        &signature::ECDSA_P521_SHA512_FIXED_SIGNING,
        private_key.as_ref(),
    )
    .unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn aws_verify_key() -> aws_lc_rs::signature::ParsedPublicKey {
    use aws_lc_rs::signature;
    signature::ParsedPublicKey::new(&signature::ECDSA_P521_SHA512_FIXED, public_key()).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_ecdsa_key() -> rind::ecdsa::KeyPair {
    rind::ecdsa::KeyPair::generate(&rind::ecdsa::sign::P521_SHA512_FIXED).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_verify_key() -> rind::ecdsa::PublicKey {
    use rind::ecdsa::{PublicKey, verify};
    PublicKey::new(&verify::P521_SHA512_FIXED, &public_key()).unwrap()
}

/// A verified-garbage signing key, after rind verifies its signature.
#[cfg(not(target_arch = "xtensa"))]
fn vg_signing_key() -> verified_garbage::ec::PrivateKey<verified_garbage::ec::P521> {
    use rind::ecdsa::{PublicKey, verify};
    use verified_garbage::hashes::sha512::Sha512;
    let (signing_key, public_key) = vg_generate();
    let rind_key = PublicKey::new(&verify::P521_SHA512_FIXED, public_key.as_bytes()).unwrap();
    let signature = signing_key.sign::<Sha512>(MESSAGE).unwrap();
    rind_key.verify(MESSAGE, &signature).unwrap();
    signing_key
}

/// verified-garbage's public key and the signature, as it takes them.
#[cfg(not(target_arch = "xtensa"))]
fn vg_signed() -> (
    verified_garbage::ec::PublicKey<verified_garbage::ec::P521>,
    [u8; 132],
) {
    let public_key =
        verified_garbage::ec::PublicKey::from_bytes(&public_key()[..].try_into().unwrap());
    (public_key, signature()[..].try_into().unwrap())
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_digest() -> rind::digest::Digest {
    rind::digest::digest(&rind::digest::SHA512, MESSAGE)
}

#[cfg(not(target_arch = "xtensa"))]
fn vg_digest() -> [u8; 64] {
    rind_digest().as_ref().try_into().unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
mod p521_ecdh {
    use swole::bench;

    use super::*;

    fn aws_input() -> (aws_lc_rs::rand::SystemRandom, Vec<u8>) {
        (aws_rng(), public_key())
    }

    #[bench(setup = aws_input)]
    fn aws_lc_rs((rng, public_key): &(aws_lc_rs::rand::SystemRandom, Vec<u8>)) {
        use aws_lc_rs::{agreement, error};
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P521, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());

        let peer_public_key = agreement::UnparsedPublicKey::new(&agreement::ECDH_P521, public_key);

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

    fn rind_input() -> Dit<Vec<u8>> {
        Dit::hold(public_key())
    }

    #[bench(setup = rind_input)]
    fn rind(public_key: &Dit<Vec<u8>>) {
        use rind::agreement::*;
        let our_private_key = PrivateKey::generate(&ECDH_P521).unwrap();
        let our_public_key = our_private_key.public_key();
        black_box(our_public_key);

        let secret = our_private_key.agree(public_key).unwrap();
        black_box(secret);
    }

    /// The peer's key as verified-garbage takes it, after checking its key
    /// agreement against rind's.
    fn vg_peer() -> [u8; 133] {
        vg_agrees_with_rind();
        public_key()[..].try_into().unwrap()
    }

    #[bench(setup = vg_peer)]
    fn verified_garbage(peer_bytes: &[u8; 133]) {
        use verified_garbage::ec::PublicKey;
        let (our_private_key, our_public_key) = vg_generate();
        black_box(our_public_key);

        let peer = PublicKey::from_bytes(peer_bytes);
        black_box(our_private_key.exchange(&peer).unwrap());
    }

    #[bench(setup = public_key)]
    fn rustcrypto(public_key: &[u8]) {
        use p521::PublicKey;
        use p521::ecdh::EphemeralSecret;
        use p521::elliptic_curve::Generate;

        let our_private_key = EphemeralSecret::generate();
        black_box(our_private_key.public_key());

        let peer = PublicKey::from_sec1_bytes(public_key).unwrap();
        black_box(our_private_key.diffie_hellman(&peer));
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl_input() -> (ossl_ec::Curve, Vec<u8>) {
        (openssl_curve(), public_key())
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_input)]
    fn openssl((curve, public_key): &mut (ossl_ec::Curve, Vec<u8>)) {
        curve.ecdh(public_key)
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod p521_keygen {
    use swole::bench;

    use super::*;

    #[bench(setup = aws_rng)]
    fn aws_lc_rs(rng: &aws_lc_rs::rand::SystemRandom) {
        use aws_lc_rs::agreement;
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P521, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        use rind::agreement::*;
        let our_private_key = PrivateKey::generate(&ECDH_P521).unwrap();
        black_box(our_private_key.public_key());
    }

    #[bench(setup = vg_agrees_with_rind)]
    fn verified_garbage(_: &()) {
        black_box(vg_generate());
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod p521_ecdsa_verify {
    use swole::bench;

    use super::*;

    type AwsKey = aws_lc_rs::signature::UnparsedPublicKey<Vec<u8>>;

    fn aws_input() -> (AwsKey, Vec<u8>) {
        let public_key = aws_lc_rs::signature::UnparsedPublicKey::new(
            &aws_lc_rs::signature::ECDSA_P521_SHA512_FIXED,
            public_key(),
        );
        (public_key, signature())
    }

    #[bench(setup = aws_input)]
    fn aws_lc_rs((public_key, signature): &(AwsKey, Vec<u8>)) {
        public_key.verify(MESSAGE, signature).unwrap();
    }

    #[bench(setup = rind_signed)]
    fn rind(input: &Dit<(Vec<u8>, Vec<u8>)>) {
        use rind::ecdsa::{PublicKey, verify};
        let (public_key, signature) = &**input;

        PublicKey::new(&verify::P521_SHA512_FIXED, public_key)
            .unwrap()
            .verify(MESSAGE, signature)
            .unwrap();
    }

    // verified-garbage takes the key's bytes and validates it on every verify.
    #[bench(setup = vg_signed)]
    fn verified_garbage(
        (public_key, signature): &(
            verified_garbage::ec::PublicKey<verified_garbage::ec::P521>,
            [u8; 132],
        ),
    ) {
        use verified_garbage::hashes::sha512::Sha512;

        public_key.verify::<Sha512>(MESSAGE, signature).unwrap();
    }

    #[bench(setup = signed)]
    fn rustcrypto((public_key, signature): &(Vec<u8>, Vec<u8>)) {
        use p521::ecdsa::{Signature, VerifyingKey, signature::Verifier};

        VerifyingKey::from_sec1_bytes(public_key)
            .unwrap()
            .verify(MESSAGE, &Signature::from_slice(signature).unwrap())
            .unwrap();
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl_input() -> (ossl_ec::Curve, Vec<u8>, Vec<u8>) {
        (
            openssl_curve(),
            public_key(),
            ossl_ec::Curve::der(&signature()),
        )
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_input)]
    fn openssl((curve, public_key, signature): &mut (ossl_ec::Curve, Vec<u8>, Vec<u8>)) {
        curve.verify(public_key, MESSAGE, signature)
    }
}

// A key parsed once, as a JWT verifier holds it, keeps its multiplication table.
#[cfg(not(target_arch = "xtensa"))]
mod p521_ecdsa_verify_parsed {
    use swole::bench;

    use super::*;

    fn aws_input() -> (aws_lc_rs::signature::ParsedPublicKey, Vec<u8>) {
        (aws_verify_key(), signature())
    }

    #[bench(setup = aws_input)]
    fn aws_lc_rs((public_key, signature): &(aws_lc_rs::signature::ParsedPublicKey, Vec<u8>)) {
        public_key.verify_sig(MESSAGE, signature).unwrap();
    }

    fn rind_input() -> Dit<(rind::ecdsa::PublicKey, Vec<u8>)> {
        Dit::hold((rind_verify_key(), signature()))
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Dit<(rind::ecdsa::PublicKey, Vec<u8>)>) {
        let (public_key, signature) = &**input;
        public_key.verify(MESSAGE, signature).unwrap();
    }
}

// A digest the caller computed, as node's `createVerify` holds it.
#[cfg(not(target_arch = "xtensa"))]
mod p521_ecdsa_verify_digest {
    use swole::bench;

    use super::*;

    fn aws_input() -> (
        aws_lc_rs::signature::ParsedPublicKey,
        aws_lc_rs::digest::Digest,
        Vec<u8>,
    ) {
        use aws_lc_rs::digest;
        (
            aws_verify_key(),
            digest::digest(&digest::SHA512, MESSAGE),
            signature(),
        )
    }

    #[bench(setup = aws_input)]
    fn aws_lc_rs(
        (public_key, digest, signature): &(
            aws_lc_rs::signature::ParsedPublicKey,
            aws_lc_rs::digest::Digest,
            Vec<u8>,
        ),
    ) {
        public_key.verify_digest_sig(digest, signature).unwrap();
    }

    fn rind_input() -> Dit<(rind::ecdsa::PublicKey, rind::digest::Digest, Vec<u8>)> {
        Dit::hold((rind_verify_key(), rind_digest(), signature()))
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Dit<(rind::ecdsa::PublicKey, rind::digest::Digest, Vec<u8>)>) {
        let (public_key, digest, signature) = &**input;
        public_key.verify_digest(digest, signature).unwrap();
    }

    fn vg_input() -> (
        verified_garbage::ec::PublicKey<verified_garbage::ec::P521>,
        [u8; 132],
        [u8; 64],
    ) {
        let (public_key, signature) = vg_signed();
        (public_key, signature, vg_digest())
    }

    // verified-garbage validates the key on every verify, which rind's row parses once.
    #[bench(setup = vg_input)]
    fn verified_garbage(
        (public_key, signature, digest): &(
            verified_garbage::ec::PublicKey<verified_garbage::ec::P521>,
            [u8; 132],
            [u8; 64],
        ),
    ) {
        use verified_garbage::hashes::sha512::Sha512;

        public_key
            .verify_prehashed::<Sha512>(digest, signature)
            .unwrap();
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod p521_ecdsa_sign {
    use swole::bench;

    use super::*;

    fn aws_key() -> (
        aws_lc_rs::signature::EcdsaKeyPair,
        aws_lc_rs::rand::SystemRandom,
    ) {
        (aws_signing_key(), aws_rng())
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
        signing_key: &verified_garbage::ec::PrivateKey<verified_garbage::ec::P521>,
    ) {
        use verified_garbage::hashes::sha512::Sha512;

        black_box(signing_key.sign::<Sha512>(MESSAGE).unwrap());
    }

    fn rustcrypto_key() -> p521::ecdsa::SigningKey {
        use p521::elliptic_curve::Generate;
        p521::ecdsa::SigningKey::generate()
    }

    #[bench(setup = rustcrypto_key)]
    fn rustcrypto(signing_key: &p521::ecdsa::SigningKey) {
        use p521::ecdsa::{Signature, signature::Signer};

        let signature: Signature = signing_key.sign(MESSAGE);
        black_box(signature);
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
mod p521_ecdsa_sign_digest {
    use swole::bench;

    use super::*;

    fn aws_input() -> (
        aws_lc_rs::signature::EcdsaKeyPair,
        aws_lc_rs::digest::Digest,
    ) {
        use aws_lc_rs::digest;
        (aws_signing_key(), digest::digest(&digest::SHA512, MESSAGE))
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
        verified_garbage::ec::PrivateKey<verified_garbage::ec::P521>,
        [u8; 64],
    ) {
        (vg_signing_key(), vg_digest())
    }

    // verified-garbage signs deterministically (RFC 6979), where rind hedges its nonce.
    #[bench(setup = vg_input)]
    fn verified_garbage(
        (signing_key, digest): &(
            verified_garbage::ec::PrivateKey<verified_garbage::ec::P521>,
            [u8; 64],
        ),
    ) {
        use verified_garbage::hashes::sha512::Sha512;

        black_box(signing_key.sign_prehashed::<Sha512>(digest).unwrap());
    }
}

// Agree with a stored key, loaded once, as WebCrypto's `deriveBits` and
// node's `ECDH` do: the variable-base multiplication alone.
#[cfg(not(target_arch = "xtensa"))]
mod p521_ecdh_stored {
    use swole::bench;

    use super::*;

    fn aws_key() -> (aws_lc_rs::agreement::PrivateKey, Vec<u8>) {
        use aws_lc_rs::agreement;
        let key = agreement::PrivateKey::from_private_key(&agreement::ECDH_P521, &SCALAR).unwrap();
        (key, public_key())
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs((key, public_key): &(aws_lc_rs::agreement::PrivateKey, Vec<u8>)) {
        use aws_lc_rs::{agreement, error};

        let peer = agreement::UnparsedPublicKey::new(&agreement::ECDH_P521, public_key);
        agreement::agree(key, peer, error::Unspecified, |key_material| {
            black_box(key_material);
            Ok(())
        })
        .unwrap();
    }

    fn rind_key() -> Dit<(rind::agreement::PrivateKey, Vec<u8>)> {
        use rind::agreement::*;
        let key = PrivateKey::from_scalar(&ECDH_P521, &SCALAR).unwrap();
        Dit::hold((key, public_key()))
    }

    #[bench(setup = rind_key)]
    fn rind(input: &Dit<(rind::agreement::PrivateKey, Vec<u8>)>) {
        let (key, public_key) = &**input;
        black_box(key.agree(public_key).unwrap());
    }

    fn vg_key() -> (
        verified_garbage::ec::PrivateKey<verified_garbage::ec::P521>,
        [u8; 133],
    ) {
        vg_agrees_with_rind();
        (
            verified_garbage::ec::PrivateKey::from_bytes(&SCALAR),
            public_key()[..].try_into().unwrap(),
        )
    }

    #[bench(setup = vg_key)]
    fn verified_garbage(
        (key, peer_bytes): &(
            verified_garbage::ec::PrivateKey<verified_garbage::ec::P521>,
            [u8; 133],
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
    use rind::agreement::{self, ECDH_P521};
    use verified_garbage::ec::{PrivateKey, PublicKey};
    let public_key = public_key();
    let key = PrivateKey::<verified_garbage::ec::P521>::from_bytes(&SCALAR);
    let peer_bytes: [u8; 133] = public_key[..].try_into().unwrap();
    let rind_key = agreement::PrivateKey::from_scalar(&ECDH_P521, &SCALAR).unwrap();
    assert_eq!(
        key.public_key().unwrap().as_bytes()[..],
        *rind_key.public_key().as_ref()
    );
    assert_eq!(
        key.exchange(&PublicKey::from_bytes(&peer_bytes)).unwrap()[..],
        *rind_key.agree(&public_key).unwrap().as_ref()
    );
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
