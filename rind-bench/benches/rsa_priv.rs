//! RSA signing, OAEP decryption, and key loading, the private-key side.

#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, dit};

#[cfg(not(target_arch = "xtensa"))]
const PRIVATE_KEY_2048: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2048.der");

#[cfg(not(target_arch = "xtensa"))]
const MESSAGE: &[u8] = &[0; 20];

/// libcrux's RSA-PSS key, which holds the modulus and private exponent
/// alone, so it signs without the CRT.
#[cfg(not(target_arch = "xtensa"))]
fn libcrux_key(private_key: &[u8]) -> libcrux_rsa::PrivateKey<256> {
    use rsa::pkcs1::DecodeRsaPrivateKey;
    use rsa::traits::{PrivateKeyParts, PublicKeyParts};
    let key = rsa::PrivateKey::from_pkcs1_der(private_key).unwrap();
    let be = |bytes: &[u8]| {
        let mut out = [0u8; 256];
        out[256 - bytes.len()..].copy_from_slice(bytes);
        out
    };
    libcrux_rsa::PrivateKey::<256>::from_components(
        be(&key.n_bytes()),
        be(&key.d().to_be_bytes_trimmed_vartime()),
    )
}

/// verified-garbage's key of a PKCS#1 or PKCS#8 private key's components,
/// since it takes them in place of DER.
#[cfg(not(target_arch = "xtensa"))]
fn vg_key(private_key: &[u8]) -> verified_garbage::rsa::PrivateKey {
    use rsa::pkcs1::DecodeRsaPrivateKey;
    use rsa::pkcs8::DecodePrivateKey;
    use rsa::traits::{PrivateKeyParts, PublicKeyParts};
    use verified_garbage::rsa::{BigUint, PrivateKey};
    let key = rsa::PrivateKey::from_pkcs1_der(private_key)
        .or_else(|_| rsa::PrivateKey::from_pkcs8_der(private_key))
        .unwrap();
    let [p, q] = key.primes() else {
        panic!("a two-prime key")
    };
    let (d, p, q) = (
        key.d().to_be_bytes_trimmed_vartime(),
        p.to_be_bytes_trimmed_vartime(),
        q.to_be_bytes_trimmed_vartime(),
    );
    PrivateKey::from_primes(
        BigUint::from_be_bytes(&key.n_bytes()),
        BigUint::from_be_bytes(&key.e_bytes()),
        BigUint::from_be_bytes(&d),
        BigUint::from_be_bytes(&p),
        BigUint::from_be_bytes(&q),
    )
    .unwrap()
}

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
fn openssl_key() -> openssl::pkey::PKey<openssl::pkey::Private> {
    use openssl::pkey::PKey;
    use openssl::rsa::Rsa;
    PKey::from_rsa(Rsa::private_key_from_der(PRIVATE_KEY_2048).unwrap()).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn ring_key() -> (ring::rsa::KeyPair, ring::rand::SystemRandom) {
    (
        ring::rsa::KeyPair::from_der(PRIVATE_KEY_2048).unwrap(),
        ring::rand::SystemRandom::new(),
    )
}

#[cfg(not(target_arch = "xtensa"))]
fn aws_key() -> (aws_lc_rs::rsa::KeyPair, aws_lc_rs::rand::SystemRandom) {
    (
        aws_lc_rs::rsa::KeyPair::from_der(PRIVATE_KEY_2048).unwrap(),
        aws_lc_rs::rand::SystemRandom::new(),
    )
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_key() -> Dit<rind::rsa::KeyPair> {
    Dit::hold(rind::rsa::KeyPair::from_pkcs1(PRIVATE_KEY_2048).unwrap())
}

#[cfg(graviola)]
#[cfg(not(target_arch = "xtensa"))]
fn graviola_key() -> graviola::signing::rsa::SigningKey {
    graviola::signing::rsa::SigningKey::from_pkcs1_der(PRIVATE_KEY_2048).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
mod rsa2048_pkcs1_sha256_sign {
    use swole::bench;

    use super::*;

    #[bench(setup = ring_key)]
    fn ring((key, rng): &(ring::rsa::KeyPair, ring::rand::SystemRandom)) -> [u8; 256] {
        let mut signature = [0u8; 256];
        key.sign(
            &ring::signature::RSA_PKCS1_SHA256,
            rng,
            MESSAGE,
            &mut signature,
        )
        .unwrap();
        signature
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(
        (key, rng): &(aws_lc_rs::rsa::KeyPair, aws_lc_rs::rand::SystemRandom),
    ) -> [u8; 256] {
        let mut signature = [0u8; 256];
        key.sign(
            &aws_lc_rs::signature::RSA_PKCS1_SHA256,
            rng,
            MESSAGE,
            &mut signature,
        )
        .unwrap();
        signature
    }

    fn rustcrypto_key() -> rsa::pkcs1v15::SigningKey<sha2::Sha256> {
        use rsa::pkcs1::DecodeRsaPrivateKey;
        rsa::pkcs1v15::SigningKey::new(rsa::PrivateKey::from_pkcs1_der(PRIVATE_KEY_2048).unwrap())
    }

    #[bench(setup = rustcrypto_key)]
    fn rustcrypto(key: &rsa::pkcs1v15::SigningKey<sha2::Sha256>) {
        use rsa::signature::Signer;
        black_box(key.sign(MESSAGE));
    }

    #[bench(setup = rind_key)]
    fn rind(key: &Dit<rind::rsa::KeyPair>) {
        black_box(key.sign(&rind::rsa::sign::PKCS1_SHA256, MESSAGE).unwrap());
    }

    /// verified-garbage's key, after checking it signs as rind does.
    fn vg_input() -> verified_garbage::rsa::PrivateKey {
        use verified_garbage::hashes::sha256::Sha256;
        use verified_garbage::rsa::pkcs1_sig::Hash;
        let key = vg_key(PRIVATE_KEY_2048);
        let theirs = key
            .sign_pkcs1v15(&Sha256::digest(MESSAGE), Hash::Sha256)
            .unwrap();
        let ours = rind::rsa::KeyPair::from_pkcs1(PRIVATE_KEY_2048)
            .unwrap()
            .sign(&rind::rsa::sign::PKCS1_SHA256, MESSAGE)
            .unwrap();
        assert_eq!(theirs, ours.as_ref());
        key
    }

    // verified-garbage signs a digest, so its row hashes the message first,
    // as rind's sign does inside.
    #[bench(setup = vg_input)]
    fn verified_garbage(key: &verified_garbage::rsa::PrivateKey) {
        use verified_garbage::hashes::sha256::Sha256;
        use verified_garbage::rsa::pkcs1_sig::Hash;
        let digest = Sha256::digest(MESSAGE);
        black_box(key.sign_pkcs1v15(&digest, Hash::Sha256).unwrap());
    }

    #[cfg(graviola)]
    #[bench(setup = graviola_key)]
    fn graviola(key: &graviola::signing::rsa::SigningKey) -> [u8; 256] {
        let mut signature = [0u8; 256];
        key.sign_pkcs1_sha256(&mut signature, MESSAGE).unwrap();
        signature
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_key)]
    fn openssl(key: &openssl::pkey::PKey<openssl::pkey::Private>) {
        use openssl::hash::MessageDigest;
        use openssl::sign::Signer;
        let mut signer = Signer::new(MessageDigest::sha256(), key).unwrap();
        black_box(signer.sign_oneshot_to_vec(MESSAGE).unwrap());
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod rsa2048_pss_sha256_sign {
    use swole::bench;

    use super::*;

    #[bench(setup = ring_key)]
    fn ring((key, rng): &(ring::rsa::KeyPair, ring::rand::SystemRandom)) -> [u8; 256] {
        let mut signature = [0u8; 256];
        key.sign(
            &ring::signature::RSA_PSS_SHA256,
            rng,
            MESSAGE,
            &mut signature,
        )
        .unwrap();
        signature
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(
        (key, rng): &(aws_lc_rs::rsa::KeyPair, aws_lc_rs::rand::SystemRandom),
    ) -> [u8; 256] {
        let mut signature = [0u8; 256];
        key.sign(
            &aws_lc_rs::signature::RSA_PSS_SHA256,
            rng,
            MESSAGE,
            &mut signature,
        )
        .unwrap();
        signature
    }

    #[bench(setup = rind_key)]
    fn rind(key: &Dit<rind::rsa::KeyPair>) {
        black_box(key.sign(&rind::rsa::sign::PSS_SHA256, MESSAGE).unwrap());
    }

    fn vg_sign(key: &verified_garbage::rsa::PrivateKey) -> Vec<u8> {
        use verified_garbage::hashes::sha256::Sha256;
        use verified_garbage::rsa::pss::Hash;
        key.sign_pss(&Sha256::digest(MESSAGE), Hash::Sha256, Hash::Sha256, 32)
            .unwrap()
    }

    /// verified-garbage's key, after checking rind verifies what it signs.
    fn vg_input() -> verified_garbage::rsa::PrivateKey {
        let key = vg_key(PRIVATE_KEY_2048);
        rind::rsa::KeyPair::from_pkcs1(PRIVATE_KEY_2048)
            .unwrap()
            .public_key()
            .verify(&rind::rsa::verify::PSS_SHA256, MESSAGE, &vg_sign(&key))
            .unwrap();
        key
    }

    // Hashing the message first, as above.
    #[bench(setup = vg_input)]
    fn verified_garbage(key: &verified_garbage::rsa::PrivateKey) {
        black_box(vg_sign(key));
    }

    fn rustcrypto_key() -> rsa::pss::SigningKey<sha2::Sha256> {
        use rsa::pkcs1::DecodeRsaPrivateKey;
        rsa::pss::SigningKey::new(rsa::PrivateKey::from_pkcs1_der(PRIVATE_KEY_2048).unwrap())
    }

    #[bench(setup = rustcrypto_key)]
    fn rustcrypto(key: &rsa::pss::SigningKey<sha2::Sha256>) {
        use getrandom::{SysRng, rand_core::UnwrapErr};
        use rsa::signature::RandomizedSigner;
        black_box(key.sign_with_rng(&mut UnwrapErr(SysRng), MESSAGE));
    }

    #[cfg(graviola)]
    #[bench(setup = graviola_key)]
    fn graviola(key: &graviola::signing::rsa::SigningKey) -> [u8; 256] {
        let mut signature = [0u8; 256];
        key.sign_pss_sha256(&mut signature, MESSAGE).unwrap();
        signature
    }

    fn libcrux_input() -> libcrux_rsa::PrivateKey<256> {
        libcrux_key(PRIVATE_KEY_2048)
    }

    #[bench(setup = libcrux_input)]
    fn libcrux(key: &libcrux_rsa::PrivateKey<256>) -> [u8; 256] {
        let mut salt = [0u8; 32];
        getrandom::fill(&mut salt).unwrap();
        let mut signature = [0u8; 256];
        libcrux_rsa::sign_2048(
            libcrux_rsa::DigestAlgorithm::Sha2_256,
            key,
            MESSAGE,
            &salt,
            &mut signature,
        )
        .unwrap();
        signature
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench(setup = openssl_key)]
    fn openssl(key: &openssl::pkey::PKey<openssl::pkey::Private>) {
        use openssl::hash::MessageDigest;
        use openssl::rsa::Padding;
        use openssl::sign::{RsaPssSaltlen, Signer};
        let mut signer = Signer::new(MessageDigest::sha256(), key).unwrap();
        signer.set_rsa_padding(Padding::PKCS1_PSS).unwrap();
        signer
            .set_rsa_pss_saltlen(RsaPssSaltlen::DIGEST_LENGTH)
            .unwrap();
        black_box(signer.sign_oneshot_to_vec(MESSAGE).unwrap());
    }
}

/// Signing at the other sizes, whose primes take a different Montgomery
/// multiplication from RSA-2048's on some CPUs: 2056 bits for primes of an
/// odd number of words, and 2560 for a multiple of four but not eight.
macro_rules! sign_size {
    ($name:ident, $pkcs8:literal $(, $ring:ident)?) => {
        mod $name {
            use super::*;
            use swole::bench;

            const PRIVATE_KEY: &[u8] = include_bytes!($pkcs8);
            const MESSAGE: &[u8] = b"hello";

            $(
                fn ring_key() -> (ring::rsa::KeyPair, ring::rand::SystemRandom, Vec<u8>) {
                    let key = ring::rsa::KeyPair::from_pkcs8(PRIVATE_KEY).unwrap();
                    let signature = vec![0u8; key.public().modulus_len()];
                    (key, ring::rand::SystemRandom::new(), signature)
                }

                // ring signs only with primes of a multiple of 512 bits, and
                // moduli of at most 4096.
                #[bench(setup = ring_key)]
                fn $ring(
                    (key, rng, signature): &mut (
                        ring::rsa::KeyPair,
                        ring::rand::SystemRandom,
                        Vec<u8>,
                    ),
                ) {
                    key.sign(&ring::signature::RSA_PKCS1_SHA256, rng, MESSAGE, signature)
                        .unwrap()
                }
            )?

            fn aws_key() -> (aws_lc_rs::rsa::KeyPair, aws_lc_rs::rand::SystemRandom, Vec<u8>) {
                let key = aws_lc_rs::rsa::KeyPair::from_pkcs8(PRIVATE_KEY).unwrap();
                let signature = vec![0u8; key.public_modulus_len()];
                (key, aws_lc_rs::rand::SystemRandom::new(), signature)
            }

            #[bench(setup = aws_key)]
            fn aws_lc_rs(
                (key, rng, signature): &mut (
                    aws_lc_rs::rsa::KeyPair,
                    aws_lc_rs::rand::SystemRandom,
                    Vec<u8>,
                ),
            ) {
                key.sign(&aws_lc_rs::signature::RSA_PKCS1_SHA256, rng, MESSAGE, signature)
                    .unwrap()
            }

            fn rind_key() -> Dit<rind::rsa::KeyPair> {
                Dit::hold(rind::rsa::KeyPair::from_pkcs8(PRIVATE_KEY).unwrap())
            }

            #[bench(setup = rind_key)]
            fn rind(key: &Dit<rind::rsa::KeyPair>) {
                black_box(key.sign(&rind::rsa::sign::PKCS1_SHA256, MESSAGE).unwrap());
            }

            /// verified-garbage's key, after checking it signs as rind does.
            fn vg_input() -> verified_garbage::rsa::PrivateKey {
                use verified_garbage::hashes::sha256::Sha256;
                use verified_garbage::rsa::pkcs1_sig::Hash;
                let key = vg_key(PRIVATE_KEY);
                let ours = rind::rsa::KeyPair::from_pkcs8(PRIVATE_KEY)
                    .unwrap()
                    .sign(&rind::rsa::sign::PKCS1_SHA256, MESSAGE)
                    .unwrap();
                let theirs = key
                    .sign_pkcs1v15(&Sha256::digest(MESSAGE), Hash::Sha256)
                    .unwrap();
                assert_eq!(theirs, ours.as_ref());
                key
            }

            // Hashing the message first, as above.
            #[bench(setup = vg_input)]
            fn verified_garbage(key: &verified_garbage::rsa::PrivateKey) {
                use verified_garbage::hashes::sha256::Sha256;
                use verified_garbage::rsa::pkcs1_sig::Hash;
                let digest = Sha256::digest(MESSAGE);
                black_box(key.sign_pkcs1v15(&digest, Hash::Sha256).unwrap());
            }
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
sign_size!(
    rsa2056_pkcs1_sha256_sign,
    "../../rind/src/high/rsa/rsa2056.pkcs8.der"
);
#[cfg(not(target_arch = "xtensa"))]
sign_size!(
    rsa2560_pkcs1_sha256_sign,
    "../../rind/src/high/rsa/rsa2560.pkcs8.der"
);
#[cfg(not(target_arch = "xtensa"))]
sign_size!(
    rsa3072_pkcs1_sha256_sign,
    "../../rind/src/high/rsa/rsa3072.pkcs8.der",
    ring
);
#[cfg(not(target_arch = "xtensa"))]
sign_size!(
    rsa4096_pkcs1_sha256_sign,
    "../../rind/src/high/rsa/rsa4096.pkcs8.der",
    ring
);
#[cfg(not(target_arch = "xtensa"))]
sign_size!(
    rsa6144_pkcs1_sha256_sign,
    "../../rind/src/high/rsa/rsa6144.pkcs8.der"
);
#[cfg(not(target_arch = "xtensa"))]
sign_size!(
    rsa8192_pkcs1_sha256_sign,
    "../../rind/src/high/rsa/rsa8192.pkcs8.der"
);

#[cfg(not(target_arch = "xtensa"))]
mod rsa2048_oaep_sha256_decrypt {
    use rind::rsa::{DecryptingKey, OAEP_SHA256};
    use swole::bench;

    use super::*;

    const PLAINTEXT: [u8; 32] = [0; 32];

    fn private_key() -> DecryptingKey {
        DecryptingKey::from_pkcs1(&OAEP_SHA256, PRIVATE_KEY_2048).unwrap()
    }

    /// Encrypted here, since OAEP ciphertexts are randomized.
    fn ciphertext() -> Vec<u8> {
        private_key()
            .public_key()
            .encrypt(&PLAINTEXT, b"")
            .unwrap()
            .as_ref()
            .to_vec()
    }

    fn aws_key() -> (aws_lc_rs::rsa::OaepPrivateDecryptingKey, Vec<u8>) {
        use aws_lc_rs::rsa::{OaepPrivateDecryptingKey, PrivateDecryptingKey};
        let pkcs8 = private_key().to_pkcs8();
        let key = OaepPrivateDecryptingKey::new(
            PrivateDecryptingKey::from_pkcs8(pkcs8.as_ref()).unwrap(),
        )
        .unwrap();
        (key, ciphertext())
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(
        (key, ciphertext): &(aws_lc_rs::rsa::OaepPrivateDecryptingKey, Vec<u8>),
    ) -> [u8; 256] {
        let mut plaintext = [0u8; 256];
        key.decrypt(
            &aws_lc_rs::rsa::OAEP_SHA256_MGF1SHA256,
            ciphertext,
            &mut plaintext,
            None,
        )
        .unwrap();
        plaintext
    }

    fn rustcrypto_key() -> (rsa::PrivateKey, Vec<u8>) {
        use rsa::pkcs1::DecodeRsaPrivateKey;
        (
            rsa::PrivateKey::from_pkcs1_der(PRIVATE_KEY_2048).unwrap(),
            ciphertext(),
        )
    }

    #[bench(setup = rustcrypto_key)]
    fn rustcrypto((key, ciphertext): &(rsa::PrivateKey, Vec<u8>)) {
        black_box(
            key.decrypt(rsa::Oaep::<sha2::Sha256>::new(), ciphertext)
                .unwrap(),
        );
    }

    fn rind_key() -> Dit<(DecryptingKey, Vec<u8>)> {
        Dit::hold((private_key(), ciphertext()))
    }

    #[bench(setup = rind_key)]
    fn rind(input: &Dit<(DecryptingKey, Vec<u8>)>) {
        let (key, ciphertext) = &**input;
        black_box(key.decrypt(ciphertext, b"").unwrap());
    }

    fn vg_decrypt(key: &verified_garbage::rsa::PrivateKey, ciphertext: &[u8]) -> Vec<u8> {
        use verified_garbage::rsa::oaep::Hash;
        key.decrypt_oaep(ciphertext, Hash::Sha256, Hash::Sha256, b"")
            .unwrap()
    }

    /// verified-garbage's key, after checking it decrypts what rind
    /// encrypted.
    fn vg_input() -> (verified_garbage::rsa::PrivateKey, Vec<u8>) {
        let key = vg_key(PRIVATE_KEY_2048);
        let ciphertext = ciphertext();
        assert_eq!(vg_decrypt(&key, &ciphertext), PLAINTEXT);
        (key, ciphertext)
    }

    #[bench(setup = vg_input)]
    fn verified_garbage((key, ciphertext): &(verified_garbage::rsa::PrivateKey, Vec<u8>)) {
        black_box(vg_decrypt(key, ciphertext));
    }
}

/// Loading a key checks its components agree, which should stay small next
/// to a signature at every size.
macro_rules! load {
    ($name:ident, $der:literal) => {
        mod $name {
            use swole::bench;

            use super::*;

            const PRIVATE_KEY: &[u8] = include_bytes!($der);

            #[bench]
            fn aws_lc_rs() {
                black_box(
                    aws_lc_rs::rsa::KeyPair::from_der(std::hint::black_box(PRIVATE_KEY)).unwrap(),
                );
            }

            #[bench(setup = dit)]
            fn rind(_: &Dit<()>) {
                black_box(
                    rind::rsa::KeyPair::from_pkcs1(std::hint::black_box(PRIVATE_KEY)).unwrap(),
                );
            }

            /// The CRT components, parsed from the DER.
            fn components() -> [Vec<u8>; 8] {
                use rsa::pkcs1::DecodeRsaPrivateKey;
                use rsa::traits::{PrivateKeyParts, PublicKeyParts};
                let key = rsa::PrivateKey::from_pkcs1_der(PRIVATE_KEY).unwrap();
                [
                    key.n_bytes().to_vec(),
                    key.e_bytes().to_vec(),
                    key.d().to_be_bytes_trimmed_vartime().to_vec(),
                    key.primes()[0].to_be_bytes_trimmed_vartime().to_vec(),
                    key.primes()[1].to_be_bytes_trimmed_vartime().to_vec(),
                    key.dp().unwrap().to_be_bytes_trimmed_vartime().to_vec(),
                    key.dq().unwrap().to_be_bytes_trimmed_vartime().to_vec(),
                    key.crt_coefficient()
                        .unwrap()
                        .to_be_bytes_trimmed_vartime()
                        .to_vec(),
                ]
            }

            // verified-garbage loads the CRT components, parsed from the DER
            // here, and checks them as BoringSSL's `RSA_check_key` does.
            #[bench(setup = components)]
            fn verified_garbage(components: &[Vec<u8>; 8]) {
                use verified_garbage::rsa::{BigUint, PrivateKey};
                let [n, e, d, p, q, dp, dq, qinv] =
                    components.each_ref().map(|c| BigUint::from_be_bytes(c));
                black_box(PrivateKey::from_crt(n, e, d, p, q, dp, dq, qinv).unwrap());
            }

            fn rind_key() -> Dit<rind::rsa::KeyPair> {
                Dit::hold(rind::rsa::KeyPair::from_pkcs1(PRIVATE_KEY).unwrap())
            }

            #[bench(setup = rind_key)]
            fn rind_sign(key: &Dit<rind::rsa::KeyPair>) {
                black_box(key.sign(&rind::rsa::sign::PKCS1_SHA256, b"hello").unwrap());
            }
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
load!(rsa2048_load, "../../rind/src/high/rsa/rsa2048.der");
#[cfg(not(target_arch = "xtensa"))]
load!(rsa8192_load, "../../rind/src/high/rsa/rsa8192.der");

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
