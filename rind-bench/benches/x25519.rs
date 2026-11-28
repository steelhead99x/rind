#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, dit};

#[cfg(not(target_arch = "xtensa"))]
const PUBLIC_KEY: &[u8; 32] = b"\xe6\xdb\x68\x67\x58\x30\x30\xdb\x35\x94\xc1\xa4\x24\xb1\x5f\x7c\x72\x66\x24\xec\x26\xb3\x35\x3b\x10\xa9\x03\xa6\xd0\xab\x1c\x4c";

/// The scalar the stored-key rows load.
#[cfg(not(target_arch = "xtensa"))]
const SCALAR: [u8; 32] = [1; 32];

#[cfg(not(target_arch = "xtensa"))]
fn ring_rng() -> ring::rand::SystemRandom {
    ring::rand::SystemRandom::new()
}

#[cfg(not(target_arch = "xtensa"))]
fn aws_rng() -> aws_lc_rs::rand::SystemRandom {
    aws_lc_rs::rand::SystemRandom::new()
}

// Checks verified-garbage's public key and exchange against rind's, from a
// fixed scalar, before any of its rows times them.
#[cfg(not(target_arch = "xtensa"))]
fn vg_agrees_with_rind() {
    use verified_garbage::x25519::{PrivateKey, PublicKey};
    let key = PrivateKey::from_bytes(&SCALAR);
    let rind_key =
        rind::agreement::PrivateKey::from_scalar(&rind::agreement::X25519, &SCALAR).unwrap();
    assert_eq!(
        key.public_key().as_bytes()[..],
        *rind_key.public_key().as_ref()
    );
    assert_eq!(
        key.exchange(&PublicKey::from_bytes(PUBLIC_KEY)).unwrap()[..],
        *rind_key.agree(PUBLIC_KEY).unwrap().as_ref()
    );
}

/// Generates a key, encodes its public key, and agrees with a fixed peer.
#[cfg(not(target_arch = "xtensa"))]
fn rind_ecdh() {
    use rind::agreement::*;
    let our_private_key = PrivateKey::generate(&X25519).unwrap();
    black_box(our_private_key.public_key());
    black_box(our_private_key.agree(PUBLIC_KEY).unwrap());
}

#[cfg(not(target_arch = "xtensa"))]
mod x25519_ecdh {
    use swole::bench;

    use super::*;

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench]
    fn openssl() {
        use openssl::derive::Deriver;
        use openssl::pkey::{Id, PKey};

        let priv_key = PKey::generate_x25519().unwrap();
        black_box(priv_key.raw_public_key().unwrap());

        let peer = PKey::public_key_from_raw_bytes(PUBLIC_KEY, Id::X25519).unwrap();
        let mut deriver = Deriver::new(&priv_key).unwrap();
        deriver.set_peer(&peer).unwrap();
        let mut secret = [0u8; 32];
        deriver.derive(&mut secret).unwrap();
        black_box(secret);
    }

    #[bench(setup = ring_rng)]
    fn ring(rng: &ring::rand::SystemRandom) {
        use ring::agreement;
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::X25519, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());

        let peer_public_key = agreement::UnparsedPublicKey::new(&agreement::X25519, PUBLIC_KEY);

        agreement::agree_ephemeral(our_private_key, &peer_public_key, |key_material| {
            black_box(key_material);
        })
        .unwrap();
    }

    #[bench(setup = aws_rng)]
    fn aws_lc_rs(rng: &aws_lc_rs::rand::SystemRandom) {
        use aws_lc_rs::{agreement, error};
        let our_private_key =
            agreement::EphemeralPrivateKey::generate(&agreement::X25519, rng).unwrap();
        black_box(our_private_key.compute_public_key().unwrap());

        let peer_public_key = agreement::UnparsedPublicKey::new(&agreement::X25519, PUBLIC_KEY);

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
    fn dalek() {
        let our_priv = x25519_dalek::EphemeralSecret::random();
        let our_pub: x25519_dalek::PublicKey = (&our_priv).into();
        black_box(our_pub);

        let their_pub = x25519_dalek::PublicKey::from(*PUBLIC_KEY);

        let shared_secret = our_priv.diffie_hellman(&their_pub);
        black_box(shared_secret.as_bytes());
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        rind_ecdh()
    }

    fn vg_checked() {
        vg_agrees_with_rind();
    }

    #[bench(setup = vg_checked)]
    fn verified_garbage(_: &()) {
        use verified_garbage::x25519::{PrivateKey, PublicKey};
        let our_private_key = PrivateKey::generate().unwrap();
        black_box(our_private_key.public_key());

        let peer = PublicKey::from_bytes(PUBLIC_KEY);
        black_box(our_private_key.exchange(&peer).unwrap());
    }

    #[cfg(graviola)]
    #[bench]
    fn graviola() {
        use graviola::key_agreement::x25519::{PrivateKey, PublicKey};
        let our_private_key = PrivateKey::new_random().unwrap();
        black_box(our_private_key.public_key());

        let peer = PublicKey::from_array(PUBLIC_KEY);
        black_box(our_private_key.diffie_hellman(&peer).unwrap());
    }

    #[bench]
    fn libcrux() {
        use libcrux_ecdh::{X25519PublicKey, x25519_derive, x25519_key_gen};
        let (our_private_key, our_public_key) = x25519_key_gen(&mut getrandom::SysRng).unwrap();
        black_box(our_public_key);

        let peer = X25519PublicKey(*PUBLIC_KEY);
        black_box(x25519_derive(&peer, &our_private_key).unwrap());
    }
}

#[cfg(target_arch = "aarch64")]
#[cfg(not(target_arch = "xtensa"))]
mod dit_per_call {
    mod x25519_ecdh {
        use swole::bench;

        use super::super::*;

        #[bench]
        fn rind() {
            rind_ecdh()
        }
    }
}

// Generate a key and its public key: the fixed-base multiplication alone,
// where `x25519-ecdh` adds the variable-base one.
#[cfg(not(target_arch = "xtensa"))]
mod x25519_keygen {
    use swole::bench;

    use super::*;

    #[bench(setup = ring_rng)]
    fn ring(rng: &ring::rand::SystemRandom) {
        use ring::agreement;
        let key = agreement::EphemeralPrivateKey::generate(&agreement::X25519, rng).unwrap();
        black_box(key.compute_public_key().unwrap());
    }

    #[bench(setup = aws_rng)]
    fn aws_lc_rs(rng: &aws_lc_rs::rand::SystemRandom) {
        use aws_lc_rs::agreement;
        let key = agreement::EphemeralPrivateKey::generate(&agreement::X25519, rng).unwrap();
        black_box(key.compute_public_key().unwrap());
    }

    #[bench]
    fn dalek() {
        let key = x25519_dalek::EphemeralSecret::random();
        black_box(x25519_dalek::PublicKey::from(&key));
    }

    #[bench(setup = dit)]
    fn rind(_dit: &Dit<()>) {
        use rind::agreement::*;
        let key = PrivateKey::generate(&X25519).unwrap();
        black_box(key.public_key());
    }

    #[cfg(graviola)]
    #[bench]
    fn graviola() {
        let key = graviola::key_agreement::x25519::PrivateKey::new_random().unwrap();
        black_box(key.public_key());
    }

    #[bench]
    fn libcrux() {
        black_box(libcrux_ecdh::x25519_key_gen(&mut getrandom::SysRng).unwrap());
    }

    fn vg_checked() {
        vg_agrees_with_rind();
    }

    #[bench(setup = vg_checked)]
    fn verified_garbage(_: &()) {
        let key = verified_garbage::x25519::PrivateKey::generate().unwrap();
        black_box(key.public_key());
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    #[bench]
    fn openssl() {
        let key = openssl::pkey::PKey::generate_x25519().unwrap();
        black_box(key.raw_public_key().unwrap());
    }
}

// Agree with a stored key, loaded once, as WebCrypto's `deriveBits` and
// node's `ECDH` do: the variable-base multiplication alone.
#[cfg(not(target_arch = "xtensa"))]
mod x25519_ecdh_stored {
    use swole::bench;

    use super::*;

    fn aws_key() -> aws_lc_rs::agreement::PrivateKey {
        use aws_lc_rs::agreement;
        agreement::PrivateKey::from_private_key(&agreement::X25519, &SCALAR).unwrap()
    }

    #[bench(setup = aws_key)]
    fn aws_lc_rs(key: &aws_lc_rs::agreement::PrivateKey) {
        use aws_lc_rs::{agreement, error};
        let public_key: &[u8] = PUBLIC_KEY;
        let peer = agreement::UnparsedPublicKey::new(&agreement::X25519, public_key);
        agreement::agree(key, peer, error::Unspecified, |key_material| {
            black_box(key_material);
            Ok(())
        })
        .unwrap();
    }

    fn rind_key() -> Dit<rind::agreement::PrivateKey> {
        use rind::agreement::*;
        Dit::hold(PrivateKey::from_scalar(&X25519, &SCALAR).unwrap())
    }

    #[bench(setup = rind_key)]
    fn rind(key: &Dit<rind::agreement::PrivateKey>) {
        let public_key: &[u8] = PUBLIC_KEY;
        black_box(key.agree(public_key).unwrap());
    }

    fn vg_key() -> verified_garbage::x25519::PrivateKey {
        vg_agrees_with_rind();
        verified_garbage::x25519::PrivateKey::from_bytes(&SCALAR)
    }

    #[bench(setup = vg_key)]
    fn verified_garbage(key: &verified_garbage::x25519::PrivateKey) {
        let peer = verified_garbage::x25519::PublicKey::from_bytes(PUBLIC_KEY);
        black_box(key.exchange(&peer).unwrap());
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
