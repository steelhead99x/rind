// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Each public call that handles a secret runs under DIT, and costs the
//! number of DIT toggles listed for it.
//!
//! The toggle counts come from [`super::model`], which counts on every
//! backend, so they are checked on x86_64 too. On an aarch64 OS
//! (`rind_dit`) a debug build also reads PSTATE.DIT at each secret `Entry` and each primitive's
//! [`super::Entry::assert_held`], and these tests require those reads to
//! have run and passed, and DIT to be clear again after each call.

use std::panic;

use super::model;
use crate::cpu::Dit;
use crate::{
    aead, agreement, cipher, constant_time, digest, ecdsa, ed25519, hkdf, hmac, hpke, kem, ml_dsa,
    oprf, pbkdf2, spake2plus, vrf,
};

/// Marks for `admin/dit-qemu-plugin.c`, no-ops anywhere else: `hint #84`
/// opens a window around one call, `hint #85` closes it, and `hint #86` to
/// `hint #87` leaves the call's setup out of it.
macro_rules! dit_qemu_mark {
    ($hint:literal) => {
        // SAFETY: an unallocated hint, which executes as a no-op.
        #[cfg(target_arch = "aarch64")]
        unsafe {
            core::arch::asm!($hint, options(nostack, preserves_flags))
        };
    };
}

/// Whether DIT stays on after a call that set it: always under
/// `--cfg rind_dit_sticky`, and for a batch under `--cfg rind_dit_autohold`.
#[cfg(all(debug_assertions, rind_dit))]
const LINGERS: bool = cfg!(any(rind_dit_sticky, rind_dit_autohold));

/// A public call, and the DIT toggles it costs alone.
struct Call {
    name: &'static str,
    toggles: u64,
    run: fn(),
}

fn quic_key(algorithm: &'static aead::quic::Algorithm) -> aead::quic::HeaderProtectionKey {
    aead::quic::HeaderProtectionKey::new(algorithm, &[7; 32][..algorithm.key_len()]).unwrap()
}

fn hmac_key() -> hmac::Key {
    hmac::Key::new(&hmac::HMAC_SHA256, &[1; 32])
}

fn aead_key(algorithm: &'static aead::Algorithm) -> aead::Key {
    aead::Key::new(algorithm, &[2; 32][..algorithm.key_len()]).unwrap()
}

fn nonce() -> aead::Nonce {
    aead::Nonce::assume_unique_for_key([3; 12])
}

fn sealed(algorithm: &'static aead::Algorithm) -> (aead::Key, [u8; 1350], aead::Tag) {
    let key = aead_key(algorithm);
    let mut packet = [4; 1350];
    let tag = key
        .seal_in_place_separate_tag(nonce(), b"header", &mut packet)
        .unwrap();
    (key, packet, tag)
}

/// Each call runs its operation on values made before it is timed, so its
/// count is the operation's alone. Setup that makes those values runs
/// outside the count, in `setup`.
macro_rules! call {
    ($name:literal, $toggles:literal, || $body:expr) => {
        Call {
            name: $name,
            toggles: $toggles,
            run: || {
                let _value = $body;
            },
        }
    };
}

/// Runs `body` and returns the toggles it made.
fn toggles(body: impl FnOnce()) -> u64 {
    let before = model::toggles();
    body();
    model::toggles() - before
}

fn calls() -> Vec<Call> {
    std::vec![
        call!("digest::digest", 1, || digest::digest(
            &digest::SHA256,
            &[5; 1350]
        )),
        call!("digest::Context::update", 1, || {
            digest::Context::new(&digest::SHA256).update(&[5; 1350])
        }),
        call!("digest::Context::finish", 1, || {
            digest::Context::new(&digest::SHA256).finish()
        }),
        call!("hmac::Key::new", 1, || hmac_key()),
        call!("hmac::sign", 1, || hmac::sign(
            &hmac_key_untimed(),
            &[5; 1350]
        )),
        call!("hmac::verify", 1, || {
            let key = hmac_key_untimed();
            hmac::verify(&key, b"m", &[0; 32]).unwrap_err();
        }),
        call!("hkdf::Salt::new", 1, || hkdf::Salt::new(
            &hkdf::HKDF_SHA256,
            b"salt"
        )),
        call!("hkdf::Salt::extract", 1, || salt_untimed()
            .extract(&[6; 32])
            .unwrap()),
        call!("hkdf::Prk::new", 1, || prk()),
        call!("hkdf::Prk::fill", 1, || {
            prk_untimed().fill(&[b"info"], &mut [0; 32]).unwrap()
        }),
        // Each conversion expands, then keys what it expanded, under one
        // entry.
        call!("hkdf Okm into aead::Key", 1, || {
            aead::Key::from(
                prk_untimed()
                    .expand(&[b"quic key"], &aead::AES_128_GCM)
                    .unwrap(),
            )
        }),
        call!("hkdf Okm into quic::HeaderProtectionKey", 1, || {
            aead::quic::HeaderProtectionKey::from(
                prk_untimed()
                    .expand(&[b"quic hp"], &aead::quic::AES_128)
                    .unwrap(),
            )
        }),
        call!("hkdf Okm into hmac::Key", 1, || {
            hmac::Key::from(
                prk_untimed()
                    .expand(&[b"finished"], &hmac::HMAC_SHA256)
                    .unwrap(),
            )
        }),
        call!("hkdf Okm into Prk", 1, || {
            hkdf::Prk::from(
                prk_untimed()
                    .expand(&[b"derived"], &hkdf::HKDF_SHA256)
                    .unwrap(),
            )
        }),
        call!("aead::Key::new AES-128-GCM", 1, || aead_key(
            &aead::AES_128_GCM
        )),
        call!("aead::Key::seal AES-128-GCM", 1, || {
            aead_key_untimed(&aead::AES_128_GCM)
                .seal_in_place_separate_tag(nonce(), b"header", &mut [4; 1350])
                .unwrap()
        }),
        call!("aead::Key::open AES-128-GCM", 1, || open_untimed(
            &aead::AES_128_GCM
        )),
        call!("aead::Key::seal ChaCha20-Poly1305", 1, || {
            aead_key_untimed(&aead::CHACHA20_POLY1305)
                .seal_in_place_separate_tag(nonce(), b"header", &mut [4; 1350])
                .unwrap()
        }),
        call!("aead::Key::open ChaCha20-Poly1305", 1, || open_untimed(
            &aead::CHACHA20_POLY1305
        )),
        call!("quic::HeaderProtectionKey::mask AES-128", 1, || {
            quic_key_untimed(&aead::quic::AES_128).mask(&[8; 16])
        }),
        call!("quic::HeaderProtectionKey::mask ChaCha20", 1, || {
            quic_key_untimed(&aead::quic::CHACHA20).mask(&[8; 16])
        }),
        call!("constant_time::verify", 1, || {
            constant_time::verify(&[9; 32], &[9; 32]).unwrap();
        }),
        call!("agreement X25519 agree", 1, || {
            x25519_untimed().agree(&X25519_PEER).unwrap()
        }),
        call!("ed25519 sign", 1, || ed25519_untimed().sign(b"message")),
        // One-shot digests and tiny inputs: each hashes, pads, and finishes
        // under one entry.
        call!("digest::digest SHA-256 16 B", 1, || digest::digest(
            &digest::SHA256,
            &[5; 16]
        )),
        call!("digest::digest SHA-1", 1, || digest::digest(
            &digest::legacy::SHA1,
            &[5; 1350]
        )),
        call!("digest::digest SHA-384", 1, || digest::digest(
            &digest::SHA384,
            &[5; 1350]
        )),
        call!("digest::digest SHA-512", 1, || digest::digest(
            &digest::SHA512,
            &[5; 1350]
        )),
        call!("digest::digest SHA3-256", 1, || digest::digest(
            &digest::SHA3_256,
            &[5; 1350]
        )),
        call!("digest::digest MD5", 1, || digest::digest(
            &digest::legacy::MD5,
            &[5; 1350]
        )),
        call!("hmac::sign HMAC-SHA1", 1, || hmac::sign(
            &untimed(|| hmac::Key::new(&hmac::legacy::HMAC_SHA1, &[1; 20])),
            &[5; 1350]
        )),
        call!("hmac::Context::update", 1, || {
            let key = hmac_key_untimed();
            let mut ctx = hmac::Context::with_key(&key);
            ctx.update(&[5; 1350]);
        }),
        call!("hmac::Context::sign", 1, || {
            let key = hmac_key_untimed();
            hmac::Context::with_key(&key).sign()
        }),
        call!("hkdf Okm into aead::Key AES-256-GCM", 1, || {
            aead::Key::from(prk_untimed().expand(&[b"key"], &aead::AES_256_GCM).unwrap())
        }),
        call!(
            "hkdf Okm into quic::HeaderProtectionKey ChaCha20",
            1,
            || {
                aead::quic::HeaderProtectionKey::from(
                    prk_untimed()
                        .expand(&[b"quic hp"], &aead::quic::CHACHA20)
                        .unwrap(),
                )
            }
        ),
        call!("pbkdf2::Secret::new", 1, || pbkdf2::Secret::new(
            &pbkdf2::PBKDF2_HMAC_SHA256,
            b"password"
        )),
        call!("pbkdf2::Secret::derive", 1, || {
            pbkdf2_untimed().derive(TWO, b"salt", &mut [0; 32]).unwrap()
        }),
        call!("pbkdf2::Secret::verify", 1, || {
            pbkdf2_untimed().verify(TWO, b"salt", &[0; 32]).unwrap_err()
        }),
        call!("aead::Key::seal AES-128-GCM 0 B", 1, || {
            aead_key_untimed(&aead::AES_128_GCM)
                .seal_in_place_separate_tag(nonce(), b"", &mut [])
                .unwrap()
        }),
        call!("aead::Key::seal AES-128-GCM 16 B", 1, || {
            aead_key_untimed(&aead::AES_128_GCM)
                .seal_in_place_separate_tag(nonce(), b"header", &mut [4; 16])
                .unwrap()
        }),
        call!("aead::Key::seal AES-256-GCM 16 B", 1, || {
            aead_key_untimed(&aead::AES_256_GCM)
                .seal_in_place_separate_tag(nonce(), b"header", &mut [4; 16])
                .unwrap()
        }),
        call!("aead::Key::open AES-256-GCM", 1, || open_untimed(
            &aead::AES_256_GCM
        )),
        call!("aead::Key::open AES-128-GCM wrong tag", 1, || {
            let (key, mut packet, _) = untimed(|| sealed(&aead::AES_128_GCM));
            let tag = aead::Tag::try_from(&[0u8; 16][..]).unwrap();
            key.open_in_place_separate_tag(nonce(), b"header", tag, &mut packet)
                .unwrap_err()
        }),
        call!("aead::Key::seal ChaCha20-Poly1305 16 B", 1, || {
            aead_key_untimed(&aead::CHACHA20_POLY1305)
                .seal_in_place_separate_tag(nonce(), b"header", &mut [4; 16])
                .unwrap()
        }),
        call!(
            "aead::RandomizedNonceKey seal (XChaCha20-Poly1305)",
            1,
            || {
                let mut packet = std::vec![4; 1350];
                untimed(|| aead::RandomizedNonceKey::new(&[2; 32]))
                    .seal_in_place_append_tag(b"header", &mut packet)
                    .unwrap()
            }
        ),
        call!(
            "aead::RandomizedNonceKey open (XChaCha20-Poly1305)",
            1,
            || {
                let (key, nonce, mut packet) = untimed(|| {
                    let key = aead::RandomizedNonceKey::new(&[2; 32]);
                    let mut packet = std::vec![4; 1350];
                    let nonce = key
                        .seal_in_place_append_tag(b"header", &mut packet)
                        .unwrap();
                    (key, nonce, packet)
                });
                key.open_in_place(nonce, b"header", &mut packet)
                    .unwrap()
                    .len()
            }
        ),
        call!("aead::gcm::Key::new", 1, || aead::gcm::Key::new(
            &cipher::AES_128,
            &[2; 16],
            aead::gcm::TagLength::Full
        )
        .unwrap()),
        call!("cipher::ChaCha20::apply_keystream", 1, || {
            cipher::ChaCha20::new(&[2; 32])
                .apply_keystream(&[3; 12], 0, &mut [4; 1350])
                .unwrap()
        }),
        call!("cipher::Aes::encrypt_block", 1, || {
            untimed(|| cipher::Aes::new(&cipher::AES_128, &[2; 16]).unwrap())
                .encrypt_block(&mut [4; 16])
        }),
        call!("cipher::AesCtr::apply_keystream", 1, || {
            untimed(|| cipher::AesCtr::new(&cipher::AES_128, &[2; 16], 32).unwrap())
                .apply_keystream(&[3; 16], &mut [4; 1350])
                .unwrap()
        }),
        call!("cipher::AesCbcEncryptingKey::encrypt_blocks", 1, || {
            untimed(|| cipher::AesCbcEncryptingKey::new(&cipher::AES_128, &[2; 16]).unwrap())
                .encrypt_blocks(cipher::CbcIv::assume_unpredictable([3; 16]), &mut [4; 64])
                .unwrap()
        }),
        call!("spake2plus prover start", 1, || {
            untimed(spake_prover)
                .start(&spake2plus::RFC9383, &SPAKE_SESSION)
                .unwrap()
        }),
        call!("spake2plus verifier start", 1, || {
            let (share_p, verifier) = untimed(|| {
                let (share_p, _) = spake_prover()
                    .start(&spake2plus::RFC9383, &SPAKE_SESSION)
                    .unwrap();
                (share_p, spake_verifier())
            });
            verifier
                .start(&spake2plus::RFC9383, &SPAKE_SESSION, &share_p)
                .unwrap()
        }),
        // SPAKE2+: each side's finish, key schedule and confirmation, under
        // one entry.
        call!("spake2plus prover finish", 1, || {
            let (prover, share_v, confirm_v, _, _) = untimed(spake_started);
            prover.finish(&share_v, &confirm_v).unwrap()
        }),
        call!("spake2plus verifier finish", 1, || {
            let (prover, share_v, confirm_v, verifier) = untimed(|| {
                let (prover, share_v, confirm_v, verifier, _) = spake_started();
                (prover, share_v, confirm_v, verifier)
            });
            let confirm_p = untimed(|| prover.finish(&share_v, &confirm_v).unwrap().0);
            verifier.finish(&confirm_p).unwrap()
        }),
        // Making a private key and encoding its public key share one entry.
        call!("agreement::PrivateKey::generate X25519", 1, || {
            agreement::PrivateKey::generate(&agreement::X25519).unwrap()
        }),
        call!("agreement::PrivateKey::generate P-256", 1, || {
            agreement::PrivateKey::generate(&agreement::ECDH_P256).unwrap()
        }),
        call!("agreement::PrivateKey::from_scalar X25519", 1, || {
            agreement::PrivateKey::from_scalar(&agreement::X25519, &[10; 32]).unwrap()
        }),
        call!("agreement::PrivateKey::from_pkcs8 P-256", 1, || {
            let der = untimed(|| {
                agreement::PrivateKey::from_scalar(&agreement::ECDH_P256, &[10; 32])
                    .unwrap()
                    .to_pkcs8()
            });
            agreement::PrivateKey::from_pkcs8(&agreement::ECDH_P256, der.as_ref()).unwrap()
        }),
        call!("hpke::PrivateKey::generate X25519", 1, || {
            hpke::PrivateKey::generate(&hpke::DHKEM_X25519_HKDF_SHA256).unwrap()
        }),
        // Key exports, which copy out a private scalar or seed, and the
        // post-quantum and signing calls.
        call!("agreement::PrivateKey::to_scalar X25519", 1, || {
            x25519_untimed().to_scalar()
        }),
        call!("agreement::PrivateKey::to_scalar P-256", 1, || {
            untimed(|| agreement::PrivateKey::generate(&agreement::ECDH_P256).unwrap()).to_scalar()
        }),
        call!("agreement P-384 agree", 1, || {
            let (key, peer) = untimed(|| {
                let peer = agreement::PrivateKey::generate(&agreement::ECDH_P384).unwrap();
                let key = agreement::PrivateKey::generate(&agreement::ECDH_P384).unwrap();
                (key, peer.public_key().as_ref().to_vec())
            });
            key.agree(&peer).unwrap()
        }),
        call!("ecdsa::KeyPair::sign P-256", 1, || {
            untimed(|| ecdsa::KeyPair::generate(&ecdsa::sign::P256_SHA256_FIXED).unwrap())
                .sign(b"message")
                .unwrap()
        }),
        call!("ecdsa::KeyPair::to_scalar P-256", 1, || {
            untimed(|| ecdsa::KeyPair::generate(&ecdsa::sign::P256_SHA256_FIXED).unwrap())
                .to_scalar()
        }),
        call!("vrf::KeyPair::to_seed P-256", 1, || {
            untimed(|| vrf::KeyPair::generate(&vrf::ECVRF_P256_SHA256_TAI).unwrap()).to_seed()
        }),
        call!("vrf::KeyPair::prove P-256", 1, || {
            untimed(|| vrf::KeyPair::generate(&vrf::ECVRF_P256_SHA256_TAI).unwrap())
                .prove(b"alpha")
                .unwrap()
        }),
        call!("oprf::ServerKey::to_scalar P-256", 1, || {
            untimed(|| oprf::ServerKey::generate(&oprf::P256_SHA256).unwrap()).to_scalar()
        }),
        call!("kem::DecapsulationKey::generate ML-KEM-768", 1, || {
            kem::DecapsulationKey::<kem::MlKem768>::generate().unwrap()
        }),
        call!("kem::EncapsulationKey::encapsulate ML-KEM-768", 1, || {
            untimed(|| {
                kem::DecapsulationKey::<kem::MlKem768>::generate()
                    .unwrap()
                    .public_key()
                    .clone()
            })
            .encapsulate()
            .unwrap()
        }),
        call!("kem::DecapsulationKey::decapsulate ML-KEM-768", 1, || {
            let (key, ciphertext) = untimed(|| {
                let key = kem::DecapsulationKey::<kem::MlKem768>::generate().unwrap();
                let (ciphertext, _) = key.public_key().encapsulate().unwrap();
                (key, ciphertext)
            });
            key.decapsulate(&ciphertext)
        }),
        call!("ml_dsa::KeyPair::from_seed ML-DSA-44", 1, || {
            ml_dsa::KeyPair::<ml_dsa::MlDsa44>::from_seed(&[12; 32]).unwrap()
        }),
        call!("ml_dsa::KeyPair::sign ML-DSA-44", 1, || {
            untimed(|| ml_dsa::KeyPair::<ml_dsa::MlDsa44>::from_seed(&[12; 32]).unwrap())
                .sign(b"message")
                .unwrap()
        }),
        call!("ecdsa::KeyPair::generate P-256", 1, || {
            ecdsa::KeyPair::generate(&ecdsa::sign::P256_SHA256_FIXED).unwrap()
        }),
        call!("ecdsa::KeyPair::from_pkcs8 P-256", 1, || {
            let der = untimed(|| {
                ecdsa::KeyPair::generate(&ecdsa::sign::P256_SHA256_FIXED)
                    .unwrap()
                    .to_pkcs8()
            });
            ecdsa::KeyPair::from_pkcs8(&ecdsa::sign::P256_SHA256_FIXED, der.as_ref()).unwrap()
        }),
    ]
}

const TWO: core::num::NonZeroU32 = core::num::NonZeroU32::new(2).unwrap();

const SPAKE_SESSION: spake2plus::Session<'static> = spake2plus::Session {
    context: b"app",
    id_prover: b"client",
    id_verifier: b"server",
};

fn spake_prover() -> spake2plus::ProverSecrets {
    spake2plus::ProverSecrets::new(&[0x11; 40], &[0x22; 40]).unwrap()
}

fn spake_verifier() -> spake2plus::VerifierRecord {
    spake2plus::VerifierRecord::from_w1(&[0x11; 40], &[0x22; 40]).unwrap()
}

type SpakeStarted = (
    spake2plus::ProverAwaiting<spake2plus::Rfc9383>,
    spake2plus::Share<spake2plus::Rfc9383>,
    spake2plus::Confirm<spake2plus::Rfc9383>,
    spake2plus::VerifierAwaiting<spake2plus::Rfc9383>,
    spake2plus::Share<spake2plus::Rfc9383>,
);

/// Both sides of a SPAKE2+ exchange, started: the prover awaiting the
/// verifier's share and confirmation, and the verifier awaiting the
/// prover's.
fn spake_started() -> SpakeStarted {
    let (share_p, prover) = spake_prover()
        .start(&spake2plus::RFC9383, &SPAKE_SESSION)
        .unwrap();
    let (share_v, confirm_v, verifier) = spake_verifier()
        .start(&spake2plus::RFC9383, &SPAKE_SESSION, &share_p)
        .unwrap();
    (prover, share_v, confirm_v, verifier, share_p)
}

fn pbkdf2_untimed() -> pbkdf2::Secret {
    untimed(|| pbkdf2::Secret::new(&pbkdf2::PBKDF2_HMAC_SHA256, b"password"))
}

// The values a timed call works on, made by the `untimed` helpers, whose
// toggles `run_counted` leaves out of the call's count.

const X25519_PEER: [u8; 32] = [9; 32];

/// Runs `make` as setup, outside the toggle count of the call it serves:
/// its toggles are subtracted by [`run_counted`].
fn untimed<T>(make: impl FnOnce() -> T) -> T {
    let before = model::toggles();
    dit_qemu_mark!("hint #86");
    let value = make();
    dit_qemu_mark!("hint #87");
    UNTIMED.set(UNTIMED.get() + (model::toggles() - before));
    value
}

thread_local! {
    static UNTIMED: core::cell::Cell<u64> = const { core::cell::Cell::new(0) };
}

fn prk() -> hkdf::Prk {
    hkdf::Prk::new(&hkdf::HKDF_SHA256, &[6; 32])
}

fn prk_untimed() -> hkdf::Prk {
    untimed(prk)
}

fn salt_untimed() -> hkdf::Salt {
    untimed(|| hkdf::Salt::new(&hkdf::HKDF_SHA256, b"salt"))
}

fn hmac_key_untimed() -> hmac::Key {
    untimed(hmac_key)
}

fn aead_key_untimed(algorithm: &'static aead::Algorithm) -> aead::Key {
    untimed(|| aead_key(algorithm))
}

fn quic_key_untimed(algorithm: &'static aead::quic::Algorithm) -> aead::quic::HeaderProtectionKey {
    untimed(|| quic_key(algorithm))
}

fn x25519_untimed() -> agreement::PrivateKey {
    untimed(|| agreement::PrivateKey::from_scalar(&agreement::X25519, &[10; 32]).unwrap())
}

fn ed25519_untimed() -> ed25519::KeyPair {
    untimed(|| ed25519::KeyPair::from_seed(&[11; 32]).unwrap())
}

fn open_untimed(algorithm: &'static aead::Algorithm) {
    let (key, mut packet, tag) = untimed(|| sealed(algorithm));
    key.open_in_place_separate_tag(nonce(), b"header", tag, &mut packet)
        .unwrap();
}

/// The toggles `call` made, less those its setup made.
fn run_counted(call: &Call) -> u64 {
    UNTIMED.set(0);
    let made = toggles(call.run);
    made - UNTIMED.get()
}

#[cfg(all(debug_assertions, rind_dit))]
fn dit_on() -> Option<bool> {
    crate::low::dit_on()
}

/// Every call costs the toggles listed, so a change that splits one
/// operation into more DIT toggles, or merges them, shows here first.
#[test]
fn each_call_costs_its_toggles() {
    let mut wrong = Vec::new();
    for call in calls() {
        assert!(!model::live(), "{} began inside a guard", call.name);
        let made = run_counted(&call);
        if made != call.toggles {
            wrong.push(std::format!(
                "{}: {made} toggles, listed {}",
                call.name,
                call.toggles
            ));
        }
        assert!(!model::live(), "{} left a guard live", call.name);
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// Under a held guard no call toggles again.
#[test]
fn a_held_guard_absorbs_every_toggle() {
    let dit = Dit::hold();
    for call in calls() {
        assert_eq!(toggles(call.run), 0, "{} toggled under a guard", call.name);
    }
    drop(dit);
}

/// A QUIC sender's per-packet work, header protection and a seal, under
/// one guard: one toggle for the whole batch.
#[test]
fn quic_packets_under_one_guard_toggle_once() {
    let header = quic_key(&aead::quic::AES_128);
    let packet_key = aead_key(&aead::AES_128_GCM);
    let made = toggles(|| {
        let _dit = Dit::hold();
        for number in 0..16u64 {
            let mut packet = [0u8; 1350];
            let nonce = aead::Nonce::from_sequence(&[3; 12], number);
            let tag = packet_key
                .seal_in_place_separate_tag(nonce, b"header", &mut packet[20..])
                .unwrap();
            let sample: &[u8; 16] = tag.as_ref().try_into().unwrap();
            let _mask = header.mask(sample);
        }
    });
    assert_eq!(made, 1);
}

/// Where rind sets DIT and the CPU has it, each call ran PSTATE.DIT checks
/// that passed, and left DIT clear. `RIND_TEST_DIT=1` fails the run if the
/// CPU lacks DIT, so a qemu or Apple run cannot pass by checking nothing.
#[cfg(all(debug_assertions, rind_dit))]
#[test]
fn every_secret_call_runs_with_dit() {
    if std::env::var_os("RIND_TEST_DIT").is_some_and(|v| v == "1") {
        assert!(
            dit_on().is_some(),
            "RIND_TEST_DIT=1 but rind sets no DIT here"
        );
    }
    if dit_on().is_none() {
        return;
    }
    for call in calls() {
        if LINGERS {
            // The last call left DIT on.
            crate::low::leave_cpu_state(1);
        }
        assert_eq!(dit_on(), Some(false), "{} began with DIT set", call.name);
        let before = super::dit_checks();
        (call.run)();
        let checks = super::dit_checks() - before;
        assert!(checks > 0, "{} ran no PSTATE.DIT check", call.name);
        // Under autohold, a call that ends with a public step (parsing a
        // public value) ends its own batch, so either is right there.
        if !cfg!(rind_dit_autohold) {
            assert_eq!(dit_on(), Some(LINGERS), "{}: DIT after the call", call.name);
        }
    }
}

/// The check fires: a primitive under a secret `Entry` whose DIT something
/// cleared panics.
#[cfg(all(debug_assertions, rind_dit))]
#[test]
fn a_cleared_dit_under_an_entry_panics() {
    if dit_on().is_none() {
        return;
    }
    let entry = super::Entry::new_secret();
    // Clears DIT under the live `Entry`, as a bug that left it would.
    crate::low::leave_cpu_state(1);
    let caught = panic::catch_unwind(|| super::Entry::assert_held());
    // Sets it again, so the `Entry` drops cleanly and clears it.
    let _ = crate::low::enter_cpu_state();
    drop(entry);
    assert_eq!(dit_on(), Some(LINGERS));
    let message = caught.expect_err("a cleared DIT passed the check");
    let message = message
        .downcast_ref::<&str>()
        .copied()
        .or_else(|| message.downcast_ref::<String>().map(|s| s.as_str()))
        .unwrap_or_default();
    assert!(message.contains("PSTATE.DIT clear"), "{message}");
}

/// Checks the guard and DIT state outside every guard: nothing held, and
/// DIT clear, except where it lingers (see [`LINGERS`]).
fn assert_released(what: &str) {
    assert!(!model::live(), "{what}: a guard is still live");
    assert!(!Dit::is_held(), "{what}: is_held after release");
    #[cfg(all(debug_assertions, rind_dit))]
    if !LINGERS {
        assert_ne!(dit_on(), Some(true), "{what}: DIT set after release");
    }
}

/// `with` toggles once for everything inside, returns the closure's value,
/// and reports the guard as held only where rind sets DIT.
#[test]
fn with_toggles_once_and_returns_its_value() {
    let tag_key = hmac_key();
    let packet_key = aead_key(&aead::AES_128_GCM);
    let made = toggles(|| {
        let tags = Dit::with(|| {
            assert_eq!(Dit::is_held(), cfg!(rind_dit));
            #[cfg(all(debug_assertions, rind_dit))]
            if let Some(on) = dit_on() {
                assert!(on, "DIT clear inside `with`");
            }
            let mut packet = [4; 64];
            let sealed = packet_key
                .seal_in_place_separate_tag(nonce(), b"", &mut packet)
                .unwrap();
            (hmac::sign(&tag_key, &packet), sealed)
        });
        assert_eq!(tags.0.as_ref().len(), 32);
    });
    assert_eq!(made, 1);
    assert_released("with");
}

/// Guards nest, in any drop order, and DIT stays held until the last one
/// goes: the inner ones toggle nothing.
#[test]
fn nested_guards_toggle_once_and_release_last() {
    let made = toggles(|| {
        let outer = Dit::hold();
        let inner = Dit::hold();
        Dit::with(|| {
            Dit::batch(0..3, |_| {
                let _digest = digest::digest(&digest::SHA256, b"x");
                Ok::<(), ()>(())
            })
            .unwrap();
        });
        // The outer guard drops first; the inner one still holds.
        drop(outer);
        assert_eq!(Dit::is_held(), cfg!(rind_dit));
        assert!(model::live());
        drop(inner);
    });
    assert_eq!(made, 1);
    assert_released("nested guards");
}

/// A panic inside `with` or `batch` unwinds through the guard, which
/// releases DIT as a return would.
#[test]
fn a_panic_inside_a_guard_releases_it() {
    let caught = panic::catch_unwind(|| {
        Dit::with(|| {
            let _digest = digest::digest(&digest::SHA256, b"x");
            panic!("inside with");
        })
    });
    assert!(caught.is_err());
    assert_released("panic in with");

    let caught = panic::catch_unwind(|| {
        Dit::batch(0..4, |n| {
            assert!(n < 2, "inside batch");
            Ok::<(), ()>(())
        })
    });
    assert!(caught.is_err());
    assert_released("panic in batch");

    // A panic in a rind call made under a guard, with an entry live too.
    let caught = panic::catch_unwind(|| {
        let _dit = Dit::hold();
        let _entry = super::Entry::new_secret();
        panic!("under a guard and an entry");
    });
    assert!(caught.is_err());
    assert_released("panic under a guard and an entry");
}

/// `batch` runs every item under one toggle, and stops at the first error,
/// returning it with the guard released.
#[test]
fn batch_toggles_once_and_stops_at_an_error() {
    let packet_key = aead_key(&aead::AES_128_GCM);
    let header_key = quic_key(&aead::quic::AES_128);
    let mut seen = 0;
    let made = toggles(|| {
        Dit::batch(0..32u64, |number| {
            let mut packet = [0u8; 64];
            let nonce = aead::Nonce::from_sequence(&[3; 12], number);
            let tag = packet_key.seal_in_place_separate_tag(nonce, b"h", &mut packet)?;
            let _mask = header_key.mask(tag.as_ref().try_into().unwrap());
            seen += 1;
            Ok::<(), crate::Error>(())
        })
        .unwrap();
    });
    assert_eq!((made, seen), (1, 32));
    assert_released("batch");

    let mut seen = 0;
    let result = Dit::batch(0..8, |n| {
        seen += 1;
        if n == 2 { Err(n) } else { Ok(()) }
    });
    assert_eq!((result, seen), (Err(2), 3));
    assert_released("batch error");
}

/// Outside a guard nothing is held, inside an entry included: `is_held`
/// reports guards, not entries.
#[test]
fn is_held_reports_guards_only() {
    assert!(!Dit::is_held());
    let entry = super::Entry::new_secret();
    assert!(!Dit::is_held());
    drop(entry);
    let dit = Dit::hold();
    assert_eq!(Dit::is_held(), cfg!(rind_dit));
    drop(dit);
    assert_released("is_held");
}

/// `admin/dit-qemu` runs this under qemu-aarch64 with
/// `admin/dit-qemu-plugin.c`, which reads PSTATE.DIT at every instruction
/// each call executes, its callees' included (core's, and libc's `memcpy`),
/// not only at the `Entry` and `assert_held` checks the other tests read.
/// It fails a call that ran without DIT between two instructions that ran
/// with it, or never set it. The names go to stdout, one per window, in
/// order.
#[cfg(all(target_arch = "aarch64", rind_dit))]
#[test]
#[ignore = "admin/dit-qemu runs it under qemu-aarch64"]
fn dit_qemu_every_secret_call() {
    for call in calls() {
        std::println!("dit-qemu: {}", call.name);
        dit_qemu_mark!("hint #84");
        (call.run)();
        dit_qemu_mark!("hint #85");
    }

    // Planted: DIT cleared under a live `Entry` and set again, which the
    // plugin must report as a hole.
    std::println!("dit-qemu: planted: a hole");
    dit_qemu_mark!("hint #84");
    let entry = super::Entry::new_secret();
    crate::low::leave_cpu_state(1);
    core::hint::black_box([0u8; 64]);
    let _ = crate::low::enter_cpu_state();
    drop(entry);
    dit_qemu_mark!("hint #85");

    // Planted: a call that clears DIT early, then does secret work before it
    // returns. Nothing after the clear sets DIT again, so this is no hole:
    // the check of what ran after DIT was last cleared must report it.
    std::println!("dit-qemu: planted: a secret tail");
    dit_qemu_mark!("hint #84");
    drop(core::hint::black_box(super::Entry::new_secret()));
    core::hint::black_box(crate::low::chacha20_block(
        core::hint::black_box(&[5; 32]),
        core::hint::black_box(&[6; 16]),
    ));
    dit_qemu_mark!("hint #85");

    // Planted: work that never sets DIT, which the plugin must report.
    std::println!("dit-qemu: planted: no DIT");
    dit_qemu_mark!("hint #84");
    core::hint::black_box(core::hint::black_box([1u8; 64]).iter().sum::<u8>());
    dit_qemu_mark!("hint #85");
}

/// A caller that set DIT itself keeps it. rind clears only what it set, so
/// no call, guard, `with`, or `batch`, nested in any order or unwound by a
/// panic, clears DIT that was on before rind ran.
#[cfg(all(debug_assertions, rind_dit))]
#[test]
fn a_caller_set_dit_survives_every_call_and_guard() {
    if dit_on().is_none() {
        return;
    }
    if LINGERS {
        crate::low::leave_cpu_state(1);
    }
    // The caller's own `msr DIT, #1`.
    assert_eq!(crate::low::enter_cpu_state(), 1);
    let still_set =
        |what: &str| assert_eq!(dit_on(), Some(true), "{what} cleared the caller's DIT");
    for call in calls() {
        (call.run)();
        still_set(call.name);
    }
    drop(Dit::hold());
    still_set("a guard");
    Dit::with(|| ());
    still_set("with");
    Dit::batch(0..3, |_| Ok::<(), ()>(())).unwrap();
    still_set("batch");
    let (outer, inner) = (Dit::hold(), Dit::hold());
    drop(outer);
    (calls()[0].run)();
    drop(inner);
    still_set("guards dropped out of order");
    let caught = panic::catch_unwind(|| Dit::with(|| panic!("inside with")));
    assert!(caught.is_err());
    still_set("a panic inside with");
    assert!(!Dit::is_held());
    crate::low::leave_cpu_state(1);
    assert_eq!(dit_on(), Some(false));
}

/// The last guard to drop puts DIT back as the first guard found it, so a
/// caller that sets DIT itself inside a guard rind took loses it when the
/// guard drops: set it before taking the guard to keep it.
#[cfg(all(debug_assertions, rind_dit))]
#[test]
fn dit_returns_to_what_the_first_guard_found() {
    if dit_on().is_none() || LINGERS {
        return;
    }
    let dit = Dit::hold();
    // The caller's own `msr DIT, #1`, a no-op since the guard set it.
    assert_eq!(crate::low::enter_cpu_state(), 0);
    drop(dit);
    assert_eq!(dit_on(), Some(false));
}

/// A thread starts with no guard of its parent's: the guard counts are the
/// thread's own. Linux copies PSTATE into a new thread, so a child spawned
/// under a guard may start with DIT set, though nothing it holds keeps it
/// on; rind then leaves it as the child found it. Either way every secret
/// call the child makes runs under DIT.
#[cfg(all(debug_assertions, rind_dit))]
#[test]
fn a_thread_spawned_under_a_guard_holds_nothing() {
    if dit_on().is_none() || LINGERS {
        return;
    }
    let dit = Dit::hold();
    let (held, before, after) = std::thread::spawn(|| {
        let before = dit_on();
        let checks = super::dit_checks();
        (calls()[0].run)();
        assert!(
            super::dit_checks() > checks,
            "the child ran no PSTATE.DIT check"
        );
        (Dit::is_held(), before, dit_on())
    })
    .join()
    .unwrap();
    drop(dit);
    assert!(!held, "a new thread inherited a guard");
    assert_eq!(
        before, after,
        "rind changed the DIT a new thread started with"
    );
    assert_eq!(dit_on(), Some(false));
}

#[cfg(all(debug_assertions, rind_dit, unix))]
static SIGNALLED: std::sync::Mutex<Vec<Option<bool>>> = std::sync::Mutex::new(Vec::new());

/// A signal handler that makes a secret call, and one that sets DIT and
/// returns with it set. Test-only: it locks a mutex, which is not
/// async-signal-safe in general, but the signal is raised synchronously on
/// a thread that holds no lock.
#[cfg(all(debug_assertions, rind_dit, unix))]
extern "C" fn on_signal(_: libc::c_int) {
    let found = dit_on();
    drop(super::Entry::new_secret());
    let left = dit_on();
    let _ = crate::low::enter_cpu_state();
    SIGNALLED.lock().unwrap().extend([found, left]);
}

/// A signal handler that runs rind under a guard, or outside one, leaves the
/// interrupted code's DIT as it was: rind restores what the handler found,
/// and the kernel's signal return restores the interrupted PSTATE, DIT
/// included, even after a handler that left DIT set.
#[cfg(all(debug_assertions, rind_dit, unix))]
#[test]
fn a_signal_handler_leaves_the_interrupted_dit() {
    if dit_on().is_none() || LINGERS {
        return;
    }
    // SAFETY: installs a handler for a signal nothing else in the tests
    // uses, and raises it on this thread.
    unsafe {
        libc::signal(
            libc::SIGUSR2,
            on_signal as extern "C" fn(libc::c_int) as libc::sighandler_t,
        );
        libc::raise(libc::SIGUSR2);
    }
    assert_eq!(dit_on(), Some(false), "a handler's DIT outlived it");
    let dit = Dit::hold();
    // SAFETY: as above.
    unsafe { libc::raise(libc::SIGUSR2) };
    assert_eq!(dit_on(), Some(true), "a handler cleared a guard's DIT");
    assert!(Dit::is_held());
    drop(dit);
    assert_eq!(dit_on(), Some(false));
    let seen = SIGNALLED.lock().unwrap().clone();
    assert_eq!(seen.len(), 4, "{seen:?}");
    // Inside each handler, the secret call left DIT as the handler found it.
    assert_eq!(seen[0], seen[1], "{seen:?}");
    assert_eq!(seen[2], seen[3], "{seen:?}");
}

/// `--cfg rind_dit_autohold` keeps DIT on after a secret call, through the
/// next calls, until a public call or the batch's limit clears it, and
/// never clears DIT the caller set.
#[cfg(all(debug_assertions, rind_dit, rind_dit_autohold))]
#[test]
fn autohold_batches_until_a_public_call_or_its_limit() {
    use super::autohold::{BATCH, in_batch};
    if dit_on().is_none() {
        return;
    }
    let secret = || drop(super::Entry::new_secret());
    let public = || drop(super::Entry::new_public());
    secret();
    assert_eq!(
        (dit_on(), in_batch()),
        (Some(true), true),
        "the first call starts a batch"
    );
    for _ in 1..BATCH {
        secret();
    }
    assert_eq!(dit_on(), Some(true), "the batch holds for its limit");
    secret();
    assert_eq!(
        (dit_on(), in_batch()),
        (Some(false), false),
        "the limit ends the batch"
    );
    secret();
    public();
    assert_eq!(
        (dit_on(), in_batch()),
        (Some(false), false),
        "a public call ends the batch"
    );
    // Nested: an inner public call does not end the batch under a live entry.
    let outer = super::Entry::new_secret();
    public();
    assert_eq!(dit_on(), Some(true));
    drop(outer);
    public();
    // A guard taken in a batch keeps DIT through a public call.
    secret();
    let dit = Dit::hold();
    public();
    assert_eq!(dit_on(), Some(true), "a public call cleared a guard's DIT");
    drop(dit);
    public();
    assert_eq!(dit_on(), Some(false));
    // The caller's own DIT is not rind's to clear.
    assert_eq!(crate::low::enter_cpu_state(), 1);
    secret();
    public();
    for _ in 0..=BATCH {
        secret();
    }
    assert_eq!(
        (dit_on(), in_batch()),
        (Some(true), false),
        "rind cleared the caller's DIT"
    );
    crate::low::leave_cpu_state(1);
}
