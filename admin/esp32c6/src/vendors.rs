// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The same operations as [`crate::bench::run_all`], run by the RustCrypto and
//! dalek crates that build for riscv32imac, so a row's library is the only
//! difference between two rows with one operation ID. The rows use the library
//! names `admin/bench-report` uses (`rustcrypto`, `dalek`).

use crate::bench::{Clock, Row, time};
use core::hint::black_box;
use core::num::NonZeroU32;

/// The associated data of the canonical 1350 B AEAD rows (`criterion::aead_rows`).
const AAD: [u8; 32] = [0; 32];

/// Times each comparison library's operations; see [`crate::bench::run_all`] for `scale`.
pub fn run_all<C: Clock>(
    clock: &mut C,
    rounds: NonZeroU32,
    scale: u32,
    mut emit: impl FnMut(&Row),
) {
    use aes_gcm::KeyInit;
    use aes_gcm::aead::AeadInOut;
    use sha2::Digest;
    let it = |n: u32| NonZeroU32::new(n / scale.max(1)).unwrap_or(NonZeroU32::MIN);
    let buf = [0x5au8; 1350];
    let mut push = |r: Row| emit(&r);

    push(time(
        clock,
        "sha256/{lib}/1350B",
        "rustcrypto",
        rounds,
        it(8),
        || sha2::Sha256::digest(black_box(&buf))[0],
    ));
    push(time(
        clock,
        "sha512/{lib}/1350B",
        "rustcrypto",
        rounds,
        it(8),
        || sha2::Sha512::digest(black_box(&buf))[0],
    ));
    push(time(
        clock,
        "sha3-256/{lib}/1350B",
        "rustcrypto",
        rounds,
        it(8),
        || sha3::Sha3_256::digest(black_box(&buf))[0],
    ));
    {
        use hmac::{Hmac, KeyInit, Mac};
        // The canonical row keys HMAC per message, as rind's does.
        push(time(
            clock,
            "hmac-sha256/{lib}/1350B",
            "rustcrypto",
            rounds,
            it(8),
            || {
                let mut m = Hmac::<sha2::Sha256>::new_from_slice(black_box(&[1; 32])).unwrap();
                m.update(black_box(&buf));
                m.finalize().into_bytes()[0]
            },
        ));
    }
    {
        use chacha20poly1305::{ChaCha20Poly1305, aead::AeadInOut};
        let c = ChaCha20Poly1305::new_from_slice(&[4; 32]).unwrap();
        push(time(
            clock,
            "chacha20poly1305/{lib}/1350B",
            "rustcrypto",
            rounds,
            it(8),
            || {
                let mut b = *black_box(&buf);
                c.encrypt_inout_detached(
                    &Default::default(),
                    black_box(&AAD),
                    black_box(&mut b[..]).into(),
                )
                .map_or(0, |t| t[0])
            },
        ));
    }
    {
        let c = aes_gcm::Aes128Gcm::new_from_slice(&[5; 16]).unwrap();
        push(time(
            clock,
            "aes128-gcm/{lib}/1350B",
            "rustcrypto",
            rounds,
            it(8),
            || {
                let mut b = *black_box(&buf);
                c.encrypt_inout_detached(
                    &Default::default(),
                    black_box(&AAD),
                    black_box(&mut b[..]).into(),
                )
                .map_or(0, |t| t[0])
            },
        ));
    }
    {
        use ed25519_dalek::{Signer, SigningKey, Verifier};
        let sk = SigningKey::from_bytes(&[11; 32]);
        let vk = sk.verifying_key();
        // The canonical messages of rind-bench/benches/ed25519.rs, as rind's rows use.
        let sig = sk.sign(b"Test");
        push(time(
            clock,
            "ed25519-sign/{lib}",
            "dalek",
            rounds,
            it(2),
            || black_box(&sk).sign(black_box(b"123400")).to_bytes()[0],
        ));
        push(time(
            clock,
            "ed25519-verify/{lib}",
            "dalek",
            rounds,
            it(2),
            || u8::from(black_box(&vk).verify(black_box(b"Test"), black_box(&sig)).is_ok()),
        ));
    }
    // The workload of rind's row: the scalar [9; 32] against the public key of
    // [10; 32], the peer, computed once outside the timed closure.
    let peer = x25519_dalek::x25519([10; 32], x25519_dalek::X25519_BASEPOINT_BYTES);
    push(time(
        clock,
        "x25519-ecdh-stored/{lib}",
        "dalek",
        rounds,
        it(2),
        || x25519_dalek::x25519(black_box([9; 32]), black_box(peer))[0],
    ));
}

/// Whether rind and each vendor give the same bytes for the work the rows time,
/// so a faster row is not a row that did less. Runs on the host and on target.
pub fn agree() -> bool {
    use ed25519_dalek::Signer;
    use sha2::Digest;
    let buf = [0x5au8; 1350];
    let same = |a: &[u8], b: &[u8]| a == b;
    let sk = ed25519_dalek::SigningKey::from_bytes(&[11; 32]);
    let (Ok(kp), Ok(x), Ok(peer)) = (
        rind::ed25519::KeyPair::from_seed(&[11; 32]),
        rind::agreement::PrivateKey::from_scalar(&rind::agreement::X25519, &[9; 32]),
        rind::agreement::PrivateKey::from_scalar(&rind::agreement::X25519, &[10; 32]),
    ) else {
        return false;
    };
    // The timed X25519 operation is the agreement with the peer's public key,
    // so that is what is compared, and the peer keys must match too.
    let peer_public = x25519_dalek::x25519([10; 32], x25519_dalek::X25519_BASEPOINT_BYTES);
    let Ok(shared) = x.agree(peer.public_key().as_ref()) else {
        return false;
    };
    same(peer.public_key().as_ref(), &peer_public)
        && same(shared.as_ref(), &x25519_dalek::x25519([9; 32], peer_public))
        && same(
            rind::digest::digest(&rind::digest::SHA256, &buf).as_ref(),
            &sha2::Sha256::digest(buf),
        )
        && same(
            rind::digest::digest(&rind::digest::SHA512, &buf).as_ref(),
            &sha2::Sha512::digest(buf),
        )
        && same(
            rind::digest::digest(&rind::digest::SHA3_256, &buf).as_ref(),
            &sha3::Sha3_256::digest(buf),
        )
        && same(kp.sign(b"123400").as_ref(), &sk.sign(b"123400").to_bytes())
        && same(kp.sign(b"Test").as_ref(), &sk.sign(b"Test").to_bytes())
        && hmac_agrees(&buf)
        && aead_agrees(&buf)
}

/// HMAC-SHA256 over the row's key and message gives the same MAC.
fn hmac_agrees(buf: &[u8]) -> bool {
    use hmac::{Hmac, KeyInit, Mac};
    let ours = rind::hmac::sign(
        &rind::hmac::Key::new(&rind::hmac::HMAC_SHA256, &[1; 32]),
        buf,
    );
    let Ok(mut m) = Hmac::<sha2::Sha256>::new_from_slice(&[1; 32]) else {
        return false;
    };
    m.update(buf);
    ours.as_ref() == m.finalize().into_bytes().as_slice()
}

/// ChaCha20-Poly1305 and AES-128-GCM seal the row's message under its key,
/// nonce and associated data to the same ciphertext and tag, and neither
/// library refuses. The timed closures turn an error into zero, so this is
/// what makes a failed seal fail the boot check instead of timing as fast.
fn aead_agrees(buf: &[u8; 1350]) -> bool {
    use aes_gcm::KeyInit as _;
    use chacha20poly1305::aead::AeadInOut;
    let (Ok(rc), Ok(ra)) = (
        rind::aead::Key::new(&rind::aead::CHACHA20_POLY1305, &[4; 32]),
        rind::aead::Key::new(&rind::aead::AES_128_GCM, &[5; 16]),
    ) else {
        return false;
    };
    let (Ok(vc), Ok(va)) = (
        chacha20poly1305::ChaCha20Poly1305::new_from_slice(&[4; 32]),
        aes_gcm::Aes128Gcm::new_from_slice(&[5; 16]),
    ) else {
        return false;
    };
    let (mut b1, mut b2, mut b3, mut b4) = (*buf, *buf, *buf, *buf);
    let n = || rind::aead::Nonce::assume_unique_for_key([0; 12]);
    let (Ok(t1), Ok(t2)) = (
        rc.seal_in_place_separate_tag(n(), &AAD, &mut b1),
        vc.encrypt_inout_detached(&Default::default(), &AAD, (&mut b2[..]).into()),
    ) else {
        return false;
    };
    let (Ok(t3), Ok(t4)) = (
        ra.seal_in_place_separate_tag(n(), &AAD, &mut b3),
        va.encrypt_inout_detached(&Default::default(), &AAD, (&mut b4[..]).into()),
    ) else {
        return false;
    };
    b1 == b2 && t1.as_ref() == t2.as_slice() && b3 == b4 && t3.as_ref() == t4.as_slice()
}

#[cfg(all(test, feature = "all"))]
mod tests {
    use super::*;
    struct Step(u64);
    impl Clock for Step {
        fn now_ns(&mut self) -> u64 {
            self.0 += 1000;
            self.0
        }
    }

    #[test]
    fn every_comparison_operation_emits_one_row_per_rind_row_it_matches() {
        let mut rows = alloc::vec::Vec::new();
        run_all(&mut Step(0), NonZeroU32::new(3).unwrap(), 4, |r| rows.push((r.operation, r.library)));
        assert_eq!(rows.len(), 9);
        let mut rind = alloc::vec::Vec::new();
        crate::bench::run_all(&mut Step(0), NonZeroU32::new(3).unwrap(), 4, |r| rind.push(r.operation));
        for (op, _) in &rows {
            assert!(rind.contains(op), "{op} has no rind row to compare with");
        }
    }

    #[test]
    fn rind_and_the_vendors_agree_on_what_they_time() {
        assert!(super::agree());
    }
}
