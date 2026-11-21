// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The same operations as [`crate::bench::run_all`], run by the RustCrypto and
//! dalek crates that build for riscv32imac, so a row's library is the only
//! difference between two rows with one operation ID. The rows use the library
//! names `admin/bench-report` uses (`rustcrypto`, `dalek`).

use crate::bench::{Clock, Row, time};

/// Times each comparison library's operations; see [`crate::bench::run_all`] for `scale`.
pub fn run_all<C: Clock>(clock: &mut C, rounds: u32, scale: u32, mut emit: impl FnMut(&Row)) {
    use aes_gcm::KeyInit;
    use aes_gcm::aead::AeadInOut;
    use sha2::Digest;
    let it = |n: u32| (n / scale.max(1)).max(1);
    let buf = [0x5au8; 1350];
    let mut push = |r: Row| emit(&r);

    push(time(
        clock,
        "sha256/{lib}/1350B",
        "rustcrypto",
        rounds,
        it(8),
        || sha2::Sha256::digest(buf)[0],
    ));
    push(time(
        clock,
        "sha512/{lib}/1350B",
        "rustcrypto",
        rounds,
        it(8),
        || sha2::Sha512::digest(buf)[0],
    ));
    push(time(
        clock,
        "sha3-256/{lib}/1350B",
        "rustcrypto",
        rounds,
        it(8),
        || sha3::Sha3_256::digest(buf)[0],
    ));
    {
        use hmac::{Hmac, KeyInit, Mac};
        let key = Hmac::<sha2::Sha256>::new_from_slice(&[1; 32]).unwrap();
        push(time(
            clock,
            "hmac-sha256/{lib}/1350B",
            "rustcrypto",
            rounds,
            it(8),
            || {
                let mut m = key.clone();
                m.update(&buf);
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
                let mut b = buf;
                c.encrypt_inout_detached(&Default::default(), &[], (&mut b[..]).into())
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
                let mut b = buf;
                c.encrypt_inout_detached(&Default::default(), &[], (&mut b[..]).into())
                    .map_or(0, |t| t[0])
            },
        ));
    }
    {
        use ed25519_dalek::{Signer, SigningKey, Verifier};
        let sk = SigningKey::from_bytes(&[11; 32]);
        let vk = sk.verifying_key();
        let sig = sk.sign(&buf[..64]);
        push(time(
            clock,
            "ed25519-sign/{lib}",
            "dalek",
            rounds,
            it(2),
            || sk.sign(&buf[..64]).to_bytes()[0],
        ));
        push(time(
            clock,
            "ed25519-verify/{lib}",
            "dalek",
            rounds,
            it(2),
            || u8::from(vk.verify(&buf[..64], &sig).is_ok()),
        ));
    }
    push(time(clock, "x25519/{lib}", "dalek", rounds, it(2), || {
        x25519_dalek::x25519([9; 32], x25519_dalek::X25519_BASEPOINT_BYTES)[0]
    }));
}

/// Whether rind and each vendor give the same bytes for the work the rows time,
/// so a faster row is not a row that did less. Runs on the host and on target.
pub fn agree() -> bool {
    use sha2::Digest;
    let buf = [0x5au8; 1350];
    let same = |a: &[u8], b: &[u8]| a == b;
    let sk = ed25519_dalek::SigningKey::from_bytes(&[11; 32]);
    let (Ok(kp), Ok(x)) = (
        rind::ed25519::KeyPair::from_seed(&[11; 32]),
        rind::agreement::PrivateKey::from_scalar(&rind::agreement::X25519, &[9; 32]),
    ) else {
        return false;
    };
    use ed25519_dalek::Signer;
    same(
        rind::digest::digest(&rind::digest::SHA256, &buf).as_ref(),
        &sha2::Sha256::digest(buf),
    ) && same(
        rind::digest::digest(&rind::digest::SHA512, &buf).as_ref(),
        &sha2::Sha512::digest(buf),
    ) && same(
        rind::digest::digest(&rind::digest::SHA3_256, &buf).as_ref(),
        &sha3::Sha3_256::digest(buf),
    ) && same(
        kp.sign(&buf[..64]).as_ref(),
        &sk.sign(&buf[..64]).to_bytes(),
    ) && same(
        &x25519_dalek::x25519([9; 32], x25519_dalek::X25519_BASEPOINT_BYTES),
        x.public_key().as_ref(),
    )
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
        run_all(&mut Step(0), 3, 4, |r| rows.push((r.operation, r.library)));
        assert_eq!(rows.len(), 9);
        let mut rind = alloc::vec::Vec::new();
        crate::bench::run_all(&mut Step(0), 3, 4, |r| rind.push(r.operation));
        for (op, _) in &rows {
            assert!(rind.contains(op), "{op} has no rind row to compare with");
        }
    }

    #[test]
    fn rind_and_the_vendors_agree_on_what_they_time() {
        assert!(super::agree());
    }
}
