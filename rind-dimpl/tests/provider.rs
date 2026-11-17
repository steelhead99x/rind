//! Calls the provider's components directly, for edges a handshake between
//! well-behaved peers never reaches.

use dimpl::crypto::{
    Aad, Buf, CryptoProvider, HashAlgorithm, NamedGroup, Nonce, SignatureAlgorithm, TmpBuf,
    aws_lc_rs,
};
use dimpl::{CryptoError, CryptoOperation};

fn rind() -> CryptoProvider {
    rind_dimpl::default_provider()
}

fn certificate(algorithm: &'static rcgen::SignatureAlgorithm) -> (Vec<u8>, Vec<u8>) {
    let key = rcgen::KeyPair::generate_for(algorithm).unwrap();
    let cert = rcgen::CertificateParams::new(Vec::<String>::new())
        .unwrap()
        .self_signed(&key)
        .unwrap();
    (cert.der().to_vec(), key.serialize_der())
}

#[test]
fn prefers_chacha20_without_aes_hardware() {
    // CI runs armv7 on a CPU model with the crypto extension and one without,
    // and aarch64 and x86_64 with AES hardware and with it denied, and names
    // which, so both orders are checked.
    let expected = match cfg!(target_arch = "x86_64") {
        true => std::env::var_os("RIND_TEST_X86_AES_HARDWARE"),
        false => std::env::var_os("RIND_TEST_ARM_CRYPTO_EXT"),
    };
    if let Some(expected) = expected {
        assert_eq!(rind::cpu::has_aes_hardware(), expected == "1");
    }

    use dimpl::crypto::{Dtls12CipherSuite as Dtls12, Dtls13CipherSuite as Dtls13};
    let mut dtls12 = vec![
        Dtls12::ECDHE_ECDSA_AES128_GCM_SHA256,
        Dtls12::ECDHE_ECDSA_AES256_GCM_SHA384,
        Dtls12::ECDHE_ECDSA_CHACHA20_POLY1305_SHA256,
    ];
    let mut dtls13 = vec![
        Dtls13::AES_128_GCM_SHA256,
        Dtls13::AES_256_GCM_SHA384,
        Dtls13::CHACHA20_POLY1305_SHA256,
    ];
    if !rind::cpu::has_aes_hardware() {
        dtls12.rotate_right(1);
        dtls13.rotate_right(1);
    }

    let provider = rind();
    assert_eq!(
        provider
            .cipher_suites
            .iter()
            .map(|s| s.suite())
            .collect::<Vec<_>>(),
        dtls12
    );
    assert_eq!(
        provider
            .dtls13_cipher_suites
            .iter()
            .map(|s| s.suite())
            .collect::<Vec<_>>(),
        dtls13
    );
}

#[test]
fn record_number_masks_match_aws_lc() {
    let aws_lc = aws_lc_rs::default_provider();
    for suite in rind().dtls13_cipher_suites {
        let reference = aws_lc
            .dtls13_cipher_suites
            .iter()
            .find(|s| s.suite() == suite.suite())
            .unwrap();
        let key: Vec<u8> = (0..suite.key_len() as u8).collect();
        // The all-ones sample puts ChaCha20's block counter at its maximum.
        for sample in [[0u8; 16], [0xff; 16], *b"0123456789abcdef"] {
            // aws-lc-rs fills only the five bytes QUIC uses for ChaCha20;
            // dimpl masks at most a two-byte sequence number.
            assert_eq!(
                suite.encrypt_sn(&key, &sample)[..5],
                reference.encrypt_sn(&key, &sample)[..5],
                "{:?} {sample:?}",
                suite.suite()
            );
        }
    }
}

#[test]
fn records_are_rejected_when_short_or_altered() {
    let provider = rind();
    for suite in provider.dtls13_cipher_suites {
        let label = format!("{:?}", suite.suite());
        let key = vec![7u8; suite.key_len()];
        let nonce = Nonce([1; 12]);
        let mut cipher = suite.create_cipher(&key).unwrap();

        let mut record = Buf::new();
        record.extend_from_slice(b"record");
        cipher
            .encrypt(&mut record, Aad(Default::default()), nonce)
            .unwrap();
        assert_eq!(record.len(), 6 + 16, "{label}");

        let mut opened = record.to_vec();
        let mut buf = TmpBuf::new(&mut opened);
        cipher
            .decrypt(&mut buf, Aad(Default::default()), nonce)
            .unwrap();
        assert_eq!(buf.as_ref(), b"record", "{label}");

        for i in [0, record.len() - 1] {
            let mut altered = record.to_vec();
            altered[i] ^= 1;
            let mut buf = TmpBuf::new(&mut altered);
            assert_eq!(
                cipher.decrypt(&mut buf, Aad(Default::default()), nonce),
                Err(CryptoError::OperationFailed(CryptoOperation::Decrypt)),
                "{label} byte {i}"
            );
        }

        let mut short = [0u8; 15];
        let mut buf = TmpBuf::new(&mut short);
        assert_eq!(
            cipher.decrypt(&mut buf, Aad(Default::default()), nonce),
            Err(CryptoError::CiphertextTooShort {
                minimum: 16,
                actual: 15
            }),
            "{label}"
        );
    }
}

#[test]
fn cipher_keys_of_the_wrong_length_are_refused() {
    let provider = rind();
    for suite in provider.dtls13_cipher_suites {
        // An AES-128 suite must not quietly run AES-256, nor the reverse.
        for len in [0, 15, 16, 24, 32, 33] {
            if len == suite.key_len() {
                continue;
            }
            assert!(
                suite.create_cipher(&vec![0; len]).is_err(),
                "{:?} accepted a {len}-byte key",
                suite.suite()
            );
        }
    }
}

#[test]
fn invalid_key_shares_are_refused() {
    let mut off_curve = vec![0x04];
    off_curve.extend_from_slice(&[0; 64]);
    let mut compressed = vec![0x02];
    compressed.extend_from_slice(&[0x11; 32]);

    let cases: [(NamedGroup, &[u8]); 6] = [
        // A low-order point makes the shared secret zero.
        (NamedGroup::X25519, &[0; 32]),
        (NamedGroup::X25519, &[9; 31]),
        (NamedGroup::Secp256r1, &off_curve),
        (NamedGroup::Secp256r1, &compressed),
        (NamedGroup::Secp384r1, &off_curve),
        (NamedGroup::Secp384r1, &[]),
    ];
    let provider = rind();
    for (group, peer) in cases {
        let kx = provider
            .kx_groups
            .iter()
            .find(|kx| kx.name() == group)
            .unwrap();
        let exchange = kx.start_exchange(Buf::new()).unwrap();
        assert_eq!(
            exchange.complete(peer, &mut Buf::new()),
            Err(CryptoError::InvalidPublicKey(group)),
            "{group:?} {peer:?}"
        );
    }
}

/// Applies the dimpl fuzzer's `Edit` to `share`: XOR, then cut from the end.
fn edit_share(share: &mut Vec<u8>, flips: &[(u16, u8)], cut: u8) {
    if !share.is_empty() {
        for &(index, xor) in flips {
            let index = usize::from(index) % share.len();
            share[index] ^= xor;
        }
    }
    share.truncate(share.len().saturating_sub(usize::from(cut)));
}

fn accepts(provider: &CryptoProvider, group: NamedGroup, share: &[u8]) -> bool {
    provider
        .kx_groups
        .iter()
        .find(|kx| kx.name() == group)
        .unwrap()
        .start_exchange(Buf::new())
        .unwrap()
        .complete(share, &mut Buf::new())
        .is_ok()
}

/// A fresh aws-lc public key, edited as the fuzzer does, whose hybrid prefix
/// matches `y`. aws-lc accepts that point and refuses the other parity.
fn matching_hybrid(group: NamedGroup, flips: &[(u16, u8)]) -> Vec<u8> {
    for _ in 0..64 {
        let mut share = aws_share(group);
        assert_eq!(share[0], 0x04, "{group:?} publishes an uncompressed point");
        edit_share(&mut share, flips, 0);
        if (share[0] & 1) == (share[share.len() - 1] & 1) {
            return share;
        }
    }
    panic!("{group:?} produced no parity-matching hybrid share");
}

/// `point`, an uncompressed NIST point, in SEC1 compressed form.
fn compress(point: &[u8]) -> Vec<u8> {
    let (x, y) = point[1..].split_at(point.len() / 2);
    let mut compressed = vec![2 | (y[y.len() - 1] & 1)];
    compressed.extend_from_slice(x);
    compressed
}

/// The dimpl fuzzer inputs `02ff696910a40079fffff70000ff0000020a` (P-256) and
/// `09a0ff97fbffffff970100000340002b01db0d250c0c06` (P-384) are `KeyShare`
/// edits of a fresh uncompressed point: P-256 XORs index 247 with 0 and index
/// 0 with 2, and P-384 XORs index 0 with 3. Neither cuts. The prefix becomes
/// SEC1 hybrid `0x06` or `0x07`, and the coordinates stay. aws-lc-rs accepts
/// that point when the prefix's low bit matches `y`, and accepts the same
/// point compressed. Both refuse a hybrid prefix whose parity does not match,
/// and the point at infinity.
#[test]
fn nist_hybrid_key_shares_match_aws_lc() {
    let aws = aws_lc_rs::default_provider();
    let rind = rind();
    let cases = [
        (NamedGroup::Secp256r1, &[(247u16, 0u8), (0, 2)][..]),
        (NamedGroup::Secp384r1, &[(0, 3)][..]),
    ];
    for (group, flips) in cases {
        let share = matching_hybrid(group, flips);
        assert_eq!(
            accepts(&rind, group, &share),
            accepts(&aws, group, &share),
            "{group:?} hybrid {:02x}",
            share[0]
        );

        // Flip only the prefix (`0x06` / `0x07`). `y` stays on the curve, and
        // its parity no longer matches the prefix.
        let mut mismatched = share.clone();
        mismatched[0] ^= 1;
        assert_eq!(
            accepts(&rind, group, &mismatched),
            accepts(&aws, group, &mismatched),
            "{group:?} hybrid prefix parity"
        );
        assert!(
            !accepts(&aws, group, &mismatched),
            "{group:?} aws-lc-rs accepted a hybrid point whose prefix parity does not match y"
        );

        let mut uncompressed = share.clone();
        uncompressed[0] = 0x04;
        let compressed = compress(&uncompressed);
        assert_eq!(
            accepts(&rind, group, &compressed),
            accepts(&aws, group, &compressed),
            "{group:?} compressed"
        );
        assert!(
            accepts(&aws, group, &compressed),
            "{group:?} aws-lc-rs refused a compressed point"
        );

        for peer in [&[0u8][..], &compressed[..compressed.len() - 1]] {
            assert_eq!(
                accepts(&rind, group, peer),
                accepts(&aws, group, peer),
                "{group:?} {peer:?}"
            );
            assert!(!accepts(&aws, group, peer), "{group:?} {peer:?}");
        }
    }
}

/// A fresh uncompressed public key from dimpl's aws-lc-rs provider.
fn aws_share(group: NamedGroup) -> Vec<u8> {
    let aws = aws_lc_rs::default_provider();
    let kx = aws.kx_groups.iter().find(|kx| kx.name() == group).unwrap();
    kx.start_exchange(Buf::new()).unwrap().pub_key().to_vec()
}

/// Asserts rind-dimpl and dimpl's aws-lc-rs provider give `share` the same
/// verdict, naming the share if rind-dimpl panics instead.
fn assert_same_verdict(group: NamedGroup, share: &[u8]) {
    let ours = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        accepts(&rind(), group, share)
    }))
    .unwrap_or_else(|_| panic!("{group:?} panicked on {share:02x?}"));
    let theirs = accepts(&aws_lc_rs::default_provider(), group, share);
    assert_eq!(ours, theirs, "{group:?} {share:02x?}");
}

/// `a + b` for big-endian numbers of the same length, which must not overflow.
fn add_be(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut sum = a.to_vec();
    let mut carry = 0u16;
    for (digit, &b) in sum.iter_mut().zip(b).rev() {
        let total = u16::from(*digit) + u16::from(b) + carry;
        *digit = total as u8;
        carry = total >> 8;
    }
    assert_eq!(carry, 0, "the sum overflows");
    sum
}

/// Every form and length a peer can send a NIST group, valid or hostile, gets
/// the same verdict from rind-dimpl as from dimpl's aws-lc-rs provider: each
/// SEC1 prefix from the point at infinity's `0x00` past hybrid `0x07`, and
/// `0xff`, at every NIST curve's compressed and uncompressed length and one
/// byte either side; the point at infinity; empty and oversized shares; and,
/// in each of the uncompressed, compressed, and hybrid forms, `x` or `y` all
/// ones, `x` equal to the field prime, `x + p` for a valid small `x`, an `x`
/// with a flipped bit, the other `y`, an off-curve `y`, and one byte short or
/// long.
#[test]
fn nist_share_edges_match_aws_lc() {
    for (group, algorithm, prime) in [
        (
            NamedGroup::Secp256r1,
            &rind::agreement::ECDH_P256,
            "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
        ),
        (
            NamedGroup::Secp384r1,
            &rind::agreement::ECDH_P384,
            "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe\
             ffffffff0000000000000000ffffffff",
        ),
    ] {
        let prime: Vec<u8> = (0..prime.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&prime[i..i + 2], 16).unwrap())
            .collect();
        let field = prime.len();
        let point = aws_share(group);
        assert_eq!(point.len(), 1 + 2 * field);

        // The smallest `x` on the curve, found by aws-lc-rs, so that `x + p`
        // fits the field and only a reduction mod `p` would accept it.
        let small = (0u8..=255)
            .map(|x| {
                let mut share = vec![0x02; 1 + field];
                share[1..].fill(0);
                share[field] = x;
                share
            })
            .find(|share| accepts(&aws_lc_rs::default_provider(), group, share))
            .expect("a small x on the curve");
        let small_point = rind::agreement::PublicKey::new(algorithm, &small)
            .unwrap()
            .as_ref()
            .to_vec();

        let mut shares = vec![vec![], vec![0], vec![0; point.len()], vec![0xff; 4096]];
        for prefix in [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0xff] {
            for len in [33, 49, 65, 67, 97, 133] {
                for len in [len - 1, len, len + 1] {
                    let mut share: Vec<u8> = point.iter().copied().cycle().take(len).collect();
                    share[0] = prefix;
                    shares.push(share);
                }
            }
        }

        let mut bases = Vec::new();
        for (uncompressed, small_x) in [(&point, false), (&small_point, true)] {
            bases.push((uncompressed.clone(), small_x));
            bases.push((compress(uncompressed), small_x));
            for prefix in [0x06, 0x07] {
                let mut hybrid = uncompressed.clone();
                hybrid[0] = prefix;
                bases.push((hybrid, small_x));
            }
        }
        for (share, small_x) in &bases {
            let x = 1..=field;
            let mut x_max = share.clone();
            x_max[x.clone()].fill(0xff);
            let mut x_prime = share.clone();
            x_prime[x.clone()].copy_from_slice(&prime);
            let mut x_flip = share.clone();
            x_flip[field] ^= 1;
            let mut other_y = share.clone();
            other_y[0] ^= 1;
            let mut long = share.clone();
            long.push(0);
            shares.extend([
                x_max,
                x_prime,
                x_flip,
                other_y,
                long,
                share[..share.len() - 1].to_vec(),
            ]);
            if *small_x {
                let mut x_plus_p = share.clone();
                x_plus_p[x.clone()].copy_from_slice(&add_be(&share[x], &prime));
                shares.push(x_plus_p);
            }
            if share.len() == point.len() {
                let mut y_max = share.clone();
                y_max[1 + field..].fill(0xff);
                let mut off_curve = share.clone();
                off_curve[share.len() - 2] ^= 1;
                shares.extend([y_max, off_curve]);
            }
        }
        shares.extend(bases.into_iter().map(|(share, _)| share));
        for share in shares {
            assert_same_verdict(group, &share);
        }
    }
}

/// Every truncation of a valid share, and each byte of it with its low or
/// high bit flipped, gets an error or a secret from rind-dimpl, never a
/// panic, and the same verdict as from dimpl's aws-lc-rs provider: X25519's
/// share, and a NIST group's in the uncompressed, compressed, and both hybrid
/// forms.
#[test]
fn mutated_key_shares_match_aws_lc() {
    for group in [
        NamedGroup::X25519,
        NamedGroup::Secp256r1,
        NamedGroup::Secp384r1,
    ] {
        let point = aws_share(group);
        let mut bases = vec![point.clone()];
        if group != NamedGroup::X25519 {
            bases.push(compress(&point));
            for prefix in [0x06, 0x07] {
                let mut hybrid = point.clone();
                hybrid[0] = prefix;
                bases.push(hybrid);
            }
        }
        for share in bases {
            for len in 0..share.len() {
                assert_same_verdict(group, &share[..len]);
            }
            for i in 0..share.len() {
                for bit in [0x01, 0x80] {
                    let mut mutated = share.clone();
                    mutated[i] ^= bit;
                    assert_same_verdict(group, &mutated);
                }
            }
        }
    }
}

/// A share wrapped in an X.509 `SubjectPublicKeyInfo` is a known difference,
/// which `README.md` lists: aws-lc-rs's `ParsedPublicKey::new` tries
/// `parse_rfc5280_public_key` before the raw point, so dimpl's aws-lc-rs
/// provider takes it, and rind-dimpl, like dimpl's RustCrypto provider,
/// refuses it.
#[test]
fn spki_key_shares_are_refused() {
    let aws = aws_lc_rs::default_provider();
    let rind = rind();
    for (group, algorithm) in [
        (NamedGroup::Secp256r1, &rcgen::PKCS_ECDSA_P256_SHA256),
        (NamedGroup::Secp384r1, &rcgen::PKCS_ECDSA_P384_SHA384),
    ] {
        let key = rcgen::KeyPair::generate_for(algorithm).unwrap();
        let spki = pem::parse(key.public_key_pem()).unwrap().into_contents();
        assert!(accepts(&aws, group, &spki), "{group:?}");
        assert!(!accepts(&rind, group, &spki), "{group:?}");
    }

    let mut spki = vec![
        0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x6e, 0x03, 0x21, 0x00,
    ];
    spki.extend_from_slice(&aws_share(NamedGroup::X25519));
    assert!(accepts(&aws, NamedGroup::X25519, &spki));
    assert!(!accepts(&rind, NamedGroup::X25519, &spki));
}

#[test]
fn signatures_are_checked_against_the_certificate() {
    let provider = rind();
    let (cert, key) = certificate(&rcgen::PKCS_ECDSA_P256_SHA256);
    let mut key = provider.key_provider.load_private_key(&key).unwrap();
    let mut signature = Buf::new();

    // A key signs only with the hash it was loaded for.
    assert_eq!(key.supported_hash_algorithms(), [HashAlgorithm::SHA256]);
    assert_eq!(
        key.sign(b"transcript", HashAlgorithm::SHA384, &mut signature),
        Err(CryptoError::SigningKeyHashMismatch {
            key_hash: HashAlgorithm::SHA256,
            requested: HashAlgorithm::SHA384,
        })
    );
    key.sign(b"transcript", HashAlgorithm::SHA256, &mut signature)
        .unwrap();

    let verify = |cert: &[u8], data: &[u8], signature: &[u8], hash, algorithm| {
        provider
            .signature_verification
            .verify_signature(cert, data, signature, hash, algorithm)
    };
    let ecdsa = SignatureAlgorithm::ECDSA;
    verify(
        &cert,
        b"transcript",
        &signature,
        HashAlgorithm::SHA256,
        ecdsa,
    )
    .unwrap();

    let failed = |hash| {
        Err(CryptoError::SignatureVerificationFailed {
            signature: ecdsa,
            hash,
            group: NamedGroup::Secp256r1,
        })
    };
    assert_eq!(
        verify(&cert, b"other", &signature, HashAlgorithm::SHA256, ecdsa),
        failed(HashAlgorithm::SHA256)
    );
    assert_eq!(
        verify(
            &cert,
            b"transcript",
            &signature,
            HashAlgorithm::SHA384,
            ecdsa
        ),
        failed(HashAlgorithm::SHA384)
    );
    let mut altered = signature.to_vec();
    *altered.last_mut().unwrap() ^= 1;
    assert_eq!(
        verify(&cert, b"transcript", &altered, HashAlgorithm::SHA256, ecdsa),
        failed(HashAlgorithm::SHA256)
    );

    assert_eq!(
        verify(
            &cert,
            b"transcript",
            &signature,
            HashAlgorithm::SHA512,
            ecdsa
        ),
        Err(CryptoError::UnsupportedSignatureVerification {
            signature: ecdsa,
            hash: HashAlgorithm::SHA512,
            group: NamedGroup::Secp256r1,
        })
    );
    assert_eq!(
        verify(
            &cert,
            b"transcript",
            &signature,
            HashAlgorithm::SHA256,
            SignatureAlgorithm::RSA
        ),
        Err(CryptoError::UnsupportedSignatureAlgorithm(
            SignatureAlgorithm::RSA
        ))
    );
    assert_eq!(
        verify(
            &cert[1..],
            b"transcript",
            &signature,
            HashAlgorithm::SHA256,
            ecdsa
        ),
        Err(CryptoError::CertificateParseFailed)
    );
    let (ed25519, _) = certificate(&rcgen::PKCS_ED25519);
    assert_eq!(
        verify(
            &ed25519,
            b"transcript",
            &signature,
            HashAlgorithm::SHA256,
            ecdsa
        ),
        Err(CryptoError::UnsupportedPublicKeyAlgorithm)
    );
}

#[test]
fn only_ecdsa_keys_load() {
    let provider = rind();
    let (_, ed25519) = certificate(&rcgen::PKCS_ED25519);
    let (_, p256) = certificate(&rcgen::PKCS_ECDSA_P256_SHA256);
    let pem = rcgen::KeyPair::try_from(p256.as_slice())
        .unwrap()
        .serialize_pem();
    assert!(
        provider
            .key_provider
            .load_private_key(pem.as_bytes())
            .is_ok()
    );

    for (key, what) in [
        (&ed25519[..], "Ed25519"),
        (&pem.as_bytes()[..pem.len() - 30], "truncated PEM"),
        (&p256[..p256.len() - 1], "truncated"),
        (&[], "empty"),
    ] {
        assert_eq!(
            provider.key_provider.load_private_key(key).err(),
            Some(CryptoError::InvalidPrivateKey),
            "{what}"
        );
    }
}

#[test]
fn ecdsa_key_encodings_load_as_aws_lc() {
    use ::aws_lc_rs::encoding::AsDer;
    use ::aws_lc_rs::signature::{
        ECDSA_P256_SHA256_ASN1_SIGNING, ECDSA_P384_SHA384_ASN1_SIGNING, EcdsaKeyPair,
    };

    let reference = aws_lc_rs::default_provider();
    let lf = pem::EncodeConfig::new().set_line_ending(pem::LineEnding::LF);
    for (algorithm, signing) in [
        (
            &rcgen::PKCS_ECDSA_P256_SHA256,
            &ECDSA_P256_SHA256_ASN1_SIGNING,
        ),
        (
            &rcgen::PKCS_ECDSA_P384_SHA384,
            &ECDSA_P384_SHA384_ASN1_SIGNING,
        ),
    ] {
        let (_, pkcs8) = certificate(algorithm);
        let sec1 = EcdsaKeyPair::from_pkcs8(signing, &pkcs8)
            .unwrap()
            .private_key()
            .as_der()
            .unwrap()
            .as_ref()
            .to_vec();
        // dimpl's providers ignore the label, so unusual ones load too.
        for (label, der) in [
            ("PRIVATE KEY", pkcs8.clone()),
            ("EC PRIVATE KEY", sec1.clone()),
            ("UNUSUAL KEY", pkcs8),
            ("CERTIFICATE", sec1),
        ] {
            let pem = pem::encode_config(&pem::Pem::new(label, der.clone()), lf);
            let mut bad_base64 = pem.clone().into_bytes();
            bad_base64[label.len() + 20] = b'!';
            let trailing = format!("{pem}garbage\n");
            let leading = format!("text\n{pem}");
            let unterminated = format!("text {pem}");
            let crlf = format!("{}\r\n", pem.trim_end());
            let blank_line = format!("{pem}\n");
            let space = format!("{pem} ");
            let nul = format!("\0\n{pem}");
            let second_footer = format!("{pem}-----END {label}-----\n");
            for (key, loads, what) in [
                (&der[..], true, "DER"),
                (pem.as_bytes(), true, "PEM"),
                (&pem.as_bytes()[..pem.len() - 30], false, "truncated PEM"),
                (&bad_base64[..], false, "invalid base64"),
                (trailing.as_bytes(), false, "trailing garbage"),
                (leading.as_bytes(), true, "leading text"),
                (
                    unterminated.as_bytes(),
                    false,
                    "preamble without a line feed",
                ),
                (crlf.as_bytes(), true, "CRLF ending"),
                (blank_line.as_bytes(), false, "trailing blank line"),
                (space.as_bytes(), false, "trailing space"),
                (nul.as_bytes(), false, "NUL in the preamble"),
                (second_footer.as_bytes(), false, "second footer"),
                (&der[..der.len() - 1], false, "truncated DER"),
            ] {
                let rind = rind().key_provider.load_private_key(key).is_ok();
                let aws_lc = reference.key_provider.load_private_key(key).is_ok();
                assert_eq!((rind, aws_lc), (loads, loads), "{label} {what}");
            }
            for bad in ["PRIVATE  KEY", " KEY", "KEY \t", "A-B", "K\x01EY"] {
                let key = pem::encode_config(&pem::Pem::new(bad, der.clone()), lf);
                let rind = rind().key_provider.load_private_key(key.as_bytes()).is_ok();
                let aws_lc = reference
                    .key_provider
                    .load_private_key(key.as_bytes())
                    .is_ok();
                assert_eq!((rind, aws_lc), (false, false), "label {bad:?}");
            }
        }
    }
}
