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
        let prime = hex(prime);
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
            assert_mutations_match(group, &share);
        }
    }
}

/// A DER element: `tag`, a minimal definite length, and `contents`.
fn tlv(tag: u8, contents: &[u8]) -> Vec<u8> {
    let mut out = vec![tag];
    match contents.len() {
        len @ 0..0x80 => out.push(len as u8),
        len @ 0x80..0x100 => out.extend([0x81, len as u8]),
        len => out.extend([0x82, (len >> 8) as u8, len as u8]),
    }
    out.extend_from_slice(contents);
    out
}

fn concat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}

fn hex(digits: &str) -> Vec<u8> {
    (0..digits.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&digits[i..i + 2], 16).unwrap())
        .collect()
}

/// A DER INTEGER of the big-endian unsigned `value`.
fn integer(value: &[u8]) -> Vec<u8> {
    let value = &value[value
        .iter()
        .position(|&b| b != 0)
        .unwrap_or(value.len() - 1)..];
    let mut contents = Vec::new();
    if value[0] & 0x80 != 0 {
        contents.push(0);
    }
    contents.extend_from_slice(value);
    tlv(0x02, &contents)
}

/// A `SubjectPublicKeyInfo` of `algorithm`, an AlgorithmIdentifier's
/// contents, and `key` in a BIT STRING with no unused bits.
fn spki(algorithm: &[u8], key: &[u8]) -> Vec<u8> {
    tlv(
        0x30,
        &concat(&[&tlv(0x30, algorithm), &tlv(0x03, &concat(&[&[0], key]))]),
    )
}

const ID_EC_PUBLIC_KEY: &[u8] = &[0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
const ID_EC_DH: &[u8] = &[0x06, 0x05, 0x2b, 0x81, 0x04, 0x01, 0x0c];
const ID_X25519: &[u8] = &[0x06, 0x03, 0x2b, 0x65, 0x6e];
const ID_ED25519: &[u8] = &[0x06, 0x03, 0x2b, 0x65, 0x70];
const RSA_ENCRYPTION: &[u8] = &[
    0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01,
];
const P256: &[u8] = &[0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07];
const P384: &[u8] = &[0x06, 0x05, 0x2b, 0x81, 0x04, 0x00, 0x22];
const P521: &[u8] = &[0x06, 0x05, 0x2b, 0x81, 0x04, 0x00, 0x23];
const SECP256K1: &[u8] = &[0x06, 0x05, 0x2b, 0x81, 0x04, 0x00, 0x0a];
const NULL: &[u8] = &[0x05, 0x00];

/// A NIST curve's domain parameters, in hex.
struct Params {
    p: &'static str,
    a: &'static str,
    b: &'static str,
    gx: &'static str,
    gy: &'static str,
    n: &'static str,
}

const P256_PARAMS: Params = Params {
    p: "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
    a: "ffffffff00000001000000000000000000000000fffffffffffffffffffffffc",
    b: "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b",
    gx: "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
    gy: "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
    n: "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
};

const P384_PARAMS: Params = Params {
    p: "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff",
    a: "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc",
    b: "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef",
    gx: "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
    gy: "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
    n: "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
};

/// The fields of an explicit `ECParameters` (RFC 3279 section 2.3.5), each a
/// whole DER element, so a test can replace one.
struct Explicit {
    version: Vec<u8>,
    field: Vec<u8>,
    curve: Vec<u8>,
    base: Vec<u8>,
    order: Vec<u8>,
    cofactor: Vec<u8>,
}

const PRIME_FIELD: &[u8] = &[0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x01, 0x01];

impl Explicit {
    fn new(params: &Params) -> Self {
        Self {
            version: integer(&[1]),
            field: tlv(0x30, &concat(&[PRIME_FIELD, &integer(&hex(params.p))])),
            curve: tlv(
                0x30,
                &concat(&[&tlv(0x04, &hex(params.a)), &tlv(0x04, &hex(params.b))]),
            ),
            base: tlv(0x04, &concat(&[&[0x04], &hex(params.gx), &hex(params.gy)])),
            order: integer(&hex(params.n)),
            cofactor: integer(&[1]),
        }
    }

    fn encode(&self) -> Vec<u8> {
        tlv(
            0x30,
            &concat(&[
                &self.version,
                &self.field,
                &self.curve,
                &self.base,
                &self.order,
                &self.cofactor,
            ]),
        )
    }
}

/// Explicit parameters for `params`: as OpenSSL writes them, then padded with
/// zeros, with a seed or no cofactor, which aws-lc takes, and with each field
/// wrong or misencoded, which it refuses.
fn explicit_variants(params: &Params, other: &Params) -> (Vec<Vec<u8>>, Vec<Vec<u8>>) {
    let canonical = Explicit::new(params);
    let with = |change: &dyn Fn(&mut Explicit)| {
        let mut explicit = Explicit::new(params);
        change(&mut explicit);
        explicit.encode()
    };
    let padded = |value: &str| concat(&[&[0, 0], &hex(value)]);
    let taken = vec![
        canonical.encode(),
        with(&|e| {
            e.curve = tlv(
                0x30,
                &concat(&[&tlv(0x04, &padded(params.a)), &tlv(0x04, &padded(params.b))]),
            )
        }),
        with(&|e| {
            e.base = tlv(
                0x04,
                &concat(&[&[0x04], &padded(params.gx), &padded(params.gy)]),
            )
        }),
        with(&|e| e.cofactor.clear()),
        with(&|e| {
            e.curve = tlv(
                0x30,
                &concat(&[
                    &tlv(0x04, &hex(params.a)),
                    &tlv(0x04, &hex(params.b)),
                    &tlv(0x03, &[0, 0xc4, 0x9d, 0x36]),
                ]),
            )
        }),
    ];
    let mut refused = vec![
        with(&|e| e.version = integer(&[2])),
        with(&|e| e.version = tlv(0x02, &[0, 1])),
        with(&|e| e.cofactor = integer(&[2])),
        with(&|e| e.cofactor = tlv(0x02, &[0, 1])),
        with(&|e| e.cofactor.extend(NULL)),
        with(&|e| e.order = integer(&hex(other.n))),
        with(&|e| e.order = tlv(0x02, &concat(&[&[0, 0], &hex(params.n)]))),
        // Without its sign byte, an INTEGER with the top bit set is negative.
        with(&|e| e.order = tlv(0x02, &hex(params.n))),
        with(&|e| e.field = tlv(0x30, &concat(&[PRIME_FIELD, &tlv(0x02, &hex(params.p))]))),
        with(&|e| e.field = tlv(0x30, &concat(&[PRIME_FIELD, &tlv(0x02, &padded(params.p))]))),
        with(&|e| e.field = tlv(0x30, &concat(&[PRIME_FIELD, &integer(&hex(other.p))]))),
        with(&|e| {
            e.field = tlv(
                0x30,
                &concat(&[PRIME_FIELD, &integer(&hex(params.p)), NULL]),
            )
        }),
        with(&|e| {
            e.field = tlv(
                0x30,
                &concat(&[
                    &[0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x01, 0x02],
                    &integer(&hex(params.p)),
                ]),
            )
        }),
        with(&|e| {
            e.curve = tlv(
                0x30,
                &concat(&[&tlv(0x04, &hex(params.a)), &tlv(0x04, &hex(other.b))]),
            )
        }),
        with(&|e| {
            e.curve = tlv(
                0x30,
                &concat(&[&tlv(0x04, &hex(params.a)), &tlv(0x04, &hex(params.b)), NULL]),
            )
        }),
        with(&|e| {
            let mut gy = hex(params.gy);
            *gy.last_mut().unwrap() ^= 1;
            e.base = tlv(0x04, &concat(&[&[0x04], &hex(params.gx), &gy]));
        }),
        with(&|e| {
            let gy = hex(params.gy);
            let prefix = 0x02 | (gy[gy.len() - 1] & 1);
            e.base = tlv(0x04, &concat(&[&[prefix], &hex(params.gx)]));
        }),
        with(&|e| {
            e.base = tlv(
                0x04,
                &concat(&[&[0x04], &hex(params.gx), &hex(params.gy), &[0]]),
            )
        }),
    ];
    let mut extra = canonical.encode();
    extra.extend(NULL);
    refused.push(extra);
    (taken, refused)
}

/// Every truncation of `share`, and each byte with its low or high bit
/// flipped, gets the same verdict from both providers and no panic.
fn assert_mutations_match(group: NamedGroup, share: &[u8]) {
    for len in 0..share.len() {
        assert_same_verdict(group, &share[..len]);
    }
    for i in 0..share.len() {
        for bit in [0x01, 0x80] {
            let mut mutated = share.to_vec();
            mutated[i] ^= bit;
            assert_same_verdict(group, &mutated);
        }
    }
}

/// A share wrapped in an X.509 `SubjectPublicKeyInfo` gets the verdict
/// aws-lc-rs's `ParsedPublicKey::new` gives it, which tries that form before
/// the raw share: for a NIST group, each point form inside `id-ecPublicKey`
/// and the group's curve, and every other algorithm, curve, or parameters,
/// WebCrypto's `id-ecDH` among them; for X25519, its 32 bytes under
/// `id-X25519` and every other length, algorithm, or parameters. Both also
/// see the structure with bytes after it, inside it, or in an unused-bits
/// count, with non-minimal and indefinite lengths, and each truncation and
/// bit flip of every valid wrapper.
#[test]
fn spki_key_shares_match_aws_lc() {
    for (group, curve, other_curves, params, other_params) in [
        (
            NamedGroup::Secp256r1,
            P256,
            [P384, P521, SECP256K1],
            &P256_PARAMS,
            &P384_PARAMS,
        ),
        (
            NamedGroup::Secp384r1,
            P384,
            [P256, P521, SECP256K1],
            &P384_PARAMS,
            &P256_PARAMS,
        ),
    ] {
        let point = aws_share(group);
        let field = (point.len() - 1) / 2;
        let parity = point[point.len() - 1] & 1;
        let mut hybrid = point.clone();
        hybrid[0] = 0x06 | parity;
        let mut mismatched = hybrid.clone();
        mismatched[0] ^= 1;
        let mut off_curve = point.clone();
        off_curve[point.len() - 2] ^= 1;
        let mut x_max = point.clone();
        x_max[1..=field].fill(0xff);
        let compressed = compress(&point);
        let ec = concat(&[ID_EC_PUBLIC_KEY, curve]);

        let valid = [
            spki(&ec, &point),
            spki(&ec, &compressed),
            spki(&ec, &hybrid),
        ];
        for share in &valid {
            assert!(accepts(&aws_lc_rs::default_provider(), group, share));
            assert_same_verdict(group, share);
        }

        let mut shares = Vec::new();
        for key in [
            &mismatched[..],
            &off_curve,
            &x_max,
            &[0],
            &[],
            &point[..field],
        ] {
            shares.push(spki(&ec, key));
        }
        for algorithm in [
            concat(&[ID_EC_DH, curve]),
            ID_EC_PUBLIC_KEY.to_vec(),
            concat(&[ID_EC_PUBLIC_KEY, NULL]),
            concat(&[ID_EC_PUBLIC_KEY, &Explicit::new(other_params).encode()]),
            concat(&[ID_EC_PUBLIC_KEY, curve, NULL]),
            concat(&[RSA_ENCRYPTION, NULL]),
            concat(&[RSA_ENCRYPTION, curve]),
            ID_X25519.to_vec(),
            curve.to_vec(),
        ] {
            shares.push(spki(&algorithm, &point));
        }
        for other in other_curves {
            shares.push(spki(&concat(&[ID_EC_PUBLIC_KEY, other]), &point));
        }

        let body = &valid[0][2..];
        let mut trailing = valid[0].clone();
        trailing.extend_from_slice(&[0, 0]);
        let mut trailing_point = valid[0].clone();
        trailing_point.push(0x04);
        let mut unused_bits = valid[0].clone();
        let bits = unused_bits.len() - point.len() - 1;
        unused_bits[bits] = 1;
        let inner = tlv(
            0x30,
            &concat(&[&tlv(0x30, &ec), &tlv(0x03, &concat(&[&[0], &point])), NULL]),
        );
        let no_padding = tlv(0x30, &concat(&[&tlv(0x30, &ec), &tlv(0x03, &point)]));
        let mut long_length = vec![0x30, 0x81, body.len() as u8];
        long_length.extend_from_slice(body);
        let mut indefinite = vec![0x30, 0x80];
        indefinite.extend_from_slice(body);
        indefinite.extend_from_slice(&[0, 0]);
        let octet_string = tlv(
            0x30,
            &concat(&[&tlv(0x30, &ec), &tlv(0x04, &concat(&[&[0], &point]))]),
        );
        let wrapped_twice = tlv(0x30, &valid[0]);
        shares.extend([
            trailing,
            trailing_point,
            unused_bits,
            inner,
            no_padding,
            long_length,
            indefinite,
            octet_string,
            wrapped_twice,
        ]);
        let explicit = Explicit::new(params).encode();
        let explicit_spki = spki(&concat(&[ID_EC_PUBLIC_KEY, &explicit]), &point);
        assert!(
            accepts(&aws_lc_rs::default_provider(), group, &explicit_spki),
            "{group:?} aws-lc-rs refused its explicit parameters"
        );
        let (taken, refused) = explicit_variants(params, other_params);
        for (variant, aws_takes) in taken
            .iter()
            .map(|v| (v, true))
            .chain(refused.iter().map(|v| (v, false)))
        {
            for key in [&point, &compressed, &hybrid] {
                let share = spki(&concat(&[ID_EC_PUBLIC_KEY, variant]), key);
                assert_eq!(
                    accepts(&aws_lc_rs::default_provider(), group, &share),
                    aws_takes,
                    "{group:?} {share:02x?}"
                );
                shares.push(share);
            }
        }
        for share in &shares {
            assert_same_verdict(group, share);
        }
        for share in valid.iter().chain([&explicit_spki]) {
            assert_mutations_match(group, share);
        }
    }

    let key = aws_share(NamedGroup::X25519);
    let valid = spki(ID_X25519, &key);
    assert!(accepts(
        &aws_lc_rs::default_provider(),
        NamedGroup::X25519,
        &valid
    ));
    let mut trailing = valid.clone();
    trailing.push(0);
    let mut shares = vec![
        valid.clone(),
        trailing,
        spki(&concat(&[ID_X25519, NULL]), &key),
        spki(ID_ED25519, &key),
        spki(ID_EC_PUBLIC_KEY, &key),
        spki(ID_X25519, &key[..31]),
        spki(ID_X25519, &concat(&[&key, &[0]])),
        spki(ID_X25519, &[0; 32]),
    ];
    // 32 bytes in all, so aws-lc-rs takes it as a raw key once the wrapper,
    // whose key is too short, fails to parse.
    let short = spki(ID_X25519, &key[..20]);
    assert_eq!(short.len(), 32);
    shares.push(short);
    for share in &shares {
        assert_same_verdict(NamedGroup::X25519, share);
    }
    assert_mutations_match(NamedGroup::X25519, &valid);
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

/// A certificate whose public key is off its curve is refused as one, before
/// any signature is checked.
#[test]
fn certificates_with_invalid_points_are_refused() {
    let key = rcgen::KeyPair::generate_for(&rcgen::PKCS_ECDSA_P256_SHA256).unwrap();
    let cert = rcgen::CertificateParams::new(Vec::<String>::new())
        .unwrap()
        .self_signed(&key)
        .unwrap();
    let mut cert = cert.der().to_vec();
    let point = key.public_key_raw();
    let at = cert.windows(point.len()).position(|w| w == point).unwrap();
    cert[at + point.len() - 1] ^= 1;
    assert_eq!(
        rind().signature_verification.verify_signature(
            &cert,
            b"transcript",
            &[0; 64],
            HashAlgorithm::SHA256,
            SignatureAlgorithm::ECDSA
        ),
        Err(CryptoError::InvalidPublicKey(NamedGroup::Secp256r1))
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

#[test]
fn suite_parameters_match_aws_lc() {
    let aws_lc = aws_lc_rs::default_provider();
    let provider = rind();
    for suite in provider.cipher_suites {
        let reference = aws_lc
            .cipher_suites
            .iter()
            .find(|other| other.suite() == suite.suite())
            .unwrap();
        assert_eq!(suite.hash_algorithm(), reference.hash_algorithm());
        assert_eq!(suite.tag_len(), reference.tag_len());
        assert_eq!(suite.key_lengths(), reference.key_lengths());
        assert_eq!(suite.explicit_nonce_len(), reference.explicit_nonce_len());
    }
    for suite in provider.dtls13_cipher_suites {
        let reference = aws_lc
            .dtls13_cipher_suites
            .iter()
            .find(|other| other.suite() == suite.suite())
            .unwrap();
        assert_eq!(suite.hash_algorithm(), reference.hash_algorithm());
        assert_eq!(suite.tag_len(), reference.tag_len());
        assert_eq!(suite.key_len(), reference.key_len());
        assert_eq!(suite.iv_len(), reference.iv_len());
    }
}

#[test]
fn signing_keys_match_aws_lc() {
    let reference = aws_lc_rs::default_provider();
    for algorithm in [
        &rcgen::PKCS_ECDSA_P256_SHA256,
        &rcgen::PKCS_ECDSA_P384_SHA384,
    ] {
        let (_, pkcs8) = certificate(algorithm);
        let key = rind().key_provider.load_private_key(&pkcs8).unwrap();
        let aws_lc = reference.key_provider.load_private_key(&pkcs8).unwrap();
        assert_eq!(key.hash_algorithm(), aws_lc.hash_algorithm());
        assert_eq!(
            key.supported_hash_algorithms(),
            aws_lc.supported_hash_algorithms()
        );
    }
}

#[test]
fn p384_sha256_verification_reaches_the_verifier() {
    // DTLS 1.2 may verify P-384 with SHA-256. A bad signature still takes that
    // arm: deleting it reports the pair as unsupported instead of a bad signature.
    // Eight zero bytes are refused by every verifier, so a valid signature is
    // what shows the arm picked P-384 with SHA-256. aws-lc-rs publishes that
    // pair only as a verifier. Sign its digest with the P-384 key: `sign_digest`
    // uses the digest's hash and keeps the key's ASN.1 encoding.
    let (cert, key) = certificate(&rcgen::PKCS_ECDSA_P384_SHA384);
    let signing =
        rind::ecdsa::KeyPair::from_pkcs8(&rind::ecdsa::sign::P384_SHA384_ASN1, &key).unwrap();
    let digest = rind::digest::digest(&rind::digest::SHA256, b"data");
    let signature = signing.sign_digest(&digest).unwrap();
    rind()
        .signature_verification
        .verify_signature(
            &cert,
            b"data",
            signature.as_ref(),
            HashAlgorithm::SHA256,
            SignatureAlgorithm::ECDSA,
        )
        .expect("a P-384/SHA-256 signature verifies");

    let error = rind()
        .signature_verification
        .verify_signature(
            &cert,
            b"data",
            &[0; 8],
            HashAlgorithm::SHA256,
            SignatureAlgorithm::ECDSA,
        )
        .expect_err("an eight-byte signature does not verify");
    assert!(
        matches!(error, CryptoError::SignatureVerificationFailed { .. }),
        "{error:?}"
    );
}

#[test]
fn random_fill_replaces_the_buffer() {
    // Replacing `Random::fill` with `Ok(())` leaves the caller's bytes.
    // This stays out of the crate's unit tests: `admin/ctgrind adapters` runs
    // those under valgrind, and comparing the filled buffer branches on secret
    // bytes.
    let mut buf = [0x5a; 32];
    rind().secure_random.fill(&mut buf).unwrap();
    assert_ne!(buf, [0x5a; 32]);
}

/// dimpl requires `Debug` of each object, which names it and its parameters
/// but no key.
#[test]
fn debug_names_objects_without_their_keys() {
    let provider = rind();
    let hash = provider.hash_provider.create_hash(HashAlgorithm::SHA256);
    assert_eq!(format!("{hash:?}"), "Running { .. }");

    let kx = provider
        .kx_groups
        .iter()
        .find(|kx| kx.name() == NamedGroup::X25519)
        .unwrap();
    let exchange = kx.start_exchange(Buf::new()).unwrap();
    assert_eq!(format!("{exchange:?}"), "Exchange { group: X25519, .. }");

    let (_, key) = certificate(&rcgen::PKCS_ECDSA_P256_SHA256);
    let key = provider.key_provider.load_private_key(&key).unwrap();
    assert_eq!(
        format!("{key:?}"),
        "Key { group: Secp256r1, hash: SHA256, .. }"
    );

    let suite = provider.dtls13_cipher_suites[0];
    let cipher = suite.create_cipher(&vec![7; suite.key_len()]).unwrap();
    assert_eq!(format!("{cipher:?}"), "Aead");
}
