//! Acceptance parity of ML-DSA key loading with aws-lc-rs 1.19.0.
//!
//! Each case is loaded through rind-aws-lc-rs and through the locked
//! aws-lc-rs 1.19.0. Both must accept or both must reject. A rejection must
//! use the same [`KeyRejected::description_()`]. An acceptance must produce
//! the same public key. Nothing here records a known difference.

#![cfg(not(any(miri, target_family = "wasm")))]

use aws_lc_rs as theirs;
use ours::signature::KeyPair as _;
use rind_aws_lc_rs as ours;
use theirs::signature::KeyPair as _;

const ID_EC_PUBLIC_KEY: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
const P256: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07];
const P384: &[u8] = &[0x2b, 0x81, 0x04, 0x00, 0x22];
const P521: &[u8] = &[0x2b, 0x81, 0x04, 0x00, 0x23];
const RSA_ENCRYPTION: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01];
const RSASSA_PSS: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a];
const SHA256: &[u8] = &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01];
const MGF1: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x08];
const ML_DSA_OID_PREFIX: [u8; 8] = [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03];
const ML_KEM_OID_PREFIX: [u8; 8] = [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04];

struct Report {
    failures: Vec<String>,
}

impl Report {
    fn new() -> Self {
        Self {
            failures: Vec::new(),
        }
    }

    fn check(&mut self, label: &str, ours: &str, theirs: &str, fixture: Option<&str>) {
        if let Some(expected) = fixture
            && !theirs.starts_with(expected)
        {
            self.failures.push(format!(
                "FIXTURE {label}: aws-lc-rs={theirs} expected {expected}"
            ));
        }
        if ours != theirs {
            let detail = if ours.starts_with("ok:") && theirs.starts_with("ok:") {
                "rind=ok aws-lc-rs=ok public keys differ".to_string()
            } else {
                format!("rind={} aws-lc-rs={}", brief(ours), brief(theirs))
            };
            self.failures.push(format!("MISMATCH {label}: {detail}"));
        }
    }

    fn finish(self) {
        assert!(
            self.failures.is_empty(),
            "parity failures:\n{}",
            self.failures.join("\n")
        );
    }
}

fn brief(outcome: &str) -> String {
    match outcome.strip_prefix("ok:") {
        Some(public_key) => format!("ok:{} bytes", public_key.len() / 2),
        None => outcome.to_string(),
    }
}

fn der(tag: u8, contents: &[u8]) -> Vec<u8> {
    let len = contents.len();
    let mut out = Vec::with_capacity(len + 4);
    out.push(tag);
    if len < 0x80 {
        out.push(u8::try_from(len).unwrap());
    } else if len <= 0xff {
        out.push(0x81);
        out.push(u8::try_from(len).unwrap());
    } else {
        let len = u16::try_from(len).expect("element fits in two length bytes");
        out.push(0x82);
        out.extend_from_slice(&len.to_be_bytes());
    }
    out.extend_from_slice(contents);
    out
}

fn tlv(input: &[u8]) -> (u8, &[u8], &[u8]) {
    let (&tag, rest) = input.split_first().expect("tag");
    let (&first, rest) = rest.split_first().expect("length");
    let (len, rest) = match first {
        len @ 0..=0x7f => (usize::from(len), rest),
        0x81 => {
            let (&len, rest) = rest.split_first().expect("one-byte length");
            assert!(len >= 0x80, "non-minimal length");
            (usize::from(len), rest)
        }
        0x82 => {
            let (bytes, rest) = rest.split_at(2);
            let len = u16::from_be_bytes([bytes[0], bytes[1]]);
            assert!(len >= 0x100, "non-minimal length");
            (usize::from(len), rest)
        }
        other => panic!("unsupported length form {other:#x}"),
    };
    let (body, rest) = rest.split_at(len);
    (tag, body, rest)
}

fn sequence_body(der_bytes: &[u8]) -> &[u8] {
    let (tag, body, rest) = tlv(der_bytes);
    assert_eq!(tag, 0x30);
    assert!(rest.is_empty(), "bytes follow the sequence");
    body
}

fn pkcs8(version: u8, algorithm: &[u8], private_key: &[u8], suffix: &[u8]) -> Vec<u8> {
    let mut body = der(0x02, &[version]);
    body.extend_from_slice(algorithm);
    body.extend(der(0x04, private_key));
    body.extend_from_slice(suffix);
    der(0x30, &body)
}

fn algorithm(oid: &[u8], parameters: Option<&[u8]>) -> Vec<u8> {
    let mut body = der(0x06, oid);
    if let Some(parameters) = parameters {
        body.extend_from_slice(parameters);
    }
    der(0x30, &body)
}

fn oid_with_last(prefix: &[u8], last: u8) -> Vec<u8> {
    let mut oid = prefix.to_vec();
    oid.push(last);
    oid
}

/// An EC PKCS#8 document. `point` is an X9.62 point, placed in `[1]`.
/// `sec1_curve` is a named curve inside the `ECPrivateKey`, placed in `[0]`.
fn ec_pkcs8(
    curve: &[u8],
    scalar: &[u8],
    point: Option<&[u8]>,
    sec1_curve: Option<&[u8]>,
) -> Vec<u8> {
    let mut sec1 = der(0x02, &[1]);
    sec1.extend(der(0x04, scalar));
    if let Some(sec1_curve) = sec1_curve {
        sec1.extend(der(0xa0, &der(0x06, sec1_curve)));
    }
    if let Some(point) = point {
        let mut bits = vec![0x00];
        bits.extend_from_slice(point);
        sec1.extend(der(0xa1, &der(0x03, &bits)));
    }
    pkcs8(
        0,
        &algorithm(ID_EC_PUBLIC_KEY, Some(&der(0x06, curve))),
        &der(0x30, &sec1),
        &[],
    )
}

struct Nist {
    oid: &'static [u8],
    len: usize,
    order: &'static str,
    theirs: &'static theirs::agreement::Algorithm,
}

const P256_NIST: Nist = Nist {
    oid: P256,
    len: 32,
    order: "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
    theirs: &theirs::agreement::ECDH_P256,
};
const P384_NIST: Nist = Nist {
    oid: P384,
    len: 48,
    order: "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
    theirs: &theirs::agreement::ECDH_P384,
};
const P521_NIST: Nist = Nist {
    oid: P521,
    len: 66,
    order: "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409",
    theirs: &theirs::agreement::ECDH_P521,
};

fn order(curve: &Nist) -> Vec<u8> {
    let order = hex::decode(curve.order).unwrap();
    assert_eq!(order.len(), curve.len);
    order
}

fn order_minus_one(curve: &Nist) -> Vec<u8> {
    let mut order = order(curve);
    let last = order.last_mut().unwrap();
    assert_ne!(*last, 0);
    *last -= 1;
    order
}

fn scalar_one(curve: &Nist) -> Vec<u8> {
    let mut scalar = vec![0; curve.len];
    *scalar.last_mut().unwrap() = 1;
    scalar
}

fn point_of(curve: &Nist, scalar: &[u8]) -> Vec<u8> {
    assert_eq!(scalar.len(), curve.len);
    let key = theirs::agreement::PrivateKey::from_private_key(curve.theirs, scalar)
        .expect("scalar is in range");
    key.compute_public_key().unwrap().as_ref().to_vec()
}

fn mldsa_oid(last: u8) -> Vec<u8> {
    oid_with_last(&ML_DSA_OID_PREFIX, last)
}

fn seed_key(seed: &[u8], tail: &[u8]) -> Vec<u8> {
    let mut body = der(0x80, seed);
    body.extend_from_slice(tail);
    body
}

fn outcome_key(result: Result<impl PublicBytes, impl Rejected>) -> String {
    match result {
        Ok(key) => format!("ok:{}", hex::encode(key.public_bytes())),
        Err(err) => format!("err:{}", err.rejected()),
    }
}

fn outcome_public(result: Result<impl core::fmt::Debug, impl Rejected>) -> String {
    match result {
        Ok(_) => "ok".to_string(),
        Err(err) => format!("err:{}", err.rejected()),
    }
}

trait PublicBytes {
    fn public_bytes(&self) -> &[u8];
}

trait Rejected {
    fn rejected(&self) -> &str;
}

impl PublicBytes for ours::signature::PqdsaKeyPair {
    fn public_bytes(&self) -> &[u8] {
        self.public_key().as_ref()
    }
}

impl PublicBytes for theirs::signature::PqdsaKeyPair {
    fn public_bytes(&self) -> &[u8] {
        self.public_key().as_ref()
    }
}

impl Rejected for ours::error::KeyRejected {
    fn rejected(&self) -> &str {
        self.description_()
    }
}

impl Rejected for theirs::error::KeyRejected {
    fn rejected(&self) -> &str {
        self.description_()
    }
}

fn signing(
    set: u8,
) -> (
    &'static ours::signature::PqdsaSigningAlgorithm,
    &'static theirs::signature::PqdsaSigningAlgorithm,
) {
    match set {
        44 => (
            &ours::signature::ML_DSA_44_SIGNING,
            &theirs::signature::ML_DSA_44_SIGNING,
        ),
        65 => (
            &ours::signature::ML_DSA_65_SIGNING,
            &theirs::signature::ML_DSA_65_SIGNING,
        ),
        87 => (
            &ours::signature::ML_DSA_87_SIGNING,
            &theirs::signature::ML_DSA_87_SIGNING,
        ),
        _ => panic!("unknown parameter set {set}"),
    }
}

fn verifying(
    set: u8,
) -> (
    &'static ours::signature::PqdsaVerificationAlgorithm,
    &'static theirs::signature::PqdsaVerificationAlgorithm,
) {
    match set {
        44 => (&ours::signature::ML_DSA_44, &theirs::signature::ML_DSA_44),
        65 => (&ours::signature::ML_DSA_65, &theirs::signature::ML_DSA_65),
        87 => (&ours::signature::ML_DSA_87, &theirs::signature::ML_DSA_87),
        _ => panic!("unknown parameter set {set}"),
    }
}

fn load_pkcs8(set: u8, doc: &[u8]) -> (String, String) {
    let (ours_alg, theirs_alg) = signing(set);
    (
        outcome_key(ours::signature::PqdsaKeyPair::from_pkcs8(ours_alg, doc)),
        outcome_key(theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_alg, doc)),
    )
}

fn load_raw(set: u8, raw: &[u8]) -> (String, String) {
    let (ours_alg, theirs_alg) = signing(set);
    (
        outcome_key(ours::signature::PqdsaKeyPair::from_raw_private_key(
            ours_alg, raw,
        )),
        outcome_key(theirs::signature::PqdsaKeyPair::from_raw_private_key(
            theirs_alg, raw,
        )),
    )
}

fn load_public(set: u8, bytes: &[u8]) -> (String, String) {
    let (ours_alg, theirs_alg) = verifying(set);
    (
        outcome_public(ours::signature::ParsedPublicKey::new(ours_alg, bytes)),
        outcome_public(theirs::signature::ParsedPublicKey::new(theirs_alg, bytes)),
    )
}

fn check_pkcs8(report: &mut Report, label: &str, set: u8, doc: &[u8], fixture: Option<&str>) {
    let (ours, theirs) = load_pkcs8(set, doc);
    report.check(label, &ours, &theirs, fixture);
}

fn private_key_octet(doc: &[u8]) -> Vec<u8> {
    let mut rest = sequence_body(doc);
    while !rest.is_empty() {
        let (tag, body, next) = tlv(rest);
        if tag == 0x04 {
            return body.to_vec();
        }
        rest = next;
    }
    panic!("no private key");
}

fn map_pkcs1_integers(doc: &[u8], edit: impl Fn(usize, &[u8]) -> Vec<u8>) -> Vec<u8> {
    let pkcs1 = private_key_octet(doc);
    let mut rest = sequence_body(&pkcs1);
    let mut rebuilt = Vec::new();
    let mut index = 0;
    while !rest.is_empty() {
        let (tag, body, next) = tlv(rest);
        assert_eq!(tag, 0x02, "PKCS#1 field {index} is an INTEGER");
        rebuilt.extend(der(0x02, &edit(index, body)));
        rest = next;
        index += 1;
    }
    assert_eq!(index, 9, "two-prime PKCS#1");
    let algorithm = {
        let rest = sequence_body(doc);
        let (_, _, rest) = tlv(rest);
        let (tag, body, _) = tlv(rest);
        assert_eq!(tag, 0x30);
        body.to_vec()
    };
    pkcs8(0, &der(0x30, &algorithm), &der(0x30, &rebuilt), &[])
}

fn rsa_integer(doc: &[u8], wanted: usize) -> Vec<u8> {
    let pkcs1 = private_key_octet(doc);
    let mut rest = sequence_body(&pkcs1);
    let mut index = 0;
    while !rest.is_empty() {
        let (tag, body, next) = tlv(rest);
        assert_eq!(tag, 0x02);
        if index == wanted {
            return body.to_vec();
        }
        rest = next;
        index += 1;
    }
    panic!("missing integer {wanted}");
}

fn rsa_public_pkcs1(doc: &[u8]) -> Vec<u8> {
    der(
        0x30,
        &[
            der(0x02, &rsa_integer(doc, 1)),
            der(0x02, &rsa_integer(doc, 2)),
        ]
        .concat(),
    )
}

fn pss_explicit_params() -> Vec<u8> {
    let sha = der(0x30, &[der(0x06, SHA256), der(0x05, &[])].concat());
    let mgf = der(0x30, &[der(0x06, MGF1), sha.clone()].concat());
    der(
        0x30,
        &[
            der(0xa0, &sha),
            der(0xa1, &mgf),
            der(0xa2, &der(0x02, &[32])),
        ]
        .concat(),
    )
}

fn rewrap_pss(doc: &[u8], parameters: Option<&[u8]>, version: u8, suffix: &[u8]) -> Vec<u8> {
    pkcs8(
        version,
        &algorithm(RSASSA_PSS, parameters),
        &private_key_octet(doc),
        suffix,
    )
}

fn corrupt_coefficient(doc: &[u8]) -> Vec<u8> {
    map_pkcs1_integers(doc, |index, body| {
        let mut body = body.to_vec();
        if index == 8 {
            let last = body.last_mut().unwrap();
            *last ^= 0x01;
        }
        body
    })
}

fn even_modulus(doc: &[u8]) -> Vec<u8> {
    map_pkcs1_integers(doc, |index, body| {
        let mut body = body.to_vec();
        if index == 1 {
            let last = body.last_mut().unwrap();
            assert_eq!(*last & 1, 1, "modulus is odd");
            *last &= !1;
        }
        body
    })
}

fn exponent_one(doc: &[u8]) -> Vec<u8> {
    map_pkcs1_integers(
        doc,
        |index, body| {
            if index == 2 { vec![1] } else { body.to_vec() }
        },
    )
}

fn pkcs1_version(doc: &[u8], version: u8) -> Vec<u8> {
    map_pkcs1_integers(doc, |index, body| {
        if index == 0 {
            vec![version]
        } else {
            body.to_vec()
        }
    })
}

fn generated_pair(set: u8, seed: &[u8; 32]) -> (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>) {
    let (_, alg) = signing(set);
    let key = theirs::signature::PqdsaKeyPair::from_seed(alg, seed).unwrap();
    let pkcs8 = key.to_pkcs8v1().unwrap().as_ref().to_vec();
    let public = key.public_key().as_ref().to_vec();
    let raw = theirs::encoding::AsRawBytes::as_raw_bytes(&key.private_key())
        .unwrap()
        .as_ref()
        .to_vec();
    let spki =
        theirs::encoding::AsDer::<theirs::encoding::PublicKeyX509Der>::as_der(key.public_key())
            .unwrap()
            .as_ref()
            .to_vec();
    (pkcs8, public, raw, spki)
}

fn append_outer(doc: &[u8], extra: &[u8]) -> Vec<u8> {
    let mut out = doc.to_vec();
    out.extend_from_slice(extra);
    out
}

fn extend_private_key(doc: &[u8], extra: &[u8]) -> Vec<u8> {
    let mut rest = sequence_body(doc);
    let mut body = Vec::new();
    let mut extended = false;
    while !rest.is_empty() {
        let (tag, inner, next) = tlv(rest);
        if tag == 0x04 && !extended {
            let mut inner = inner.to_vec();
            inner.extend_from_slice(extra);
            body.extend(der(0x04, &inner));
            extended = true;
        } else {
            body.extend(der(tag, inner));
        }
        rest = next;
    }
    assert!(extended);
    der(0x30, &body)
}

fn attributes() -> Vec<u8> {
    let friendly = der(
        0x30,
        &[
            der(
                0x06,
                &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x14],
            ),
            der(0x31, &der(0x1e, &[0x00, 0x61])),
        ]
        .concat(),
    );
    der(0xa0, &friendly)
}

fn public_suffix(public_key: &[u8]) -> Vec<u8> {
    let mut bits = vec![0x00];
    bits.extend_from_slice(public_key);
    der(0x81, &bits)
}

const RSA2048: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der");
const RSA2047: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2047.pkcs8.der");
const RSA2049: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2049.pkcs8.der");
const RSA8192: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa8192.pkcs8.der");

fn embedded(name: &str) -> Vec<u8> {
    let hex = match name {
        "rsa1024" => RSA1024,
        "secp256k1" => SECP256K1,
        "secp224r1" => SECP224R1,
        "brainpoolP256r1" => BRAINPOOL_P256R1,
        "dsa2048" => DSA2048,
        _ => panic!("unknown embedded key {name}"),
    };
    hex::decode(hex).unwrap()
}

#[test]
fn pqdsa_from_pkcs8_rsa_consistency() {
    let mut report = Report::new();
    let keys = [
        ("rsa2048", RSA2048.to_vec(), Some("err:WrongAlgorithm")),
        ("rsa2049", RSA2049.to_vec(), Some("err:WrongAlgorithm")),
        ("rsa8192", RSA8192.to_vec(), Some("err:WrongAlgorithm")),
        ("rsa2047", RSA2047.to_vec(), Some("err:WrongAlgorithm")),
        ("rsa1024", embedded("rsa1024"), Some("err:WrongAlgorithm")),
    ];
    for (name, doc, fixture) in keys {
        check_pkcs8(
            &mut report,
            &format!("{name} consistent"),
            65,
            &doc,
            fixture,
        );
        check_pkcs8(
            &mut report,
            &format!("{name} inconsistent qInv"),
            65,
            &corrupt_coefficient(&doc),
            Some("err:InvalidEncoding"),
        );
    }
    check_pkcs8(
        &mut report,
        "rsa2048 even modulus",
        65,
        &even_modulus(RSA2048),
        Some("err:InvalidEncoding"),
    );
    check_pkcs8(
        &mut report,
        "rsa2048 exponent 1",
        65,
        &exponent_one(RSA2048),
        None,
    );
    check_pkcs8(
        &mut report,
        "rsa2048 pkcs1 version 1",
        65,
        &pkcs1_version(RSA2048, 1),
        None,
    );
    check_pkcs8(
        &mut report,
        "rsa2048 document tail",
        65,
        &append_outer(RSA2048, &[0x00]),
        None,
    );
    let v2 = pkcs8(
        1,
        &algorithm(RSA_ENCRYPTION, Some(&der(0x05, &[]))),
        &private_key_octet(RSA2048),
        &public_suffix(&rsa_public_pkcs1(RSA2048)),
    );
    check_pkcs8(&mut report, "rsa2048 v2 public key", 65, &v2, None);
    check_pkcs8(
        &mut report,
        "rsa2048 absent null",
        65,
        &pkcs8(
            0,
            &algorithm(RSA_ENCRYPTION, None),
            &private_key_octet(RSA2048),
            &[],
        ),
        None,
    );
    report.finish();
}

#[test]
fn pqdsa_from_pkcs8_ec_short_scalar() {
    let mut report = Report::new();
    for (name, curve) in [
        ("p256", &P256_NIST),
        ("p384", &P384_NIST),
        ("p521", &P521_NIST),
    ] {
        let full = scalar_one(curve);
        let point = point_of(curve, &full);
        check_pkcs8(
            &mut report,
            &format!("{name} scalar 1"),
            65,
            &ec_pkcs8(curve.oid, &full, Some(&point), None),
            Some("err:WrongAlgorithm"),
        );
        let mut short = full.clone();
        while short.first() == Some(&0) && short.len() > 1 {
            short.remove(0);
            check_pkcs8(
                &mut report,
                &format!("{name} scalar {} bytes", short.len()),
                65,
                &ec_pkcs8(curve.oid, &short, Some(&point), None),
                None,
            );
        }
        let mut longer = vec![0];
        longer.extend_from_slice(&full);
        check_pkcs8(
            &mut report,
            &format!("{name} scalar one leading zero past the field"),
            65,
            &ec_pkcs8(curve.oid, &longer, Some(&point), None),
            None,
        );
        check_pkcs8(
            &mut report,
            &format!("{name} short scalar without a point"),
            65,
            &ec_pkcs8(curve.oid, &[1], None, None),
            None,
        );
    }
    report.finish();
}

#[test]
fn ec_scalar_range() {
    let mut report = Report::new();
    for (name, curve) in [
        ("p256", &P256_NIST),
        ("p384", &P384_NIST),
        ("p521", &P521_NIST),
    ] {
        let below = order_minus_one(curve);
        let point = point_of(curve, &below);
        check_pkcs8(
            &mut report,
            &format!("{name} scalar n-1"),
            65,
            &ec_pkcs8(curve.oid, &below, Some(&point), None),
            Some("err:WrongAlgorithm"),
        );
        check_pkcs8(
            &mut report,
            &format!("{name} scalar n"),
            65,
            &ec_pkcs8(curve.oid, &order(curve), None, None),
            Some("err:InvalidEncoding"),
        );
        let mut above = order(curve);
        *above.last_mut().unwrap() += 1;
        check_pkcs8(
            &mut report,
            &format!("{name} scalar n+1"),
            65,
            &ec_pkcs8(curve.oid, &above, None, None),
            Some("err:InvalidEncoding"),
        );
        check_pkcs8(
            &mut report,
            &format!("{name} scalar 0"),
            65,
            &ec_pkcs8(curve.oid, &vec![0; curve.len], None, None),
            Some("err:InvalidEncoding"),
        );
        check_pkcs8(
            &mut report,
            &format!("{name} scalar n with scalar-1 point"),
            65,
            &ec_pkcs8(
                curve.oid,
                &order(curve),
                Some(&point_of(curve, &scalar_one(curve))),
                None,
            ),
            Some("err:InvalidEncoding"),
        );
    }
    report.finish();
}

#[test]
fn ec_mismatched_point() {
    let mut report = Report::new();
    let curve = &P256_NIST;
    let one = scalar_one(curve);
    let two = {
        let mut scalar = one.clone();
        *scalar.last_mut().unwrap() = 2;
        scalar
    };
    let point_one = point_of(curve, &one);
    let point_two = point_of(curve, &two);
    check_pkcs8(
        &mut report,
        "p256 point of scalar 2",
        65,
        &ec_pkcs8(curve.oid, &one, Some(&point_two), None),
        Some("err:InvalidEncoding"),
    );
    let mut flipped = point_one.clone();
    *flipped.last_mut().unwrap() ^= 0x01;
    check_pkcs8(
        &mut report,
        "p256 flipped point byte",
        65,
        &ec_pkcs8(curve.oid, &one, Some(&flipped), None),
        Some("err:InvalidEncoding"),
    );
    check_pkcs8(
        &mut report,
        "p256 matching [0] curve",
        65,
        &ec_pkcs8(curve.oid, &one, Some(&point_one), Some(P256)),
        Some("err:WrongAlgorithm"),
    );
    check_pkcs8(
        &mut report,
        "p256 [0] names p384",
        65,
        &ec_pkcs8(curve.oid, &one, Some(&point_one), Some(P384)),
        Some("err:InvalidEncoding"),
    );
    check_pkcs8(
        &mut report,
        "p384 algorithm with a p256 scalar and point",
        65,
        &ec_pkcs8(P384, &one, Some(&point_one), None),
        None,
    );
    check_pkcs8(
        &mut report,
        "p256 no point",
        65,
        &ec_pkcs8(curve.oid, &one, None, None),
        Some("err:WrongAlgorithm"),
    );
    for (name, curve_name) in [
        ("secp256k1", "secp256k1"),
        ("secp224r1", "secp224r1"),
        ("brainpoolP256r1", "brainpoolP256r1"),
    ] {
        check_pkcs8(
            &mut report,
            &format!("{name} scalar 1"),
            65,
            &embedded(curve_name),
            Some("err:WrongAlgorithm"),
        );
    }
    report.finish();
}

#[test]
fn pqdsa_from_pkcs8_pss_inconsistent_and_v2() {
    let mut report = Report::new();
    let base = RSA2048;
    let public = public_suffix(&rsa_public_pkcs1(base));
    let mut flipped_public = rsa_public_pkcs1(base);
    *flipped_public.last_mut().unwrap() ^= 0x01;
    let flipped_public = public_suffix(&flipped_public);
    let shapes: [(&str, Option<Vec<u8>>); 4] = [
        ("absent params", None),
        ("empty params", Some(der(0x30, &[]))),
        ("null params", Some(der(0x05, &[]))),
        ("explicit sha256 params", Some(pss_explicit_params())),
    ];
    for (name, params) in shapes {
        let params = params.as_deref();
        let consistent = rewrap_pss(base, params, 0, &[]);
        check_pkcs8(
            &mut report,
            &format!("pss 2048 {name}"),
            65,
            &consistent,
            None,
        );
        check_pkcs8(
            &mut report,
            &format!("pss 2048 inconsistent qInv {name}"),
            65,
            &rewrap_pss(&corrupt_coefficient(base), params, 0, &[]),
            None,
        );
        check_pkcs8(
            &mut report,
            &format!("pss 2048 v2 public {name}"),
            65,
            &rewrap_pss(base, params, 1, &public),
            None,
        );
        check_pkcs8(
            &mut report,
            &format!("pss 2048 v2 mismatched public {name}"),
            65,
            &rewrap_pss(base, params, 1, &flipped_public),
            None,
        );
        check_pkcs8(
            &mut report,
            &format!("pss 2048 version 1 without public {name}"),
            65,
            &rewrap_pss(base, params, 1, &[]),
            None,
        );
    }
    let small = embedded("rsa1024");
    let small_public = public_suffix(&rsa_public_pkcs1(&small));
    check_pkcs8(
        &mut report,
        "pss 1024 absent params",
        65,
        &rewrap_pss(&small, None, 0, &[]),
        Some("err:WrongAlgorithm"),
    );
    check_pkcs8(
        &mut report,
        "pss 1024 inconsistent qInv",
        65,
        &rewrap_pss(&corrupt_coefficient(&small), None, 0, &[]),
        Some("err:InvalidEncoding"),
    );
    check_pkcs8(
        &mut report,
        "pss 1024 v2 public",
        65,
        &rewrap_pss(&small, None, 1, &small_public),
        None,
    );
    check_pkcs8(
        &mut report,
        "pss 2047 absent params",
        65,
        &rewrap_pss(RSA2047, None, 0, &[]),
        Some("err:WrongAlgorithm"),
    );
    check_pkcs8(
        &mut report,
        "pss 2047 inconsistent qInv",
        65,
        &rewrap_pss(&corrupt_coefficient(RSA2047), None, 0, &[]),
        Some("err:InvalidEncoding"),
    );
    report.finish();
}

#[test]
fn mldsa_seed_tail() {
    let mut report = Report::new();
    let seed = [0x2a; 32];
    let (own, public, raw, spki) = generated_pair(65, &seed);
    check_pkcs8(&mut report, "mldsa65 own seed", 65, &own, Some("ok:"));
    check_pkcs8(
        &mut report,
        "mldsa65 seed as mldsa44",
        44,
        &own,
        Some("err:Unspecified"),
    );
    check_pkcs8(
        &mut report,
        "mldsa65 seed as mldsa87",
        87,
        &own,
        Some("err:Unspecified"),
    );
    for (name, tail) in [
        ("one zero", vec![0x00]),
        ("one ff", vec![0xff]),
        (
            "eight bytes",
            vec![0x01, 0x02, 0x03, 0x04, 0x80, 0x00, 0x00, 0x00],
        ),
        ("second seed element", der(0x80, &[0x11; 32])),
    ] {
        let doc = mldsa_pkcs8_version(18, &seed_key(&seed, &tail), 0, &[]);
        check_pkcs8(
            &mut report,
            &format!("mldsa65 own seed tail {name}"),
            65,
            &doc,
            None,
        );
        check_pkcs8(
            &mut report,
            &format!("mldsa65 seed tail as mldsa44 {name}"),
            44,
            &doc,
            None,
        );
    }
    for len in [0, 31, 33, 64] {
        let doc = mldsa_pkcs8_version(18, &seed_key(&vec![0x2a; len], &[]), 0, &[]);
        check_pkcs8(
            &mut report,
            &format!("mldsa65 seed length {len} as own set"),
            65,
            &doc,
            None,
        );
        check_pkcs8(
            &mut report,
            &format!("mldsa65 seed length {len} as mldsa44"),
            44,
            &doc,
            None,
        );
    }
    check_pkcs8(
        &mut report,
        "mldsa65 own document tail",
        65,
        &append_outer(&own, &[0x00]),
        None,
    );
    check_pkcs8(
        &mut report,
        "mldsa65 document tail as mldsa44",
        44,
        &append_outer(&own, &[0x00]),
        None,
    );
    check_pkcs8(
        &mut report,
        "mldsa65 private-key tail as own set",
        65,
        &extend_private_key(&own, &[0x00]),
        None,
    );
    let mut bad_public = public.clone();
    *bad_public.last_mut().unwrap() ^= 0x01;
    check_pkcs8(
        &mut report,
        "mldsa65 v2 matching public",
        65,
        &mldsa_pkcs8_version(18, &seed_key(&seed, &[]), 1, &public_suffix(&public)),
        None,
    );
    check_pkcs8(
        &mut report,
        "mldsa65 v2 mismatched public",
        65,
        &mldsa_pkcs8_version(18, &seed_key(&seed, &[]), 1, &public_suffix(&bad_public)),
        None,
    );
    check_pkcs8(
        &mut report,
        "mldsa65 v2 matching public as mldsa44",
        44,
        &mldsa_pkcs8_version(18, &seed_key(&seed, &[]), 1, &public_suffix(&public)),
        None,
    );
    let (ours, theirs) = load_raw(65, &raw);
    report.check("mldsa65 raw expanded", &ours, &theirs, Some("ok:"));
    let mut corrupt = raw.clone();
    corrupt[100] ^= 0x01;
    let (ours, theirs) = load_raw(65, &corrupt);
    report.check(
        "mldsa65 raw expanded flipped",
        &ours,
        &theirs,
        Some("err:InvalidEncoding"),
    );
    let (ours, theirs) = load_raw(44, &raw);
    report.check(
        "mldsa65 raw as mldsa44",
        &ours,
        &theirs,
        Some("err:Unspecified"),
    );
    let (ours, theirs) = load_raw(44, &corrupt);
    report.check(
        "mldsa65 raw flipped as mldsa44",
        &ours,
        &theirs,
        Some("err:InvalidEncoding"),
    );
    let (ours, theirs) = load_raw(65, &[]);
    report.check(
        "mldsa65 empty raw",
        &ours,
        &theirs,
        Some("err:InvalidEncoding"),
    );
    let (ours, theirs) = load_raw(65, &seed);
    report.check(
        "mldsa65 seed as raw",
        &ours,
        &theirs,
        Some("err:InvalidEncoding"),
    );
    let (_, _, raw44, _) = generated_pair(44, &seed);
    let (_, _, raw87, _) = generated_pair(87, &seed);
    let (ours, theirs) = load_raw(44, &raw87);
    report.check(
        "mldsa87 raw as mldsa44",
        &ours,
        &theirs,
        Some("err:Unspecified"),
    );
    let (ours, theirs) = load_raw(65, &raw87);
    report.check(
        "mldsa87 raw as mldsa65",
        &ours,
        &theirs,
        Some("err:Unspecified"),
    );
    let (ours, theirs) = load_raw(65, &raw44);
    report.check(
        "mldsa44 raw as mldsa65",
        &ours,
        &theirs,
        Some("err:Unspecified"),
    );
    let (ours, theirs) = load_raw(65, &raw44[..raw44.len() - 1]);
    report.check(
        "mldsa44 raw one short as mldsa65",
        &ours,
        &theirs,
        Some("err:InvalidEncoding"),
    );
    let mut one_long = raw87.clone();
    one_long.push(0);
    let (ours, theirs) = load_raw(44, &one_long);
    report.check(
        "mldsa87 raw one long as mldsa44",
        &ours,
        &theirs,
        Some("err:InvalidEncoding"),
    );
    let (ours, theirs) = load_raw(65, &raw[..raw.len() - 1]);
    report.check(
        "mldsa65 raw short",
        &ours,
        &theirs,
        Some("err:InvalidEncoding"),
    );
    let (ours, theirs) = load_public(65, &public);
    report.check("mldsa65 raw public", &ours, &theirs, Some("ok"));
    let (ours, theirs) = load_public(65, &public[..public.len() - 1]);
    report.check(
        "mldsa65 raw public short",
        &ours,
        &theirs,
        Some("err:Unspecified"),
    );
    let (ours, theirs) = load_public(65, &append_outer(&public, &[0x00]));
    report.check("mldsa65 raw public long", &ours, &theirs, None);
    let mut flipped_public = public.clone();
    *flipped_public.last_mut().unwrap() ^= 0x01;
    let (ours, theirs) = load_public(65, &flipped_public);
    report.check("mldsa65 raw public flipped", &ours, &theirs, None);
    let (ours, theirs) = load_public(65, &[]);
    report.check("mldsa65 empty public", &ours, &theirs, None);
    let (ours, theirs_out) = load_public(65, &spki);
    report.check("mldsa65 spki", &ours, &theirs_out, Some("ok"));
    let (ours, theirs_out) = load_public(65, &append_outer(&spki, &[0x00]));
    report.check("mldsa65 spki tail", &ours, &theirs_out, None);
    let null_parameter = pkcs8(
        0,
        &algorithm(&mldsa_oid(18), Some(&der(0x05, &[]))),
        &seed_key(&seed, &[]),
        &[],
    );
    for set in [65, 44] {
        check_pkcs8(
            &mut report,
            &format!("mldsa65 null parameter as mldsa{set}"),
            set,
            &null_parameter,
            None,
        );
    }
    let wycheproof = wycheproof_mldsa65_seed();
    check_pkcs8(
        &mut report,
        "wycheproof mldsa65 seed",
        65,
        &wycheproof,
        Some("ok:"),
    );
    check_pkcs8(
        &mut report,
        "wycheproof mldsa65 seed tail",
        65,
        &extend_private_key(&wycheproof, &[0x00]),
        None,
    );
    report.finish();
}

/// Every RFC 9881 private-key form of every parameter set, intact and
/// broken, bare and with each tail aws-lc ignores, loaded as each set. This
/// pins Option A: a key of another set is loaded in full before it is
/// refused, so a consistent one is `Unspecified` and an inconsistent one
/// `InvalidEncoding`, as in aws-lc-rs.
#[test]
fn mldsa_pkcs8_forms() {
    let mut report = Report::new();
    let seed = [0x5c; 32];
    for set in [44u8, 65, 87] {
        let last = match set {
            44 => 17,
            65 => 18,
            _ => 19,
        };
        let (_, public, raw, _) = generated_pair(set, &seed);
        let mut flipped = raw.clone();
        flipped[100] ^= 0x01;
        let mut other_seed = seed;
        other_seed[0] ^= 0x01;
        let both = |seed: &[u8], expanded: &[u8]| {
            der(0x30, &[der(0x04, seed), der(0x04, expanded)].concat())
        };
        let forms = [
            ("seed", der(0x80, &seed)),
            ("expanded", der(0x04, &raw)),
            ("expanded flipped", der(0x04, &flipped)),
            ("both", both(&seed, &raw)),
            ("both mismatched", both(&other_seed, &raw)),
            ("both flipped", both(&seed, &flipped)),
        ];
        for (form, private_key) in &forms {
            let mut private_tail = private_key.clone();
            private_tail.push(0x00);
            let docs = [
                ("bare", mldsa_pkcs8_version(last, private_key, 0, &[])),
                (
                    "private-key tail",
                    mldsa_pkcs8_version(last, &private_tail, 0, &[]),
                ),
                (
                    "v2 public key",
                    mldsa_pkcs8_version(last, private_key, 1, &public_suffix(&public)),
                ),
                (
                    "attributes",
                    mldsa_pkcs8_version(last, private_key, 0, &attributes()),
                ),
                (
                    "document tail",
                    append_outer(&mldsa_pkcs8_version(last, private_key, 0, &[]), &[0x00]),
                ),
            ];
            for (tail, doc) in &docs {
                for load_as in [44u8, 65, 87] {
                    check_pkcs8(
                        &mut report,
                        &format!("mldsa{set} {form} {tail} as mldsa{load_as}"),
                        load_as,
                        doc,
                        None,
                    );
                }
            }
        }
        for load_as in [44u8, 65, 87] {
            for (name, key) in [("raw", &raw), ("raw flipped", &flipped)] {
                let (ours, theirs) = load_raw(load_as, key);
                report.check(
                    &format!("mldsa{set} {name} as mldsa{load_as}"),
                    &ours,
                    &theirs,
                    None,
                );
            }
        }
    }
    report.finish();
}

fn mldsa_pkcs8_version(last: u8, private_key: &[u8], version: u8, suffix: &[u8]) -> Vec<u8> {
    pkcs8(
        version,
        &algorithm(&mldsa_oid(last), None),
        private_key,
        suffix,
    )
}

/// The first ML-DSA-65 seed PKCS#8 in Wycheproof's signing file whose seed
/// is not 32 bytes of 0x2a, the key this test builds itself.
fn wycheproof_mldsa65_seed() -> Vec<u8> {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../thirdparty/vectors/wycheproof/testvectors_v1/mldsa_65_sign_seed_test.json"
    );
    let value: serde_json::Value =
        serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
    let own = "2a".repeat(32);
    let pkcs8 = value["testGroups"]
        .as_array()
        .unwrap()
        .iter()
        .find_map(|group| {
            let seed = group["privateSeed"].as_str()?;
            let pkcs8 = group["privateKeyPkcs8"].as_str()?;
            (seed != own).then_some(pkcs8)
        })
        .unwrap();
    hex::decode(pkcs8).unwrap()
}

#[test]
fn nearby_edges() {
    let mut report = Report::new();
    check_pkcs8(
        &mut report,
        "dsa2048",
        65,
        &embedded("dsa2048"),
        Some("err:WrongAlgorithm"),
    );
    let ed_key = theirs::signature::Ed25519KeyPair::from_seed_unchecked(&[3; 32]).unwrap();
    let ed_doc = ed_key.to_pkcs8v1().unwrap();
    let ed = ed_doc.as_ref();
    check_pkcs8(&mut report, "ed25519", 65, ed, Some("err:WrongAlgorithm"));
    check_pkcs8(
        &mut report,
        "ed25519 attributes",
        65,
        &extend_suffix(ed, &attributes()),
        None,
    );
    check_pkcs8(
        &mut report,
        "ed25519 document tail",
        65,
        &append_outer(ed, &[0x00]),
        None,
    );
    let ed_public = ed_key.public_key().as_ref().to_vec();
    check_pkcs8(
        &mut report,
        "ed25519 v2 public",
        65,
        &curve25519_versioned(&[0x2b, 0x65, 0x70], &[3; 32], 1, &public_suffix(&ed_public)),
        None,
    );
    let mut bad_ed = ed_public.clone();
    *bad_ed.last_mut().unwrap() ^= 0x01;
    check_pkcs8(
        &mut report,
        "ed25519 v2 mismatched public",
        65,
        &curve25519_versioned(&[0x2b, 0x65, 0x70], &[3; 32], 1, &public_suffix(&bad_ed)),
        Some("err:InvalidEncoding"),
    );
    let x_seed = [9; 32];
    let x_doc = curve25519_versioned(&[0x2b, 0x65, 0x6e], &x_seed, 0, &[]);
    check_pkcs8(
        &mut report,
        "x25519",
        65,
        &x_doc,
        Some("err:WrongAlgorithm"),
    );
    check_pkcs8(
        &mut report,
        "x25519 attributes",
        65,
        &curve25519_versioned(&[0x2b, 0x65, 0x6e], &x_seed, 0, &attributes()),
        None,
    );
    let x_public =
        theirs::agreement::PrivateKey::from_private_key(&theirs::agreement::X25519, &x_seed)
            .unwrap()
            .compute_public_key()
            .unwrap()
            .as_ref()
            .to_vec();
    check_pkcs8(
        &mut report,
        "x25519 v2 public",
        65,
        &curve25519_versioned(&[0x2b, 0x65, 0x6e], &x_seed, 1, &public_suffix(&x_public)),
        None,
    );
    for (name, last, expanded) in [
        ("mlkem512", 1, 1632),
        ("mlkem768", 2, 2400),
        ("mlkem1024", 3, 3168),
    ] {
        let oid = oid_with_last(&ML_KEM_OID_PREFIX, last);
        let alg = algorithm(&oid, None);
        check_pkcs8(
            &mut report,
            &format!("{name} seed"),
            65,
            &pkcs8(0, &alg, &der(0x80, &[0x11; 64]), &[]),
            Some("err:WrongAlgorithm"),
        );
        check_pkcs8(
            &mut report,
            &format!("{name} seed tail"),
            65,
            &pkcs8(0, &alg, &seed_key(&[0x11; 64], &[0x00]), &[]),
            None,
        );
        check_pkcs8(
            &mut report,
            &format!("{name} seed 63"),
            65,
            &pkcs8(0, &alg, &der(0x80, &[0x11; 63]), &[]),
            Some("err:InvalidEncoding"),
        );
        check_pkcs8(
            &mut report,
            &format!("{name} expanded"),
            65,
            &pkcs8(0, &alg, &der(0x04, &vec![0x22; expanded]), &[]),
            Some("err:WrongAlgorithm"),
        );
        check_pkcs8(
            &mut report,
            &format!("{name} expanded short"),
            65,
            &pkcs8(0, &alg, &der(0x04, &vec![0x22; expanded - 1]), &[]),
            Some("err:InvalidEncoding"),
        );
    }
    report.finish();
}

fn extend_suffix(doc: &[u8], suffix: &[u8]) -> Vec<u8> {
    let mut body = sequence_body(doc).to_vec();
    body.extend_from_slice(suffix);
    der(0x30, &body)
}

fn curve25519_versioned(oid: &[u8], seed: &[u8], version: u8, suffix: &[u8]) -> Vec<u8> {
    pkcs8(version, &algorithm(oid, None), &der(0x04, seed), suffix)
}

const RSA1024: &str = "30820277020100300d06092a864886f70d0101010500048202613082025d02010002818100d8917628e8923e137bea7c3e38e8b3c9f450c7a367d600e1a8c11342f058ffe805489d4d92f8588d014f18e5c27cea30fa644e71d46696447c44503bb9dc52e51422a571a85bf4a905da23f9ea59ce30b5f2eec76dab1c16944ea8b48483028202d18480d7e0e3ce78d078a6b783c33431dac86e34faf55cb3b6e0211ff2424b02030100010281807957874d04826c259e989364899e589e1f35e3a5bad83d4632b77b83560787db089ad7085000b61ccb4ef63445f4978339c859eb8d86ad4b5215349f4254205d117f98e11bb3557e3c6c2f5b2858992e43c5e07c9434f40c3852bbbd3587eb6bb3cea25cbc90a71de1ce189b83ff90daa4e3155fcc623cc5eec74a942f1c8901024100fde3a3ce09c42388577b89b51f698f0bacb8901009b5e2dabc0ffd87603827b341fc7c9a6de912f4590eebb35efc4b8639fb8b1a7a68bdb8a6e10987783a8f79024100da5e63e8305a91c2137849ae4328e6dcff7e9b617777c991340e1e11ea5d244aafeaa0c0624a1c9a41ce4e4e47b84a8b202802135aa06e7704276ce2a698dae3024100b53d8bf1c986fad6999cd6f1353b65a22fea90ece201b5aff0107a2be9c42c930ac7f32b4acad77d17164fabfc629e87735cde3048b1fcbd94639129e3e9ea0102402246b4a9ea851ce1f8ca65ce5bae5ce68d9822ed9ea207daa9f0195a388e5c36f8fbfc359678099b50ff001d9b765b05118c161f5197631f7d606edff8c47f7f024100d84310b6d51b56e7e5f32aa5f09ef77ef2aa0d13a592228c418a9794276beea194345cdf5c1003ab48a83a1dd3c99ef87e6bd8b47dd3d5e423b348ac0da5ac7b";

const SECP256K1: &str = "308184020100301006072a8648ce3d020106052b8104000a046d306b02010104200000000000000000000000000000000000000000000000000000000000000001a1440342000479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8";

const SECP224R1: &str = "3078020100301006072a8648ce3d020106052b810400210461305f020101041c00000000000000000000000000000000000000000000000000000001a13c033a0004b70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21bd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34";

const BRAINPOOL_P256R1: &str = "308188020100301406072a8648ce3d020106092b2403030208010107046d306b02010104200000000000000000000000000000000000000000000000000000000000000001a144034200048bd2aeb9cb7e57cb2c4b482ffc81b7afb9de27e1e3bd23c23a4453bd9ace3262547ef835c3dac4fd97f8461a14611dc9c27745132ded8e545c1d54c72f046997";

const DSA2048: &str = "308202640201003082023906072a8648ce3804013082022c0282010100c08c599431df3924f64fda9256309e524f9b1ea0a9e0b5419dd76dc4c6aa8939cbda10333f601342d84613ca54690ab01035900f2e0ba0e684578e57433a6e69ce2718e298a041ee7e4dc8662d5f6f8378be56f19f23b8066df39eb49b00f4fe55c51ea44daef979755776ae4d021ca671f7ac68d31cfacf41898042751b5935db1fc7ae49bf03c1e553fcbae9d6fe56e887b3e1131239a59f7cff002c9f792e4c6a5da2ab3c12ce554aa66ed2e7d46175399a993b1e3e2e7af2d1696a3702b5bc56e2cc231eded5e0b36477f842dd51a56d583a646bce1eacf2a29c4e9e4f7c2f69495dec81e72c6ad28e808454841e5a09e23dec470ea9849c5ae6efc1654d022100c4ab66bc558a709de088237bc8328872781ee7e7aac40fdc057400608d9d19ef028201000e63b3fd86198fdb185b93aad33deff342df2d6f51aba0de0a54f0d353b6a9253e0dee0cbedea163beccf77c560c5ad10f0b2fd4d35b478fb62a257702c7e4ddfba8f30d1c89c8d3abb629dc7ba7dfcf706582091f23db7522cd314cb410da79af29deaa1f5f1d77261d18cb6cb6e408a54d0add77ccc88db82d7363b14d6f9d4c16c88095e05308397a84a2ec3a71ae07f562b7bc13b4b2353f24ad94148652db8d97fcd2893cd6039963a8a33b7ca2796ef82ad8aa763ad7bdcd6d69f76df0f595826704dc3692c96e73b6ca31e4f58b950a001522e88679a83387a086168f64f30f8dc647a1c5e94a9019984e0d763d446a5b5b331e5696bc0f8bd251c73904220220426017294ef8d321fe29b1b5c53e3aeccf85bdeb5513aaa0ffb9f217efc795ac";
