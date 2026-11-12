#![no_main]

//! Every public key loader against aws-lc-rs's: the first byte picks the
//! loader and the rest is its input. Both must accept and refuse alike, except
//! where an [`Expect`] names a difference by design, and every key rind loads
//! must re-encode to input both load again as the same key. Loaders 55 to 58
//! are ECVRF, which aws-lc-rs does not implement, checked against akd_core
//! and vrf-rfc9381.

use aws_lc_rs::agreement::ParsedPublicKeyFormat as Format;
use aws_lc_rs::encoding::{AsBigEndian, AsDer};
use aws_lc_rs::signature::KeyPair as _;
use aws_lc_rs::{
    agreement as theirs_ecdh, kem as their_kem, rsa as their_rsa, signature as theirs,
};
use der::{element, elements, sequence, spki, spki_parameters, trailing};
use libfuzzer_sys::fuzz_target;
use rind::agreement as ours_ecdh;
use rind::kem as our_kem;
use rind::signature::{self as ours, sign, verify};

mod der;

fuzz_target!(|data: &[u8]| {
    let Some((&loader, input)) = data.split_first() else {
        return;
    };
    match loader {
        0 => ecdsa_pkcs8(&P256, input),
        1 => ecdsa_pkcs8(&P384, input),
        2 => ecdsa_pkcs8(&P521, input),
        3 => ecdsa_sec1(&P256, input),
        4 => ecdsa_sec1(&P384, input),
        5 => ecdsa_sec1(&P521, input),
        6 => ecdsa_scalar(&P256, input),
        7 => ecdsa_scalar(&P384, input),
        8 => ecdsa_scalar(&P521, input),
        9 => ecdsa_public(&P256, input),
        10 => ecdsa_public(&P384, input),
        11 => ecdsa_public(&P521, input),
        12 => rsa_private(
            input,
            ours::RsaKeyPair::from_pkcs8,
            their_rsa::KeyPair::from_pkcs8,
            (trailing(input) || v2_without_public_key(input)).into(),
        ),
        13 => rsa_private(
            input,
            ours::RsaKeyPair::from_pkcs1,
            their_rsa::KeyPair::from_der,
            trailing(input).into(),
        ),
        14 => rsa_public(&RSA_1024, input),
        15 => rsa_public(&RSA_2048, input),
        16 => rsa_public(&RSA_3072, input),
        17 => rsa_components(&RSA_1024, input),
        18 => rsa_components(&RSA_2048, input),
        19 => rsa_components(&RSA_3072, input),
        20 => ed25519_pkcs8(input),
        21 => ed25519_seed(input),
        22 => ed25519_public(input),
        23 => mlkem_public(input),
        24 => ecdh_scalar(&X25519, input),
        25 => ecdh_scalar(&P256.ecdh, input),
        26 => ecdh_scalar(&P384.ecdh, input),
        27 => ecdh_scalar(&P521.ecdh, input),
        28 => x25519_pkcs8(input),
        29 => ecdsa_spki(&P256, input),
        30 => ecdsa_spki(&P384, input),
        31 => ecdsa_spki(&P521, input),
        32 => ed25519_spki(input),
        33 => rsa_spki(&RSA_2048, input),
        34 => ecdh_public(&X25519, input),
        35 => ecdh_public(&P256.ecdh, input),
        36 => ecdh_public(&P384.ecdh, input),
        37 => ecdh_public(&P521.ecdh, input),
        38 => ecdh_spki(&X25519, input),
        39 => ecdh_spki(&P256.ecdh, input),
        40 => ecdh_spki(&P384.ecdh, input),
        41 => ecdh_spki(&P521.ecdh, input),
        42 => agree_ed25519(
            ours::Ed25519KeyPair::from_seed(input),
            theirs::Ed25519KeyPair::from_seed_unchecked(input),
            Expect::Agree,
        ),
        43 => ml_dsa_pkcs8::<sign::MlDsa44>(&MLDSA_44, input),
        44 => ml_dsa_pkcs8::<sign::MlDsa65>(&MLDSA_65, input),
        45 => ml_dsa_pkcs8::<sign::MlDsa87>(&MLDSA_87, input),
        46 => ml_dsa_seed::<sign::MlDsa44>(&MLDSA_44, input),
        47 => ml_dsa_seed::<sign::MlDsa65>(&MLDSA_65, input),
        48 => ml_dsa_seed::<sign::MlDsa87>(&MLDSA_87, input),
        49 => ml_dsa_public(&MLDSA_44, input),
        50 => ml_dsa_public(&MLDSA_65, input),
        51 => ml_dsa_public(&MLDSA_87, input),
        52 => ml_dsa_spki(&MLDSA_44, input),
        53 => ml_dsa_spki(&MLDSA_65, input),
        54 => ml_dsa_spki(&MLDSA_87, input),
        55 => vrf_edwards_seed(input),
        56 => vrf_edwards_public(input),
        57 => vrf_p256_seed(input),
        58 => vrf_p256_public(input),
        _ => {}
    }
});

/// One curve's algorithms on each side, and its scalar's length.
struct Curve {
    ours: &'static ours::EcdsaSigningAlgorithm,
    ecdh: Ecdh,
    ours_verify: &'static ours::VerificationAlgorithm,
    theirs: &'static theirs::EcdsaSigningAlgorithm,
    theirs_verify: &'static theirs::EcdsaVerificationAlgorithm,
    scalar_len: usize,
}

const P256: Curve = Curve {
    ecdh: Ecdh {
        ours: &ours_ecdh::ECDH_P256,
        theirs: &theirs_ecdh::ECDH_P256,
        scalar_len: 32,
    },
    ours: &sign::ECDSA_P256_SHA256_ASN1,
    ours_verify: &verify::ECDSA_P256_SHA256_ASN1,
    theirs: &theirs::ECDSA_P256_SHA256_ASN1_SIGNING,
    theirs_verify: &theirs::ECDSA_P256_SHA256_ASN1,
    scalar_len: 32,
};

const P384: Curve = Curve {
    ecdh: Ecdh {
        ours: &ours_ecdh::ECDH_P384,
        theirs: &theirs_ecdh::ECDH_P384,
        scalar_len: 48,
    },
    ours: &sign::ECDSA_P384_SHA384_ASN1,
    ours_verify: &verify::ECDSA_P384_SHA384_ASN1,
    theirs: &theirs::ECDSA_P384_SHA384_ASN1_SIGNING,
    theirs_verify: &theirs::ECDSA_P384_SHA384_ASN1,
    scalar_len: 48,
};

const P521: Curve = Curve {
    ecdh: Ecdh {
        ours: &ours_ecdh::ECDH_P521,
        theirs: &theirs_ecdh::ECDH_P521,
        scalar_len: 66,
    },
    ours: &sign::ECDSA_P521_SHA512_ASN1,
    ours_verify: &verify::ECDSA_P521_SHA512_ASN1,
    theirs: &theirs::ECDSA_P521_SHA512_ASN1_SIGNING,
    theirs_verify: &theirs::ECDSA_P521_SHA512_ASN1,
    scalar_len: 66,
};

/// An agreement algorithm on each side, and its scalar's length.
struct Ecdh {
    ours: &'static ours_ecdh::Algorithm,
    theirs: &'static theirs_ecdh::Algorithm,
    scalar_len: usize,
}

impl Ecdh {
    /// Whether this is a NIST curve's, whose points have X9.62's forms.
    fn nist(&self) -> bool {
        self.theirs != &theirs_ecdh::X25519
    }
}

const X25519: Ecdh = Ecdh {
    ours: &ours_ecdh::X25519,
    theirs: &theirs_ecdh::X25519,
    scalar_len: 32,
};

/// An RSA verification algorithm on each side, and its smallest modulus.
struct Rsa {
    ours: &'static ours::RsaVerificationAlgorithm,
    theirs: &'static theirs::RsaParameters,
    min_bits: usize,
}

const RSA_1024: Rsa = Rsa {
    ours: &verify::legacy::RSA_PKCS1_1024_SHA256,
    theirs: &theirs::RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY,
    min_bits: 1024,
};

const RSA_2048: Rsa = Rsa {
    ours: &verify::RSA_PKCS1_SHA256,
    theirs: &theirs::RSA_PKCS1_2048_8192_SHA256,
    min_bits: 2048,
};

const RSA_3072: Rsa = Rsa {
    ours: &verify::legacy::RSA_PKCS1_3072_SHA384,
    theirs: &theirs::RSA_PKCS1_3072_8192_SHA384,
    min_bits: 3072,
};

/// An ML-DSA parameter set on each side, and its public key's length.
struct MlDsa {
    ours: &'static ours::VerificationAlgorithm,
    theirs: &'static theirs::PqdsaSigningAlgorithm,
    theirs_verify: &'static theirs::PqdsaVerificationAlgorithm,
    public_key_len: usize,
}

const MLDSA_44: MlDsa = MlDsa {
    ours: &verify::ML_DSA_44,
    theirs: &theirs::ML_DSA_44_SIGNING,
    theirs_verify: &theirs::ML_DSA_44,
    public_key_len: 1312,
};

const MLDSA_65: MlDsa = MlDsa {
    ours: &verify::ML_DSA_65,
    theirs: &theirs::ML_DSA_65_SIGNING,
    theirs_verify: &theirs::ML_DSA_65,
    public_key_len: 1952,
};

const MLDSA_87: MlDsa = MlDsa {
    ours: &verify::ML_DSA_87,
    theirs: &theirs::ML_DSA_87_SIGNING,
    theirs_verify: &theirs::ML_DSA_87,
    public_key_len: 2592,
};

/// How rind's answer to an input may differ from aws-lc-rs's.
#[derive(Clone, Copy, PartialEq)]
enum Expect {
    /// Both take it or both refuse it.
    Agree,
    /// rind refuses it by design, though aws-lc-rs may take it.
    Refused,
    /// rind may refuse it where aws-lc-rs takes it, never the reverse.
    Stricter,
}

impl From<bool> for Expect {
    /// [`Expect::Refused`] if a difference by design applies, else
    /// [`Expect::Agree`].
    fn from(refused: bool) -> Self {
        match refused {
            true => Self::Refused,
            false => Self::Agree,
        }
    }
}

fn agree<A, B, E: std::fmt::Debug>(
    ours: &Result<A, rind::Error>,
    theirs: &Result<B, E>,
    expect: Expect,
) {
    let (ours, theirs) = (ours.as_ref().err(), theirs.as_ref().err());
    match expect {
        Expect::Agree => assert_eq!(
            ours.is_none(),
            theirs.is_none(),
            "rind: {ours:?}, aws-lc-rs: {theirs:?}"
        ),
        Expect::Refused => assert!(ours.is_some(), "rind took an input it refuses by design"),
        Expect::Stricter => assert!(
            ours.is_some() || theirs.is_none(),
            "rind took an input aws-lc-rs refused: {theirs:?}"
        ),
    }
}

/// Whether `input` is a PKCS#8 version 2 document without a public key, which
/// aws-lc-rs takes for every key type. RFC 5958 sets version 2 only when the
/// public key is present.
fn v2_without_public_key(input: &[u8]) -> bool {
    let Some(contents) = sequence(input) else {
        return false;
    };
    let mut fields = elements(contents);
    fields.next() == Some((0x02, &[1][..])) && fields.all(|(tag, _)| tag != 0x81)
}

/// The `privateKey` of the PKCS#8 document `input`.
fn pkcs8_private_key(input: &[u8]) -> Option<&[u8]> {
    let (tag, private_key) = elements(sequence(input)?).nth(2)?;
    (tag == 0x04).then_some(private_key)
}

/// The public key of the SEC1 `ECPrivateKey` `input`.
fn sec1_public_key(input: &[u8]) -> Option<&[u8]> {
    let (_, field) = elements(sequence(input)?).find(|(tag, _)| *tag == 0xa1)?;
    let (tag, bits, _) = element(field)?;
    (tag == 0x03).then_some(bits)?.strip_prefix(&[0])
}

/// Whether `point` is in X9.62's hybrid form, which aws-lc-rs takes and rind
/// refuses everywhere: no consumer sends it.
fn hybrid(point: &[u8]) -> bool {
    matches!(point.first(), Some(6 | 7))
}

/// Splits `input` after a leading big-endian 16-bit length, for loaders
/// taking two values.
fn split(input: &[u8]) -> Option<(&[u8], &[u8])> {
    let (len, rest) = input.split_first_chunk::<2>()?;
    rest.split_at_checked(usize::from(u16::from_be_bytes(*len)))
}

fn ecdsa_pkcs8(curve: &Curve, input: &[u8]) {
    let ours = ours::EcdsaKeyPair::from_pkcs8(curve.ours, input);
    let theirs = theirs::EcdsaKeyPair::from_pkcs8(curve.theirs, input);
    let point = pkcs8_private_key(input).and_then(sec1_public_key);
    let refused = trailing(input) || v2_without_public_key(input) || point.is_some_and(hybrid);
    let ecdh = ours_ecdh::PrivateKey::from_pkcs8(curve.ecdh.ours, input);
    same_key(&ours, &ecdh);
    agree_ecdsa(curve, ours, theirs, refused.into());
}

/// An agreement key loads exactly the encodings an ECDSA key pair does, as
/// the same key.
fn same_key(
    ecdsa: &Result<ours::EcdsaKeyPair, rind::Error>,
    ecdh: &Result<ours_ecdh::PrivateKey, rind::Error>,
) {
    match (ecdsa, ecdh) {
        (Ok(ecdsa), Ok(ecdh)) => {
            assert_eq!(ecdsa.public_key().as_ref(), ecdh.public_key().as_ref());
        }
        (Err(ecdsa), Err(ecdh)) => assert_eq!(ecdsa, ecdh),
        (ecdsa, ecdh) => panic!(
            "ECDSA: {:?}, ECDH: {:?}",
            ecdsa.as_ref().err(),
            ecdh.as_ref().err()
        ),
    }
}

fn ecdsa_sec1(curve: &Curve, input: &[u8]) {
    let ours = ours::EcdsaKeyPair::from_sec1(curve.ours, input);
    let theirs = theirs::EcdsaKeyPair::from_private_key_der(curve.theirs, input);
    // aws-lc-rs's loader also takes PKCS#8; rind's caller always knows which
    // of the two it holds.
    let pkcs8 = theirs::EcdsaKeyPair::from_pkcs8(curve.theirs, input).is_ok();
    let refused = pkcs8 || trailing(input) || sec1_public_key(input).is_some_and(hybrid);
    let ecdh = ours_ecdh::PrivateKey::from_sec1(curve.ecdh.ours, input);
    same_key(&ours, &ecdh);
    agree_ecdsa(curve, ours, theirs, refused.into());
}

fn ecdh_scalar(ecdh: &Ecdh, input: &[u8]) {
    let (ours_algorithm, theirs_algorithm) = (ecdh.ours, ecdh.theirs);
    let ours = ours_ecdh::PrivateKey::from_scalar(ours_algorithm, input);
    let theirs = theirs_ecdh::PrivateKey::from_private_key(theirs_algorithm, input);
    agree(&ours, &theirs, Expect::Agree);
    let (Ok(ours), Ok(theirs)) = (ours, theirs) else {
        return;
    };
    let theirs_public = theirs.compute_public_key().unwrap();
    assert_eq!(ours.public_key().as_ref(), theirs_public.as_ref());
    assert_eq!(ours.to_scalar().as_ref(), input);

    // PKCS#8 loads again as the same key, on both sides for a NIST curve,
    // whose PKCS#8 aws-lc-rs takes.
    let pkcs8 = ours.to_pkcs8();
    let again = ours_ecdh::PrivateKey::from_pkcs8(ours_algorithm, pkcs8.as_ref()).unwrap();
    assert_eq!(again.public_key().as_ref(), theirs_public.as_ref());
    if theirs_algorithm != &theirs_ecdh::X25519 {
        let theirs =
            theirs_ecdh::PrivateKey::from_private_key_der(theirs_algorithm, pkcs8.as_ref())
                .unwrap();
        assert_eq!(
            theirs.compute_public_key().unwrap().as_ref(),
            theirs_public.as_ref()
        );
    }
}

/// aws-lc-rs's agreement API takes no X25519 PKCS#8, so this checks that a
/// key rind loads re-encodes to input it loads again as the same key, and
/// to the input itself for a v1 document of only its three required fields,
/// with nothing after it: attributes, which the loader skips, are not
/// written back.
fn x25519_pkcs8(input: &[u8]) {
    let Ok(ours) = ours_ecdh::PrivateKey::from_pkcs8(&ours_ecdh::X25519, input) else {
        return;
    };
    let pkcs8 = ours.to_pkcs8();
    let again = ours_ecdh::PrivateKey::from_pkcs8(&ours_ecdh::X25519, pkcs8.as_ref()).unwrap();
    assert_eq!(again.public_key().as_ref(), ours.public_key().as_ref());
    let fields: Vec<_> = elements(sequence(input).unwrap()).collect();
    if fields.len() == 3 && fields[0] == (0x02, &[0][..]) && !trailing(input) {
        assert_eq!(pkcs8.as_ref(), input);
    }
}

fn ecdsa_scalar(curve: &Curve, input: &[u8]) {
    let Some((scalar, point)) = split(input) else {
        return;
    };
    let ours = ours::EcdsaKeyPair::from_scalar_and_public_key(curve.ours, scalar, point);
    let theirs = theirs::EcdsaKeyPair::from_private_key_and_public_key(curve.theirs, scalar, point);
    // aws-lc-rs takes leading zeros added or stripped, though its docs
    // require the curve's length.
    let refused = scalar.len() != curve.scalar_len || hybrid(point);
    agree_ecdsa(curve, ours, theirs, refused.into());
}

fn agree_ecdsa(
    curve: &Curve,
    ours: Result<ours::EcdsaKeyPair, rind::Error>,
    theirs: Result<theirs::EcdsaKeyPair, aws_lc_rs::error::KeyRejected>,
    expect: Expect,
) {
    agree(&ours, &theirs, expect);
    let Ok(ours) = ours else {
        return;
    };
    if let Ok(theirs) = &theirs {
        assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());
        let scalar = theirs.private_key().as_be_bytes().unwrap();
        assert_eq!(ours.to_scalar().as_ref(), scalar.as_ref());
    }

    // Each encoding loads again, on both sides, as the same key.
    let public = ours.public_key();
    let point = public.as_ref();
    let pkcs8 = ours.to_pkcs8();
    let again = ours::EcdsaKeyPair::from_pkcs8(curve.ours, pkcs8.as_ref()).unwrap();
    assert_eq!(again.public_key().as_ref(), point);
    let theirs = theirs::EcdsaKeyPair::from_pkcs8(curve.theirs, pkcs8.as_ref()).unwrap();
    assert_eq!(theirs.public_key().as_ref(), point);
    assert_eq!(
        ours.to_spki().as_ref(),
        theirs.public_key().as_der().unwrap().as_ref()
    );
    let sec1 = ours.to_sec1();
    let again = ours::EcdsaKeyPair::from_sec1(curve.ours, sec1.as_ref()).unwrap();
    assert_eq!(again.public_key().as_ref(), point);
    assert_eq!(
        sec1.as_ref(),
        theirs.private_key().as_der().unwrap().as_ref()
    );

    // The scalar loads with the point uncompressed or compressed.
    let scalar = ours.to_scalar();
    let (x, y) = point[1..].split_at(point.len() / 2);
    let compressed = [&[0x02 | (y[y.len() - 1] & 1)][..], x].concat();
    for point in [point, &compressed] {
        ours::EcdsaKeyPair::from_scalar_and_public_key(curve.ours, scalar.as_ref(), point).unwrap();
        theirs::EcdsaKeyPair::from_private_key_and_public_key(curve.theirs, scalar.as_ref(), point)
            .unwrap();
    }
    ecdsa_public(curve, point);
    ecdsa_spki(curve, ours.to_spki().as_ref());
}

fn ecdsa_public(curve: &Curve, input: &[u8]) {
    let ours = ours::PublicKey::new(curve.ours_verify, input);
    let theirs = theirs::ParsedPublicKey::new(curve.theirs_verify, input);
    // rind takes only the uncompressed point here: no consumer sends another
    // form, and a compressed one would cost a square root.
    let compressed = matches!(input.first(), Some(2 | 3));
    let refused = compressed || hybrid(input) || spki(input);
    agree(&ours, &theirs, refused.into());
    let Ok(ours) = ours else {
        return;
    };
    assert_eq!(ours.as_ref(), input);
    let again = ours::PublicKey::new(curve.ours_verify, ours.as_ref()).unwrap();
    assert_eq!(again.as_ref(), input);
}

fn rsa_private(
    input: &[u8],
    ours: fn(&[u8]) -> Result<ours::RsaKeyPair, rind::Error>,
    theirs: fn(&[u8]) -> Result<their_rsa::KeyPair, aws_lc_rs::error::KeyRejected>,
    expect: Expect,
) {
    let (ours, theirs) = (ours(input), theirs(input));
    agree(&ours, &theirs, expect);
    let Ok(ours) = ours else {
        return;
    };
    let public = ours.public_key(&sign::RSA_PKCS1_SHA256);
    if let Ok(theirs) = &theirs {
        assert_eq!(public.as_ref(), theirs.public_key().as_ref());
    }

    let pkcs8 = ours.to_pkcs8();
    let again = ours::RsaKeyPair::from_pkcs8(pkcs8.as_ref()).unwrap();
    assert_eq!(
        again.public_key(&sign::RSA_PKCS1_SHA256).as_ref(),
        public.as_ref()
    );
    let theirs = their_rsa::KeyPair::from_pkcs8(pkcs8.as_ref()).unwrap();
    assert_eq!(theirs.public_key().as_ref(), public.as_ref());
    assert_eq!(
        ours.to_spki().as_ref(),
        theirs.public_key().as_der().unwrap().as_ref()
    );
    rsa_public(&RSA_2048, public.as_ref());
}

/// aws-lc-rs's key, if it takes `der` and its modulus is in `rsa`'s range.
///
/// aws-lc-rs checks the range only when it verifies, and rind as it loads the
/// key, so neither verifies with a key the other refuses.
fn their_rsa_public(rsa: &Rsa, der: &[u8]) -> Result<their_rsa::PublicKey, &'static str> {
    let key = their_rsa::PublicKey::from_der(der).map_err(|_| "refused")?;
    let modulus = key.modulus();
    let modulus = modulus.big_endian_without_leading_zero();
    let bits = modulus.len() * 8 - modulus.first().map_or(8, |b| b.leading_zeros() as usize);
    match (rsa.min_bits..=8192).contains(&bits) {
        true => Ok(key),
        false => Err("modulus out of range"),
    }
}

fn rsa_public(rsa: &Rsa, input: &[u8]) {
    let ours = ours::PublicKey::new(rsa.ours, input);
    let theirs = their_rsa_public(rsa, input);
    agree(
        &ours,
        &theirs,
        (spki_parameters(input) || trailing(input)).into(),
    );
    let Ok(ours) = ours else {
        return;
    };
    if let Ok(theirs) = &theirs {
        assert_eq!(ours.as_ref(), theirs.as_ref());
    }
    rsa_reencode(rsa, &ours);
}

fn rsa_components(rsa: &Rsa, input: &[u8]) {
    let Some((n, e)) = split(input) else {
        return;
    };
    let ours = ours::PublicKey::from_components(rsa.ours, &rind::rsa::PublicKeyComponents { n, e });
    // aws-lc-rs checks components only when it verifies, so their key is the
    // same components as DER. Both refuse an empty component or a leading
    // zero, which DER cannot carry.
    let theirs = match [n, e].iter().all(|x| x.first().is_some_and(|&b| b != 0)) {
        true => their_rsa_public(rsa, &rsa_public_key_der(n, e)),
        false => Err("leading zero"),
    };
    agree(&ours, &theirs, Expect::Agree);
    let Ok(ours) = ours else {
        return;
    };
    assert_eq!(ours.as_ref(), rsa_public_key_der(n, e));
    rsa_reencode(rsa, &ours);
}

/// `key`'s DER loads again on both sides, and as components on rind's.
fn rsa_reencode(rsa: &Rsa, key: &ours::PublicKey) {
    let again = ours::PublicKey::new(rsa.ours, key.as_ref()).unwrap();
    assert_eq!(again.as_ref(), key.as_ref());
    theirs::ParsedPublicKey::new(rsa.theirs, key.as_ref()).unwrap();

    let theirs = their_rsa::PublicKey::from_der(key.as_ref()).unwrap();
    let (n, e) = (theirs.modulus(), theirs.exponent());
    let components = rind::rsa::PublicKeyComponents {
        n: n.big_endian_without_leading_zero(),
        e: e.big_endian_without_leading_zero(),
    };
    let again = ours::PublicKey::from_components(rsa.ours, &components).unwrap();
    assert_eq!(again.as_ref(), key.as_ref());
}

/// The PKCS#1 `RSAPublicKey` for `n` and `e`, each without leading zeros.
fn rsa_public_key_der(n: &[u8], e: &[u8]) -> Vec<u8> {
    fn element(tag: u8, body: &[u8]) -> Vec<u8> {
        let mut out = vec![tag];
        match body.len() {
            len @ 0..=0x7f => out.push(len as u8),
            len => {
                let len = len.to_be_bytes();
                let len = &len[len.iter().position(|&b| b != 0).unwrap()..];
                out.push(0x80 | len.len() as u8);
                out.extend_from_slice(len);
            }
        }
        out.extend_from_slice(body);
        out
    }
    let integer = |x: &[u8]| match x[0] & 0x80 {
        0 => element(0x02, x),
        _ => element(0x02, &[&[0], x].concat()),
    };
    element(0x30, &[integer(n), integer(e)].concat())
}

fn ed25519_pkcs8(input: &[u8]) {
    let ours = ours::Ed25519KeyPair::from_pkcs8(input);
    let theirs = theirs::Ed25519KeyPair::from_pkcs8(input);
    let refused = trailing(input) || v2_without_public_key(input);
    agree_ed25519(ours, theirs, refused.into());
}

fn ed25519_seed(input: &[u8]) {
    let Some((seed, public)) = split(input) else {
        return;
    };
    let ours = ours::Ed25519KeyPair::from_seed_and_public_key(seed, public);
    let theirs = theirs::Ed25519KeyPair::from_seed_and_public_key(seed, public);
    agree_ed25519(ours, theirs, Expect::Agree);
}

fn agree_ed25519(
    ours: Result<ours::Ed25519KeyPair, rind::Error>,
    theirs: Result<theirs::Ed25519KeyPair, aws_lc_rs::error::KeyRejected>,
    expect: Expect,
) {
    agree(&ours, &theirs, expect);
    let Ok(ours) = ours else {
        return;
    };
    let public = ours.public_key();
    if let Ok(theirs) = &theirs {
        assert_eq!(public.as_ref(), theirs.public_key().as_ref());
        let seed = theirs.seed().unwrap();
        assert_eq!(
            ours.to_seed().as_ref(),
            seed.as_be_bytes().unwrap().as_ref()
        );
    }

    let pkcs8 = ours.to_pkcs8();
    let again = ours::Ed25519KeyPair::from_pkcs8(pkcs8.as_ref()).unwrap();
    assert_eq!(again.public_key().as_ref(), public.as_ref());
    let theirs = theirs::Ed25519KeyPair::from_pkcs8(pkcs8.as_ref()).unwrap();
    assert_eq!(theirs.public_key().as_ref(), public.as_ref());
    assert_eq!(
        ours.to_spki().as_ref(),
        theirs.public_key().as_der().unwrap().as_ref()
    );
    let pkcs8v1 = ours.to_pkcs8v1();
    assert_eq!(pkcs8v1.as_ref(), theirs.to_pkcs8v1().unwrap().as_ref());
    let again = ours::Ed25519KeyPair::from_pkcs8(pkcs8v1.as_ref()).unwrap();
    assert_eq!(again.public_key().as_ref(), public.as_ref());
    let seed = ours.to_seed();
    ours::Ed25519KeyPair::from_seed_and_public_key(seed.as_ref(), public.as_ref()).unwrap();
    let again = ours::Ed25519KeyPair::from_seed(seed.as_ref()).unwrap();
    assert_eq!(again.public_key().as_ref(), public.as_ref());
    ed25519_public(public.as_ref());
    ed25519_spki(ours.to_spki().as_ref());
}

fn ed25519_public(input: &[u8]) {
    let ours = ours::PublicKey::new(&verify::ED25519, input);
    let theirs = theirs::ParsedPublicKey::new(&theirs::ED25519, input);
    // aws-lc-rs takes a `SubjectPublicKeyInfo` for any length but 32, and
    // any 32 bytes, checking the point only when it verifies.
    let expect = match input.len() {
        32 => Expect::Stricter,
        _ => Expect::Refused,
    };
    agree(&ours, &theirs, expect);
    let Ok(ours) = ours else {
        return;
    };
    assert_eq!(ours.as_ref(), input);
    ours::PublicKey::new(&verify::ED25519, ours.as_ref()).unwrap();
}

fn ed25519_spki(input: &[u8]) {
    let ours = ours::PublicKey::from_spki(&verify::ED25519, input);
    let theirs = theirs::ParsedPublicKey::new(&theirs::ED25519, input);
    // aws-lc-rs takes any 32 bytes as a bare key, and checks the point only
    // when it verifies.
    let expect = match input.len() {
        32 => Expect::Refused,
        _ => Expect::Stricter,
    };
    agree(&ours, &theirs, expect);
    let Ok(ours) = ours else {
        return;
    };
    let spki = ours.to_spki();
    assert_eq!(spki.as_ref(), theirs.unwrap().as_der().unwrap().as_ref());
    let again = ours::PublicKey::from_spki(&verify::ED25519, spki.as_ref()).unwrap();
    assert_eq!(again.as_ref(), ours.as_ref());
    ed25519_public(ours.as_ref());
}

fn ecdsa_spki(curve: &Curve, input: &[u8]) {
    let ours = ours::PublicKey::from_spki(curve.ours_verify, input);
    let theirs = theirs::ParsedPublicKey::new(curve.theirs_verify, input);
    // aws-lc-rs takes a bare point here too, and a curve's explicit
    // parameters in place of its name.
    let refused = !spki(input)
        || trailing(input)
        || explicit_curve(input)
        || spki_point(input).is_some_and(hybrid);
    agree(&ours, &theirs, refused.into());
    let Ok(ours) = ours else {
        return;
    };

    // The point is aws-lc-rs's, uncompressed, and each encoding of it loads
    // again on both sides as the same key.
    same_peer(&curve.ecdh, ours.as_ref(), input);
    let again = ours::PublicKey::new(curve.ours_verify, ours.as_ref()).unwrap();
    assert_eq!(again.as_ref(), ours.as_ref());
    let spki = ours.to_spki();
    let again = ours::PublicKey::from_spki(curve.ours_verify, spki.as_ref()).unwrap();
    assert_eq!(again.as_ref(), ours.as_ref());
    let theirs = theirs::ParsedPublicKey::new(curve.theirs_verify, spki.as_ref()).unwrap();
    assert_eq!(theirs.as_der().unwrap().as_ref(), spki.as_ref());
}

fn rsa_spki(rsa: &Rsa, input: &[u8]) {
    let ours = ours::PublicKey::from_spki(rsa.ours, input);
    let theirs = their_rsa_public(rsa, input);
    // aws-lc-rs takes PKCS#1's `RSAPublicKey` here too.
    let refused = !spki(input) || spki_parameters(input) || trailing(input);
    agree(&ours, &theirs, refused.into());
    let Ok(ours) = ours else {
        return;
    };
    assert_eq!(ours.as_ref(), theirs.unwrap().as_ref());
    let spki = ours.to_spki();
    let again = ours::PublicKey::from_spki(rsa.ours, spki.as_ref()).unwrap();
    assert_eq!(again.as_ref(), ours.as_ref());
    rsa_reencode(rsa, &ours);
}

fn ecdh_public(ecdh: &Ecdh, input: &[u8]) {
    let ours = ours_ecdh::PublicKey::new(ecdh.ours, input);
    let theirs = their_ecdh_public(ecdh, input);
    // aws-lc-rs takes a `SubjectPublicKeyInfo` here too.
    let refused = theirs
        .as_ref()
        .is_ok_and(|key| matches!(key.format(), Format::X509 | Format::Hybrid));
    agree(&ours, &theirs, refused.into());
    let Ok(ours) = ours else {
        return;
    };
    if input.first() == Some(&4) || !ecdh.nist() {
        assert_eq!(ours.as_ref(), input);
    }
    ecdh_reencode(ecdh, &ours, input);
}

fn ecdh_spki(ecdh: &Ecdh, input: &[u8]) {
    let ours = ours_ecdh::PublicKey::from_spki(ecdh.ours, input);
    let theirs = their_ecdh_public(ecdh, input);
    // aws-lc-rs takes a bare point here too, and a curve's explicit
    // parameters in place of its name. rind takes WebCrypto's id-ecDH,
    // whatever aws-lc-rs makes of it.
    let refused = theirs
        .as_ref()
        .is_ok_and(|key| key.format() != Format::X509)
        || trailing(input)
        || explicit_curve(input)
        || ecdh.nist() && spki_point(input).is_some_and(hybrid);
    if !id_ecdh(input) {
        agree(&ours, &theirs, refused.into());
    }
    let Ok(ours) = ours else {
        return;
    };
    ecdh_reencode(ecdh, &ours, spki_point(input).unwrap());
}

/// aws-lc-rs's agreement key from `input`, which it takes as a
/// `SubjectPublicKeyInfo` or a bare point.
fn their_ecdh_public(
    ecdh: &Ecdh,
    input: &[u8],
) -> Result<theirs_ecdh::ParsedPublicKey, aws_lc_rs::error::KeyRejected> {
    theirs_ecdh::UnparsedPublicKey::new(ecdh.theirs, input).try_into()
}

/// `key`, which rind loaded from the bare point `point`, is aws-lc-rs's key
/// for the point, and each of its encodings loads again on both sides as
/// itself.
fn ecdh_reencode(ecdh: &Ecdh, key: &ours_ecdh::PublicKey, point: &[u8]) {
    same_peer(ecdh, key.as_ref(), point);
    let again = ours_ecdh::PublicKey::new(ecdh.ours, key.as_ref()).unwrap();
    assert_eq!(again.as_ref(), key.as_ref());
    let spki = key.to_spki();
    let again = ours_ecdh::PublicKey::from_spki(ecdh.ours, spki.as_ref()).unwrap();
    assert_eq!(again.as_ref(), key.as_ref());
    let theirs = their_ecdh_public(ecdh, spki.as_ref()).unwrap();
    assert!(theirs.format() == Format::X509);
}

/// Whether rind's key `ours` and aws-lc-rs's key from `theirs`, in any form
/// it takes, are the same key: each agrees on the same secret with a private
/// key of all 0x01 bytes, or both refuse.
fn same_peer(ecdh: &Ecdh, ours: &[u8], theirs: &[u8]) {
    let scalar = vec![1; ecdh.scalar_len];
    let ours = ours_ecdh::PrivateKey::from_scalar(ecdh.ours, &scalar)
        .unwrap()
        .agree(ours);
    let private = theirs_ecdh::PrivateKey::from_private_key(ecdh.theirs, &scalar).unwrap();
    let peer = theirs_ecdh::UnparsedPublicKey::new(ecdh.theirs, theirs);
    let theirs = theirs_ecdh::agree(&private, peer, "refused", |secret| Ok(secret.to_vec()));
    agree(&ours, &theirs, Expect::Agree);
    if let (Ok(ours), Ok(theirs)) = (ours, theirs) {
        assert_eq!(ours.as_ref(), theirs);
    }
}

/// The point in the `SubjectPublicKeyInfo` `input`.
fn spki_point(input: &[u8]) -> Option<&[u8]> {
    let (tag, bits) = elements(sequence(input)?).nth(1)?;
    (tag == 0x03).then_some(bits)?.strip_prefix(&[0])
}

/// The object identifier and parameters of the `SubjectPublicKeyInfo`
/// `input`'s algorithm.
fn spki_algorithm(input: &[u8]) -> Option<(&[u8], &[u8])> {
    let (tag, oid, parameters) = element(sequence(sequence(input)?)?)?;
    (tag == 0x06).then_some((oid, parameters))
}

/// Whether the `SubjectPublicKeyInfo` `input` gives its curve's parameters
/// in place of its name, which aws-lc-rs takes for a curve it knows.
fn explicit_curve(input: &[u8]) -> bool {
    spki_algorithm(input).is_some_and(|(_, parameters)| parameters.first() == Some(&0x30))
}

/// Whether the `SubjectPublicKeyInfo` `input` names id-ecDH, which WebCrypto
/// takes for an ECDH key.
fn id_ecdh(input: &[u8]) -> bool {
    spki_algorithm(input).is_some_and(|(oid, _)| oid == [0x2b, 0x81, 0x04, 0x01, 0x0c])
}

fn mlkem_public(input: &[u8]) {
    let ours = our_kem::EncapsulationKey::new(&our_kem::ML_KEM_768, input);
    // aws-lc-rs checks the modulus only when it encapsulates.
    let theirs = their_kem::EncapsulationKey::new(&their_kem::ML_KEM_768, input)
        .map_err(|_| "refused")
        .and_then(|key| key.encapsulate().map(|_| key).map_err(|_| "modulus"));
    agree(&ours, &theirs, Expect::Agree);
    let Ok(ours) = ours else {
        return;
    };
    assert_eq!(ours.as_ref(), input);
    let theirs = theirs.unwrap();
    assert_eq!(theirs.key_bytes().unwrap().as_ref(), input);
}

fn ml_dsa_pkcs8<P: sign::MlDsaParameterSet>(set: &MlDsa, input: &[u8]) {
    let ours = sign::MlDsaKeyPair::<P>::from_pkcs8(input);
    let theirs = theirs::PqdsaKeyPair::from_pkcs8(set.theirs, input);
    // aws-lc ignores what rind refuses: bytes after the document or after
    // its private key's CHOICE, a version 2 document's public key, and a
    // `both` key whose expanded form differs from its seed's in `K`, which
    // the public keys aws-lc compares leave out.
    agree(&ours, &theirs, Expect::Stricter);
    agree_ml_dsa(set, ours, theirs.ok());
}

fn ml_dsa_seed<P: sign::MlDsaParameterSet>(set: &MlDsa, input: &[u8]) {
    let ours = sign::MlDsaKeyPair::<P>::from_seed(input);
    let theirs = theirs::PqdsaKeyPair::from_seed(set.theirs, input);
    agree(&ours, &theirs, Expect::Agree);
    agree_ml_dsa(set, ours, theirs.ok());
}

/// A key pair rind loaded matches aws-lc-rs's, re-encodes to a document both
/// load as the same key, and signs as aws-lc-rs verifies, and the reverse.
fn agree_ml_dsa<P: sign::MlDsaParameterSet>(
    set: &MlDsa,
    ours: Result<sign::MlDsaKeyPair<P>, rind::Error>,
    theirs: Option<theirs::PqdsaKeyPair>,
) {
    let Ok(ours) = ours else {
        return;
    };
    let public = ours.public_key();
    if let Some(theirs) = &theirs {
        assert_eq!(public.as_ref(), theirs.public_key().as_ref());
    }

    let pkcs8 = ours.to_pkcs8();
    let again = sign::MlDsaKeyPair::<P>::from_pkcs8(pkcs8.as_ref()).unwrap();
    assert_eq!(again.public_key().as_ref(), public.as_ref());
    let theirs = theirs::PqdsaKeyPair::from_pkcs8(set.theirs, pkcs8.as_ref()).unwrap();
    assert_eq!(theirs.public_key().as_ref(), public.as_ref());
    if let Some(seed) = ours.to_seed() {
        let again = sign::MlDsaKeyPair::<P>::from_seed(seed.as_ref()).unwrap();
        assert_eq!(again.public_key().as_ref(), public.as_ref());
    }

    let message = b"rind";
    let signature = ours.sign(message).unwrap();
    theirs::UnparsedPublicKey::new(set.theirs_verify, public.as_ref())
        .verify(message, signature.as_ref())
        .unwrap();
    let mut signature = [0; 4627];
    let len = theirs.sign(message, &mut signature).unwrap();
    public.verify(message, &signature[..len]).unwrap();

    ml_dsa_public(set, public.as_ref());
    ml_dsa_spki(set, public.to_spki().as_ref());
}

fn ml_dsa_public(set: &MlDsa, input: &[u8]) {
    let ours = ours::PublicKey::new(set.ours, input);
    let theirs = theirs::ParsedPublicKey::new(set.theirs_verify, input);
    // aws-lc-rs also takes a `SubjectPublicKeyInfo`; any bytes of the raw
    // key's length are one.
    let expect = match input.len() == set.public_key_len {
        true => Expect::Agree,
        false => Expect::Refused,
    };
    agree(&ours, &theirs, expect);
    let Ok(ours) = ours else {
        return;
    };
    assert_eq!(ours.as_ref(), input);
    let spki = ours.to_spki();
    assert_eq!(spki.as_ref(), theirs.unwrap().as_der().unwrap().as_ref());
}

fn ml_dsa_spki(set: &MlDsa, input: &[u8]) {
    let ours = ours::PublicKey::from_spki(set.ours, input);
    let theirs = theirs::ParsedPublicKey::new(set.theirs_verify, input);
    // aws-lc-rs also takes the raw key.
    let expect = match input.len() == set.public_key_len {
        true => Expect::Refused,
        false => Expect::Stricter,
    };
    agree(&ours, &theirs, expect);
    let Ok(ours) = ours else {
        return;
    };
    let spki = ours.to_spki();
    assert_eq!(spki.as_ref(), theirs.unwrap().as_der().unwrap().as_ref());
    let again = ours::PublicKey::from_spki(set.ours, spki.as_ref()).unwrap();
    assert_eq!(again.as_ref(), ours.as_ref());
    ml_dsa_public(set, ours.as_ref());
}

/// ECVRF keys. aws-lc-rs has none, so Edwards is checked against akd_core and
/// P-256 against vrf-rfc9381. rind may refuse a non-canonical Edwards point
/// or an uncompressed P-256 point the reference takes, and must not take a
/// key the reference refuses.
fn vrf_edwards_seed(input: &[u8]) {
    use akd_core::ecvrf::{VRFPrivateKey, VRFPublicKey};
    use rind::vrf::{ECVRF_EDWARDS25519_SHA512_TAI, PublicKey, SecretKey};

    let ours = SecretKey::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, input);
    let theirs = VRFPrivateKey::try_from(input);
    assert_eq!(ours.is_ok(), theirs.is_ok(), "edwards seed");
    let (Ok(ours), Ok(theirs)) = (ours, theirs) else {
        return;
    };
    assert_eq!(ours.to_bytes().as_slice(), input);
    let public = ours.public_key();
    let theirs = VRFPublicKey::from(&theirs);
    assert_eq!(public.as_ref(), theirs.as_bytes().as_slice());
    PublicKey::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, public.as_ref()).unwrap();
}

fn vrf_edwards_public(input: &[u8]) {
    use akd_core::ecvrf::VRFPublicKey;
    use rind::vrf::{ECVRF_EDWARDS25519_SHA512_TAI, PublicKey};

    let ours = PublicKey::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, input);
    let theirs = VRFPublicKey::try_from(input);
    // akd_core decompresses and accepts a non-canonical `y` or a sign bit on
    // `x = 0`. rind rejects those. It must not accept a key akd rejects.
    assert!(
        ours.is_err() || theirs.is_ok(),
        "rind loaded an Edwards public key akd_core refused: {:?}",
        theirs.as_ref().err()
    );
    let Ok(ours) = ours else {
        return;
    };
    assert_eq!(ours.as_ref(), input);
}

fn vrf_p256_seed(input: &[u8]) {
    use rind::vrf::{ECVRF_P256_SHA256_TAI, SecretKey};
    use vrf_rfc9381::Prover as _;
    use vrf_rfc9381::ec::p256::tai::EcVrfP256TaiSecretKey;

    let ours = SecretKey::from_bytes(&ECVRF_P256_SHA256_TAI, input);
    let theirs = EcVrfP256TaiSecretKey::from_slice(input);
    assert_eq!(
        ours.is_ok(),
        theirs.is_ok(),
        "p256 seed: rind {:?}, vrf-rfc9381 {:?}",
        ours.as_ref().err(),
        theirs.as_ref().err()
    );
    let Ok(ours) = ours else {
        return;
    };
    assert_eq!(ours.to_bytes().as_slice(), input);
    // Loading agrees, and the reference can derive a verifier from it.
    let _ = theirs.unwrap().verifier();
}

fn vrf_p256_public(input: &[u8]) {
    use rind::vrf::{ECVRF_P256_SHA256_TAI, PublicKey};
    use vrf_rfc9381::Verifier as _;
    use vrf_rfc9381::ec::p256::tai::EcVrfP256TaiPublicKey;

    let ours = PublicKey::from_bytes(&ECVRF_P256_SHA256_TAI, input);
    let theirs = EcVrfP256TaiPublicKey::from_slice(input);
    assert!(
        ours.is_err() || theirs.is_ok(),
        "rind loaded a P-256 public key vrf-rfc9381 refused"
    );
    let Ok(ours) = ours else {
        return;
    };
    assert_eq!(ours.as_ref(), input);
}
