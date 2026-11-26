//! Whether aws-lc's decoders accept an EC, DSA, or DH key that rind does not
//! load itself: one on a curve rind cannot back, one whose curve is given by
//! explicit parameters, or a DSA or DH key. aws-lc-rs refuses a key of
//! another type as `WrongAlgorithm` when its decoder parses it and as
//! `InvalidEncoding` when it does not (`parse_rfc5280_public_key` and
//! `parse_rfc5208_private_key` in aws-lc-rs 1.19.0 `aws-lc-rs/src/evp_pkey.rs`),
//! so these follow the decoders in aws-lc's `crypto/evp_extra` and what they
//! call.
//!
//! Everything read here is public and checked in variable time, except a
//! private key's scalar or DSA `x`, which is compared with its bound without
//! a branch or memory index on its bytes and only the result made public.

use alloc::vec::Vec;
use core::cmp::Ordering;

use crate::der;

const INTEGER: u8 = 0x02;
const BIT_STRING: u8 = 0x03;
const OCTET_STRING: u8 = 0x04;
const OBJECT_IDENTIFIER: u8 = 0x06;
const SEQUENCE: u8 = 0x30;

/// X9.62 `prime-field`, 1.2.840.10045.1.1.
const PRIME_FIELD: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x01, 0x01];

/// aws-lc's `OPENSSL_DSA_MAX_MODULUS_BITS` and `OPENSSL_DH_MAX_MODULUS_BITS`.
const MAX_MODULUS_BITS: usize = 10_000;

/// A curve aws-lc builds in.
pub(crate) struct Curve {
    /// Its name's object identifier's contents.
    pub(crate) oid: &'static [u8],
    /// Its explicit `ECParameters`, as OpenSSL encodes them.
    parameters: &'static [u8],
}

/// aws-lc's built-in curves, in the order `kAllGroups` (`crypto/ec_extra/ec_asn1.c`)
/// lists them.
static CURVES: [Curve; 10] = [
    Curve {
        oid: &[0x2b, 0x81, 0x04, 0x00, 0x21],
        parameters: include_bytes!("evp/p224.der"),
    },
    Curve {
        oid: &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07],
        parameters: include_bytes!("evp/p256.der"),
    },
    Curve {
        oid: &[0x2b, 0x81, 0x04, 0x00, 0x22],
        parameters: include_bytes!("evp/p384.der"),
    },
    Curve {
        oid: &[0x2b, 0x81, 0x04, 0x00, 0x23],
        parameters: include_bytes!("evp/p521.der"),
    },
    Curve {
        oid: &[0x2b, 0x81, 0x04, 0x00, 0x0a],
        parameters: include_bytes!("evp/secp256k1.der"),
    },
    Curve {
        oid: &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x05],
        parameters: include_bytes!("evp/brainpool_p224r1.der"),
    },
    Curve {
        oid: &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x07],
        parameters: include_bytes!("evp/brainpool_p256r1.der"),
    },
    Curve {
        oid: &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x09],
        parameters: include_bytes!("evp/brainpool_p320r1.der"),
    },
    Curve {
        oid: &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x0b],
        parameters: include_bytes!("evp/brainpool_p384r1.der"),
    },
    Curve {
        oid: &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x0d],
        parameters: include_bytes!("evp/brainpool_p512r1.der"),
    },
];

/// An unsigned INTEGER's magnitude, without leading zeros (empty for zero),
/// and the bytes after it, refusing a negative or non-minimal encoding as
/// `CBS_is_unsigned_asn1_integer` does.
fn unsigned(der: &[u8]) -> Option<(&[u8], &[u8])> {
    let (INTEGER, value, rest) = der::split(der)? else {
        return None;
    };
    let magnitude = match value {
        [] | [0x80..=0xff, ..] | [0, 0..=0x7f, ..] => return None,
        [0, rest @ ..] => rest,
        _ => value,
    };
    Some((magnitude, rest))
}

/// `bytes` without its leading zeros.
fn strip(bytes: &[u8]) -> &[u8] {
    let zeros = bytes.iter().take_while(|byte| **byte == 0).count();
    &bytes[zeros..]
}

/// Compares two magnitudes without leading zeros.
fn cmp(a: &[u8], b: &[u8]) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| a.cmp(b))
}

fn odd(magnitude: &[u8]) -> bool {
    magnitude.last().is_some_and(|byte| byte & 1 == 1)
}

/// Prime-curve parameters, each field a big-endian value that may carry
/// leading zeros.
struct Domain<'a> {
    p: &'a [u8],
    a: &'a [u8],
    b: &'a [u8],
    x: &'a [u8],
    y: &'a [u8],
    order: &'a [u8],
}

impl Domain<'_> {
    /// Whether every field equals `other`'s as a number, as
    /// `integers_equal` compares them; the seed is ignored.
    fn same(&self, other: &Domain<'_>) -> bool {
        [
            (self.p, other.p),
            (self.a, other.a),
            (self.b, other.b),
            (self.x, other.x),
            (self.y, other.y),
            (self.order, other.order),
        ]
        .into_iter()
        .all(|(a, b)| strip(a) == strip(b))
    }
}

/// Explicit prime-curve parameters and the bytes after them, as
/// `parse_explicit_prime_curve` (`crypto/ec_extra/ec_asn1.c`) reads them: a
/// cofactor, if present, of one, and an uncompressed base point.
fn explicit(der: &[u8]) -> Option<(Domain<'_>, &[u8])> {
    let (SEQUENCE, body, after) = der::split(der)? else {
        return None;
    };
    let ([1], body) = unsigned(body)? else {
        return None;
    };
    let (SEQUENCE, field, body) = der::split(body)? else {
        return None;
    };
    let (OBJECT_IDENTIFIER, PRIME_FIELD, field) = der::split(field)? else {
        return None;
    };
    let (p, []) = unsigned(field)? else {
        return None;
    };
    let (SEQUENCE, curve, body) = der::split(body)? else {
        return None;
    };
    let (OCTET_STRING, a, curve) = der::split(curve)? else {
        return None;
    };
    let (OCTET_STRING, b, mut curve) = der::split(curve)? else {
        return None;
    };
    if curve.first() == Some(&BIT_STRING) {
        curve = der::split(curve)?.2;
    }
    let (OCTET_STRING, base, body) = der::split(body)? else {
        return None;
    };
    let (order, mut body) = unsigned(body)?;
    if body.first() == Some(&INTEGER) {
        let (_, [1], rest) = der::split(body)? else {
            return None;
        };
        body = rest;
    }
    let [0x04, coordinates @ ..] = base else {
        return None;
    };
    if !curve.is_empty() || !body.is_empty() || coordinates.len() % 2 != 0 {
        return None;
    }
    let (x, y) = coordinates.split_at(coordinates.len() / 2);
    Some((
        Domain {
            p,
            a,
            b,
            x,
            y,
            order,
        },
        after,
    ))
}

impl Curve {
    fn domain(&self) -> Domain<'static> {
        explicit(self.parameters)
            .expect("built-in parameters parse")
            .0
    }

    /// The curve's order, big-endian.
    pub(crate) fn order(&self) -> &'static [u8] {
        self.domain().order
    }

    /// Whether `encoded` is a point on the curve other than infinity, as
    /// `EC_POINT_oct2point` (`crypto/fipsmodule/ec/oct.c`) decodes it:
    /// uncompressed, compressed, or hybrid with a matching parity bit. aws-lc
    /// decodes infinity too, then refuses it as a key in
    /// `EC_KEY_set_public_key` and `EC_KEY_check_key`.
    pub(crate) fn has_point(&self, encoded: &[u8]) -> bool {
        let domain = self.domain();
        let len = domain.p.len();
        let field = Field::new(&domain);
        match encoded {
            [form @ (0x04 | 0x06 | 0x07), coordinates @ ..] if coordinates.len() == 2 * len => {
                let (x, y) = coordinates.split_at(len);
                (*form == 0x04 || form & 1 == y[len - 1] & 1) && field.on_curve(x, y)
            }
            [0x02 | 0x03, x @ ..] if x.len() == len => field.has_x(x),
            _ => false,
        }
    }
}

/// The curve `parameters` name, or match field by field when explicit, and
/// the bytes after them, as `EC_KEY_parse_parameters_and_type` reads them.
pub(crate) fn ec_group(parameters: &[u8]) -> Option<(&'static Curve, &[u8])> {
    match der::split(parameters)? {
        (OBJECT_IDENTIFIER, oid, rest) => Some((CURVES.iter().find(|c| c.oid == oid)?, rest)),
        (SEQUENCE, ..) => {
            let (domain, rest) = explicit(parameters)?;
            // The order alone picks the candidate; the rest must then match.
            let curve = CURVES
                .iter()
                .find(|c| strip(c.domain().order) == strip(domain.order))?;
            curve.domain().same(&domain).then_some((curve, rest))
        }
        _ => None,
    }
}

/// `eckey_pub_decode`: parameters naming a built-in curve, by name or
/// explicitly, and nothing after them, then a point on that curve.
pub(crate) fn ec_public_key(parameters: &[u8], key: &[u8]) -> bool {
    ec_group(parameters).is_some_and(|(curve, rest)| rest.is_empty() && curve.has_point(key))
}

/// An RFC 5915 `ECPrivateKey`'s fields.
pub(crate) struct Sec1<'a> {
    /// The private key's bytes, secret.
    pub(crate) scalar: &'a [u8],
    /// The contents of `[0]`, if present.
    pub(crate) parameters: Option<&'a [u8]>,
    /// The encoded point in `[1]`, if present.
    pub(crate) public_key: Option<&'a [u8]>,
}

/// Splits an `ECPrivateKey` filling all of `der`, framed as
/// `EC_KEY_parse_private_key` reads it, without reading the scalar's bytes.
pub(crate) fn sec1(der: &[u8]) -> Option<Sec1<'_>> {
    let (SEQUENCE, body, []) = der::split(der)? else {
        return None;
    };
    let ([1], body) = unsigned(body)? else {
        return None;
    };
    let (OCTET_STRING, scalar, mut body) = der::split(body)? else {
        return None;
    };
    let mut parameters = None;
    if let Some((0xa0, inner, rest)) = der::split(body) {
        parameters = Some(inner);
        body = rest;
    }
    let mut public_key = None;
    if let Some((0xa1, inner, rest)) = der::split(body) {
        let (BIT_STRING, [0, point @ ..], []) = der::split(inner)? else {
            return None;
        };
        if point.is_empty() {
            return None;
        }
        public_key = Some(point);
        body = rest;
    }
    body.is_empty().then_some(Sec1 {
        scalar,
        parameters,
        public_key,
    })
}

/// `EC_KEY_parse_private_key` for a curve rind cannot back, given its
/// already split `ECPrivateKey`: a public key on the curve, if present, and
/// a scalar that is nonzero and below the order. aws-lc also checks that the
/// public key is the scalar's; rind has no constant-time arithmetic on these
/// curves to compute it, so that check is left out.
pub(crate) fn unbacked_ec_private_key(curve: &Curve, key: &Sec1<'_>) -> bool {
    key.public_key.is_none_or(|point| curve.has_point(point))
        && declassify(below(key.scalar, curve.order()))
}

/// `DSA_parse_parameters`, its `dsa_check_key` (`crypto/dsa/dsa_asn1.c`),
/// and nothing after the parameters: q, which it returns, of 160, 224, or
/// 256 bits, odd and below an odd p of at most 10,000 bits, and g in 1..p.
fn dsa_parameters(parameters: &[u8]) -> Option<&[u8]> {
    let (SEQUENCE, body, []) = der::split(parameters)? else {
        return None;
    };
    let (p, body) = unsigned(body)?;
    let (q, body) = unsigned(body)?;
    let (g, []) = unsigned(body)? else {
        return None;
    };
    let ok = odd(p)
        && odd(q)
        && cmp(q, p) == Ordering::Less
        && !g.is_empty()
        && cmp(g, p) == Ordering::Less
        && matches!(der::bits(q), 160 | 224 | 256)
        && der::bits(p) <= MAX_MODULUS_BITS;
    ok.then_some(q)
}

/// `dsa_pub_decode`: parameters, then an unsigned INTEGER, which is not
/// range-checked.
pub(crate) fn dsa_public_key(parameters: &[u8], key: &[u8]) -> bool {
    dsa_parameters(parameters).is_some() && matches!(unsigned(key), Some((_, [])))
}

/// `dsa_priv_decode`: parameters, then a private key `x` of one INTEGER
/// that `dsa_check_key` bounds to 1..q. `x` is secret: its encoding is
/// checked without a branch on its bytes.
pub(crate) fn dsa_private_key(parameters: &[u8], key: &[u8]) -> bool {
    let Some(q) = dsa_parameters(parameters) else {
        return false;
    };
    let Some((INTEGER, x, [])) = der::split(key) else {
        return false;
    };
    let Some(&first) = x.first() else {
        return false;
    };
    // Minimal and non-negative, as `CBS_is_valid_asn1_integer` requires.
    let negative = first >> 7;
    let padded = match x.get(1) {
        Some(&second) => is_zero(first) & (1 ^ (second >> 7)),
        None => 0,
    };
    declassify((1 ^ negative) & (1 ^ padded) & below(x, q))
}

/// `dh_pub_decode` (`crypto/evp_extra/p_dh_asn1.c`): `DH_parse_parameters`,
/// which reads p, g, and an optional private-value length of at most 32
/// bits, and ignores bytes after them; `dh_check_params_fast`, an odd p of
/// at most 10,000 bits and g in 1..p; then an unsigned INTEGER in 2..p-1.
pub(crate) fn dh_public_key(parameters: &[u8], key: &[u8]) -> bool {
    let Some((SEQUENCE, body, _)) = der::split(parameters) else {
        return false;
    };
    let Some((p, body)) = unsigned(body) else {
        return false;
    };
    let Some((g, mut body)) = unsigned(body) else {
        return false;
    };
    if !body.is_empty() {
        let Some((length, [])) = unsigned(body) else {
            return false;
        };
        if length.len() > 4 {
            return false;
        }
        body = &[];
    }
    let Some((y, [])) = unsigned(key) else {
        return false;
    };
    // p is odd, so p - 1 only clears its lowest bit.
    let mut p_minus_one = p.to_vec();
    if let Some(last) = p_minus_one.last_mut() {
        *last &= !1;
    }
    body.is_empty()
        && odd(p)
        && der::bits(p) <= MAX_MODULUS_BITS
        && !g.is_empty()
        && cmp(g, p) == Ordering::Less
        && cmp(y, &[1]) == Ordering::Greater
        && cmp(y, strip(&p_minus_one)) == Ordering::Less
}

/// 1 if `byte` is zero, else 0, without a branch.
fn is_zero(byte: u8) -> u8 {
    // `wrapping_add`, since an overflow check would branch on `byte`.
    1 ^ (u16::from(byte).wrapping_add(0xff) >> 8) as u8
}

/// 1 if `value`, big-endian of any length, is nonzero and below `bound`,
/// else 0. Only the lengths pick what is read; no branch or index depends on
/// `value`'s bytes.
fn below(value: &[u8], bound: &[u8]) -> u8 {
    let byte = |bytes: &[u8], i: usize| bytes.len().checked_sub(i + 1).map_or(0, |at| bytes[at]);
    let mut borrow = 0u8;
    let mut any = 0u8;
    for i in 0..value.len().max(bound.len()) {
        let v = byte(value, i);
        let diff = u16::from(v)
            .wrapping_sub(u16::from(byte(bound, i)))
            .wrapping_sub(u16::from(borrow));
        borrow = (diff >> 8) as u8 & 1;
        any |= v;
    }
    borrow & (1 ^ is_zero(any))
}

/// Makes a secret 0-or-1 flag public, through rind's constant-time
/// comparison, which declassifies only its result.
fn declassify(flag: u8) -> bool {
    rind::constant_time::verify(&[flag], &[1]).is_ok()
}

/// Limbs enough for P-521's field, the largest built-in one.
const LIMBS: usize = 9;

type Num = [u64; LIMBS];

/// A big-endian value of at most `8 * LIMBS` significant bytes.
fn num(bytes: &[u8]) -> Option<Num> {
    let bytes = strip(bytes);
    if bytes.len() > 8 * LIMBS {
        return None;
    }
    let mut out = [0; LIMBS];
    for (i, byte) in bytes.iter().rev().enumerate() {
        out[i / 8] |= u64::from(*byte) << (8 * (i % 8));
    }
    Some(out)
}

fn less(a: &Num, b: &Num) -> bool {
    a.iter().rev().lt(b.iter().rev())
}

/// `a -= b`, wrapping.
fn sub(a: &mut Num, b: &Num) {
    let mut borrow = false;
    for (a, b) in a.iter_mut().zip(b) {
        let (d, b1) = a.overflowing_sub(*b);
        let (d, b2) = d.overflowing_sub(u64::from(borrow));
        *a = d;
        borrow = b1 | b2;
    }
}

/// Arithmetic modulo a built-in curve's odd prime, on public values, in
/// Montgomery form with R = 2^(64 * LIMBS). Multiplication is CIOS (Koç,
/// Acar, and Kaliski, "Analyzing and Comparing Montgomery Multiplication
/// Algorithms", 1996); the differential tests against aws-lc check it.
struct Field {
    p: Num,
    /// -p^-1 mod 2^64.
    inv: u64,
    /// R mod p, one in Montgomery form.
    one: Num,
    /// R^2 mod p.
    r2: Num,
    a: Num,
    b: Num,
}

impl Field {
    fn new(domain: &Domain<'_>) -> Self {
        let p = num(domain.p).expect("built-in prime fits");
        // Newton's iteration doubles the correct low bits of p^-1 each step.
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p[0].wrapping_mul(inv)));
        }
        let mut field = Self {
            p,
            inv: inv.wrapping_neg(),
            one: [0; LIMBS],
            r2: [0; LIMBS],
            a: [0; LIMBS],
            b: [0; LIMBS],
        };
        let mut r = [0; LIMBS];
        r[0] = 1;
        for _ in 0..64 * LIMBS {
            r = field.add(&r, &r);
        }
        field.one = r;
        for _ in 0..64 * LIMBS {
            r = field.add(&r, &r);
        }
        field.r2 = r;
        field.a = field.to(&num(domain.a).expect("built-in a fits"));
        field.b = field.to(&num(domain.b).expect("built-in b fits"));
        field
    }

    /// `a + b mod p`, for `a` and `b` below p.
    fn add(&self, a: &Num, b: &Num) -> Num {
        let mut out = [0; LIMBS];
        let mut carry = false;
        for ((out, a), b) in out.iter_mut().zip(a).zip(b) {
            let (s, c1) = a.overflowing_add(*b);
            let (s, c2) = s.overflowing_add(u64::from(carry));
            *out = s;
            carry = c1 | c2;
        }
        if carry || !less(&out, &self.p) {
            sub(&mut out, &self.p);
        }
        out
    }

    /// `a * b / R mod p`, for `a` and `b` below p.
    fn mul(&self, a: &Num, b: &Num) -> Num {
        let mut t = [0u64; LIMBS + 2];
        for b in b {
            let mut c = 0u128;
            for (t, a) in t.iter_mut().zip(a) {
                let s = u128::from(*t) + u128::from(*a) * u128::from(*b) + c;
                *t = s as u64;
                c = s >> 64;
            }
            let s = u128::from(t[LIMBS]) + c;
            t[LIMBS] = s as u64;
            t[LIMBS + 1] = (s >> 64) as u64;
            let m = t[0].wrapping_mul(self.inv);
            let mut c = (u128::from(t[0]) + u128::from(m) * u128::from(self.p[0])) >> 64;
            for j in 1..LIMBS {
                let s = u128::from(t[j]) + u128::from(m) * u128::from(self.p[j]) + c;
                t[j - 1] = s as u64;
                c = s >> 64;
            }
            let s = u128::from(t[LIMBS]) + c;
            t[LIMBS - 1] = s as u64;
            t[LIMBS] = t[LIMBS + 1] + (s >> 64) as u64;
        }
        let mut out: Num = t[..LIMBS].try_into().expect("LIMBS limbs");
        if t[LIMBS] != 0 || !less(&out, &self.p) {
            sub(&mut out, &self.p);
        }
        out
    }

    /// `a` in Montgomery form.
    fn to(&self, a: &Num) -> Num {
        self.mul(a, &self.r2)
    }

    /// A coordinate of the field's length, in Montgomery form, if below p.
    fn element(&self, bytes: &[u8]) -> Option<Num> {
        let value = num(bytes)?;
        less(&value, &self.p).then(|| self.to(&value))
    }

    /// `x^3 + a x + b`, in Montgomery form.
    fn rhs(&self, x: &Num) -> Num {
        let x3 = self.mul(&self.mul(x, x), x);
        self.add(&self.add(&x3, &self.mul(&self.a, x)), &self.b)
    }

    /// Whether `(x, y)` satisfies `y^2 = x^3 + a x + b`, both below p.
    fn on_curve(&self, x: &[u8], y: &[u8]) -> bool {
        match (self.element(x), self.element(y)) {
            (Some(x), Some(y)) => self.mul(&y, &y) == self.rhs(&x),
            _ => false,
        }
    }

    /// Whether some point has x-coordinate `x`: `x^3 + a x + b` is a square,
    /// by Euler's criterion. It is never zero, since these curves have prime
    /// order and so no point of order two, so either root's parity is there.
    fn has_x(&self, x: &[u8]) -> bool {
        let Some(x) = self.element(x) else {
            return false;
        };
        let mut exponent = self.p;
        exponent[0] -= 1;
        let mut power = self.one;
        let rhs = self.rhs(&x);
        for bit in (0..64 * LIMBS).rev() {
            power = self.mul(&power, &power);
            // (p - 1) / 2: bit i of it is bit i + 1 of p - 1.
            let i = bit + 1;
            if i < 64 * LIMBS && (exponent[i / 64] >> (i % 64)) & 1 == 1 {
                power = self.mul(&power, &rhs);
            }
        }
        power == self.one
    }
}

/// A PKCS#8 document rind can load for `curve`, from the parts of one aws-lc
/// takes that rind's parser does not: the curve given by explicit
/// parameters, outside the `ECPrivateKey` or in its `[0]`, or a public key in
/// hybrid form, which becomes uncompressed. `None` if there is none of those,
/// or the hybrid point is not on the curve.
pub(crate) fn canonical_ec_pkcs8(
    curve: &Curve,
    parameters: &[u8],
    key: &Sec1<'_>,
) -> Option<Vec<u8>> {
    let explicit = |parameters: &[u8]| parameters.first() == Some(&SEQUENCE);
    let hybrid = key
        .public_key
        .is_some_and(|point| matches!(point.first(), Some(0x06 | 0x07)));
    if !(explicit(parameters) || key.parameters.is_some_and(explicit) || hybrid) {
        return None;
    }
    let named = tlv(OBJECT_IDENTIFIER, curve.oid);
    let mut sec1 = alloc::vec![INTEGER, 1, 1];
    sec1.extend(tlv(OCTET_STRING, key.scalar));
    if key.parameters.is_some() {
        sec1.extend(tlv(0xa0, &named));
    }
    if let Some(point) = key.public_key {
        if hybrid && !curve.has_point(point) {
            return None;
        }
        let mut bits = alloc::vec![0];
        bits.extend_from_slice(point);
        if hybrid {
            bits[1] = 0x04;
        }
        sec1.extend(tlv(0xa1, &tlv(BIT_STRING, &bits)));
    }
    let mut algorithm = tlv(
        OBJECT_IDENTIFIER,
        &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01],
    );
    algorithm.extend(named);
    let mut body = alloc::vec![INTEGER, 1, 0];
    body.extend(tlv(SEQUENCE, &algorithm));
    body.extend(tlv(OCTET_STRING, &tlv(SEQUENCE, &sec1)));
    Some(tlv(SEQUENCE, &body))
}

/// A DER element; every EC key fits a two-byte length.
fn tlv(tag: u8, body: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(body.len() + 4);
    out.push(tag);
    match body.len() {
        len @ 0..=0x7f => out.push(len as u8),
        len @ 0x80..=0xff => out.extend([0x81, len as u8]),
        len => out.extend([0x82, (len >> 8) as u8, len as u8]),
    }
    out.extend_from_slice(body);
    out
}
