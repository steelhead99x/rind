// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Textbook elliptic-curve arithmetic over `num-bigint`, written from the
//! standards and the Explicit-Formulas Database: double-and-add in
//! projective coordinates, and affine points between. It
//! shares no code with rind or with any crate covering these curves, so the
//! differential tests take it as the independent oracle where every such
//! crate runs what rind runs: fiat-crypto's NIST field arithmetic and
//! curve25519-dalek on armv7 and the portable backend, and HACL*'s SHA-512
//! under Ed25519 on the portable backend. It hashes with RustCrypto's
//! `sha2`. It is slow, not constant time, and refuses nothing but what the
//! standards refuse.
//!
//! `rind`'s unit tests, `tests/crosschecks.rs`, and the fuzz targets include
//! this file, so it names nothing in any of them.

#![allow(dead_code, reason = "each crate that includes it uses part of it")]

use num_bigint::BigUint;
use sha2::Digest;

fn hex(s: &str) -> BigUint {
    BigUint::parse_bytes(s.as_bytes(), 16).unwrap()
}

fn dec(s: &str) -> BigUint {
    BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
}

/// `x` as `len` big-endian bytes.
pub(crate) fn be_bytes(x: &BigUint, len: usize) -> Vec<u8> {
    let bytes = x.to_bytes_be();
    let mut out = vec![0; len - bytes.len()];
    out.extend(bytes);
    out
}

/// Arithmetic modulo the prime `p`.
#[derive(Clone)]
pub(crate) struct Field {
    pub(crate) p: BigUint,
}

impl Field {
    fn reduce(&self, x: &BigUint) -> BigUint {
        x % &self.p
    }

    fn add(&self, x: &BigUint, y: &BigUint) -> BigUint {
        (x + y) % &self.p
    }

    fn sub(&self, x: &BigUint, y: &BigUint) -> BigUint {
        (x + &self.p - (y % &self.p)) % &self.p
    }

    fn mul(&self, x: &BigUint, y: &BigUint) -> BigUint {
        (x * y) % &self.p
    }

    fn neg(&self, x: &BigUint) -> BigUint {
        self.sub(&BigUint::ZERO, x)
    }

    fn pow(&self, x: &BigUint, e: &BigUint) -> BigUint {
        x.modpow(e, &self.p)
    }

    /// `1 / x`, or zero for zero.
    fn inv(&self, x: &BigUint) -> BigUint {
        self.reduce(x).modinv(&self.p).unwrap_or_default()
    }

    fn div(&self, x: &BigUint, y: &BigUint) -> BigUint {
        self.mul(x, &self.inv(y))
    }

    fn is_square(&self, x: &BigUint) -> bool {
        let legendre = self.pow(x, &((&self.p - 1u32) >> 1));
        legendre <= BigUint::from(1u32)
    }

    /// A square root of `x`, for `p` = 3 mod 4, if it has one.
    fn sqrt_3_mod_4(&self, x: &BigUint) -> Option<BigUint> {
        let root = self.pow(x, &((&self.p + 1u32) >> 2));
        (self.mul(&root, &root) == self.reduce(x)).then_some(root)
    }
}

/// An affine point, or `None` for the identity.
pub(crate) type Point = Option<(BigUint, BigUint)>;

/// A point in Jacobian coordinates, `(X / Z^2, Y / Z^3)`, the identity
/// where `Z` is zero.
type Jacobian = (BigUint, BigUint, BigUint);

/// A NIST prime curve, y^2 = x^3 - 3x + b, with its base point's prime order
/// `n`, cofactor 1, and its RFC 9380 suite: the SSWU map's `z` and the hash
/// that `expand_message_xmd` runs.
pub(crate) struct Weierstrass {
    pub(crate) field: Field,
    pub(crate) b: BigUint,
    pub(crate) n: BigUint,
    pub(crate) g: (BigUint, BigUint),
    /// The length of an encoded field element or scalar.
    pub(crate) len: usize,
    /// RFC 9380's `L`, the bytes hashed to each field element or scalar.
    pub(crate) l: usize,
    z: BigUint,
    hash: fn(&[u8]) -> Vec<u8>,
    hash_block: usize,
}

fn sha256(data: &[u8]) -> Vec<u8> {
    sha2::Sha256::digest(data).to_vec()
}

fn sha384(data: &[u8]) -> Vec<u8> {
    sha2::Sha384::digest(data).to_vec()
}

fn sha512(data: &[u8]) -> Vec<u8> {
    sha2::Sha512::digest(data).to_vec()
}

/// SEC 2's secp256r1, with RFC 9380's P256_XMD:SHA-256_SSWU_RO_.
pub(crate) fn p256() -> Weierstrass {
    let p = hex("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff");
    Weierstrass {
        b: hex("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b"),
        n: hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"),
        g: (
            hex("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296"),
            hex("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5"),
        ),
        len: 32,
        l: 48,
        z: &p - 10u32,
        hash: sha256,
        hash_block: 64,
        field: Field { p },
    }
}

/// SEC 2's secp384r1, with RFC 9380's P384_XMD:SHA-384_SSWU_RO_.
pub(crate) fn p384() -> Weierstrass {
    let p = hex(
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff",
    );
    Weierstrass {
        b: hex(
            "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef",
        ),
        n: hex(
            "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
        ),
        g: (
            hex(
                "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
            ),
            hex(
                "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
            ),
        ),
        len: 48,
        l: 72,
        z: &p - 12u32,
        hash: sha384,
        hash_block: 128,
        field: Field { p },
    }
}

/// SEC 2's secp521r1, with RFC 9380's P521_XMD:SHA-512_SSWU_RO_.
pub(crate) fn p521() -> Weierstrass {
    let p = (BigUint::from(1u32) << 521u32) - 1u32;
    Weierstrass {
        b: hex(
            "0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00",
        ),
        n: hex(
            "01fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e91386409",
        ),
        g: (
            hex(
                "00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66",
            ),
            hex(
                "011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650",
            ),
        ),
        len: 66,
        l: 98,
        z: &p - 4u32,
        hash: sha512,
        hash_block: 128,
        field: Field { p },
    }
}

impl Weierstrass {
    fn a(&self) -> BigUint {
        &self.field.p - 3u32
    }

    /// x^3 - 3x + b.
    fn rhs(&self, x: &BigUint) -> BigUint {
        let f = &self.field;
        f.add(
            &f.mul(&f.mul(x, x), x),
            &f.add(&f.mul(&self.a(), x), &self.b),
        )
    }

    pub(crate) fn add(&self, p: &Point, q: &Point) -> Point {
        let f = &self.field;
        let ((x1, y1), (x2, y2)) = match (p, q) {
            (None, q) => return q.clone(),
            (p, None) => return p.clone(),
            (Some(p), Some(q)) => (p, q),
        };
        let slope = if x1 == x2 {
            if f.add(y1, y2) == BigUint::ZERO {
                return None;
            }
            let three_x2 = f.mul(&BigUint::from(3u32), &f.mul(x1, x1));
            f.div(&f.add(&three_x2, &self.a()), &f.add(y1, y1))
        } else {
            f.div(&f.sub(y2, y1), &f.sub(x2, x1))
        };
        let x3 = f.sub(&f.sub(&f.mul(&slope, &slope), x1), x2);
        let y3 = f.sub(&f.mul(&slope, &f.sub(x1, &x3)), y1);
        Some((x3, y3))
    }

    /// `k` times `p`, by double-and-add in Jacobian coordinates, with the
    /// Explicit-Formulas Database's dbl-2001-b and add-2007-bl.
    pub(crate) fn mul(&self, k: &BigUint, p: &Point) -> Point {
        let f = &self.field;
        let one = BigUint::from(1u32);
        let (px, py) = p.as_ref()?;
        let base = (px.clone(), py.clone(), one.clone());
        let mut acc = (BigUint::ZERO, one.clone(), BigUint::ZERO);
        for i in (0..k.bits()).rev() {
            acc = self.jacobian_double(&acc);
            if k.bit(i) {
                acc = self.jacobian_add(&acc, &base);
            }
        }
        let (x, y, z) = acc;
        if z == BigUint::ZERO {
            return None;
        }
        let z_inv = f.inv(&z);
        let z_inv2 = f.mul(&z_inv, &z_inv);
        Some((f.mul(&x, &z_inv2), f.mul(&y, &f.mul(&z_inv2, &z_inv))))
    }

    fn jacobian_double(&self, (x, y, z): &Jacobian) -> Jacobian {
        let f = &self.field;
        if *z == BigUint::ZERO || *y == BigUint::ZERO {
            return (BigUint::ZERO, BigUint::from(1u32), BigUint::ZERO);
        }
        let delta = f.mul(z, z);
        let gamma = f.mul(y, y);
        let beta = f.mul(x, &gamma);
        let alpha = f.mul(
            &BigUint::from(3u32),
            &f.mul(&f.sub(x, &delta), &f.add(x, &delta)),
        );
        let x3 = f.sub(&f.mul(&alpha, &alpha), &f.mul(&BigUint::from(8u32), &beta));
        let y_plus_z = f.add(y, z);
        let z3 = f.sub(&f.sub(&f.mul(&y_plus_z, &y_plus_z), &gamma), &delta);
        let four_beta = f.mul(&BigUint::from(4u32), &beta);
        let y3 = f.sub(
            &f.mul(&alpha, &f.sub(&four_beta, &x3)),
            &f.mul(&BigUint::from(8u32), &f.mul(&gamma, &gamma)),
        );
        (x3, y3, z3)
    }

    fn jacobian_add(&self, p: &Jacobian, q: &Jacobian) -> Jacobian {
        let f = &self.field;
        let ((x1, y1, z1), (x2, y2, z2)) = (p, q);
        if *z1 == BigUint::ZERO {
            return q.clone();
        }
        if *z2 == BigUint::ZERO {
            return p.clone();
        }
        let z1z1 = f.mul(z1, z1);
        let z2z2 = f.mul(z2, z2);
        let u1 = f.mul(x1, &z2z2);
        let u2 = f.mul(x2, &z1z1);
        let s1 = f.mul(y1, &f.mul(z2, &z2z2));
        let s2 = f.mul(y2, &f.mul(z1, &z1z1));
        if u1 == u2 {
            return match s1 == s2 {
                true => self.jacobian_double(p),
                false => (BigUint::ZERO, BigUint::from(1u32), BigUint::ZERO),
            };
        }
        let h = f.sub(&u2, &u1);
        let two_h = f.add(&h, &h);
        let i = f.mul(&two_h, &two_h);
        let j = f.mul(&h, &i);
        let r = f.add(&f.sub(&s2, &s1), &f.sub(&s2, &s1));
        let v = f.mul(&u1, &i);
        let x3 = f.sub(&f.sub(&f.mul(&r, &r), &j), &f.add(&v, &v));
        let s1j = f.mul(&s1, &j);
        let y3 = f.sub(&f.mul(&r, &f.sub(&v, &x3)), &f.add(&s1j, &s1j));
        let z1_plus_z2 = f.add(z1, z2);
        let z3 = f.mul(
            &f.sub(&f.sub(&f.mul(&z1_plus_z2, &z1_plus_z2), &z1z1), &z2z2),
            &h,
        );
        (x3, y3, z3)
    }

    pub(crate) fn base(&self) -> Point {
        Some(self.g.clone())
    }

    /// SEC 1's uncompressed encoding of a point other than the identity.
    pub(crate) fn encode(&self, point: &Point) -> Vec<u8> {
        let (x, y) = point.as_ref().expect("the identity has no encoding here");
        [&[4][..], &be_bytes(x, self.len), &be_bytes(y, self.len)].concat()
    }

    /// A point from its uncompressed or compressed SEC 1 encoding, if that
    /// is a point on the curve other than the identity.
    pub(crate) fn decode(&self, bytes: &[u8]) -> Option<(BigUint, BigUint)> {
        let (tag, rest) = bytes.split_first()?;
        let x = BigUint::from_bytes_be(rest.get(..self.len)?);
        if x >= self.field.p {
            return None;
        }
        let y = match (tag, rest.len()) {
            (4, n) if n == 2 * self.len => {
                let y = BigUint::from_bytes_be(&rest[self.len..]);
                (y < self.field.p && self.field.mul(&y, &y) == self.rhs(&x)).then_some(y)?
            }
            (2 | 3, n) if n == self.len => {
                let y = self.field.sqrt_3_mod_4(&self.rhs(&x))?;
                match y.bit(0) == (*tag == 3) {
                    true => y,
                    false => self.field.neg(&y),
                }
            }
            _ => return None,
        };
        Some((x, y))
    }

    /// The public key of the private scalar `d`, uncompressed.
    pub(crate) fn public_key(&self, d: &[u8]) -> Vec<u8> {
        self.encode(&self.mul(&BigUint::from_bytes_be(d), &self.base()))
    }

    /// The ECDH secret, the x-coordinate of `d` times `peer`, if `peer` is a
    /// point on the curve.
    pub(crate) fn agree(&self, d: &[u8], peer: &[u8]) -> Option<Vec<u8>> {
        let peer = self.decode(peer)?;
        let (x, _) = self.mul(&BigUint::from_bytes_be(d), &Some(peer))?;
        Some(be_bytes(&x, self.len))
    }

    /// SEC 1's `e`: the digest's leftmost bits, as many as `n` has.
    fn digest_to_int(&self, digest: &[u8]) -> BigUint {
        let e = BigUint::from_bytes_be(digest);
        let bits = 8 * digest.len() as u64;
        match bits > self.n.bits() {
            true => e >> (bits - self.n.bits()),
            false => e,
        }
    }

    /// ECDSA's signature over `digest` under the private scalar `d`, as
    /// `r || s`, with a nonce hashed from both.
    pub(crate) fn sign(&self, d: &[u8], digest: &[u8]) -> Vec<u8> {
        let scalar = Field { p: self.n.clone() };
        let d_int = BigUint::from_bytes_be(d);
        let e = self.digest_to_int(digest);
        for counter in 0u8.. {
            let seed = sha512(&[d, digest, &[counter]].concat());
            let k = BigUint::from_bytes_be(&seed) % (&self.n - 1u32) + 1u32;
            let Some((x, _)) = self.mul(&k, &self.base()) else {
                continue;
            };
            let r = x % &self.n;
            let s = scalar.div(&scalar.add(&e, &scalar.mul(&r, &d_int)), &k);
            if r != BigUint::ZERO && s != BigUint::ZERO {
                return [be_bytes(&r, self.len), be_bytes(&s, self.len)].concat();
            }
        }
        unreachable!()
    }

    /// Whether `signature`, as `r || s`, is ECDSA's over `digest` under the
    /// encoded public key.
    pub(crate) fn verify(&self, public_key: &[u8], digest: &[u8], signature: &[u8]) -> bool {
        let Some(q) = self.decode(public_key) else {
            return false;
        };
        if signature.len() != 2 * self.len {
            return false;
        }
        let r = BigUint::from_bytes_be(&signature[..self.len]);
        let s = BigUint::from_bytes_be(&signature[self.len..]);
        let in_range = |x: &BigUint| *x != BigUint::ZERO && *x < self.n;
        if !in_range(&r) || !in_range(&s) {
            return false;
        }
        let scalar = Field { p: self.n.clone() };
        let w = scalar.inv(&s);
        let u1 = scalar.mul(&self.digest_to_int(digest), &w);
        let u2 = scalar.mul(&r, &w);
        let point = self.add(&self.mul(&u1, &self.base()), &self.mul(&u2, &Some(q)));
        point.is_some_and(|(x, _)| x % &self.n == r)
    }

    /// RFC 9380's `expand_message_xmd` over this suite's hash, or `None`
    /// where it refuses the lengths, or for an empty DST.
    pub(crate) fn expand_message_xmd(&self, msg: &[u8], dst: &[u8], len: usize) -> Option<Vec<u8>> {
        if dst.is_empty() {
            return None;
        }
        let oversize;
        let dst = match dst.len() > 255 {
            true => {
                oversize = (self.hash)(&[b"H2C-OVERSIZE-DST-", dst].concat());
                &oversize[..]
            }
            false => dst,
        };
        let b_len = (self.hash)(b"").len();
        let ell = len.div_ceil(b_len);
        if ell > 255 || len > 65535 {
            return None;
        }
        let dst_prime = [dst, &[dst.len() as u8]].concat();
        let msg_prime = [
            &vec![0u8; self.hash_block][..],
            msg,
            &(len as u16).to_be_bytes(),
            &[0],
            &dst_prime,
        ]
        .concat();
        let b0 = (self.hash)(&msg_prime);
        let mut b = (self.hash)(&[&b0[..], &[1], &dst_prime].concat());
        let mut out = b.clone();
        for i in 2..=ell {
            let xored: Vec<u8> = b0.iter().zip(&b).map(|(x, y)| x ^ y).collect();
            b = (self.hash)(&[&xored[..], &[i as u8], &dst_prime].concat());
            out.extend(&b);
        }
        out.truncate(len);
        Some(out)
    }

    /// RFC 9380's `hash_to_field`: `count` elements modulo `modulus`.
    fn hash_to_field(
        &self,
        msg: &[u8],
        dst: &[u8],
        count: usize,
        modulus: &BigUint,
    ) -> Option<Vec<BigUint>> {
        let uniform = self.expand_message_xmd(msg, dst, count * self.l)?;
        Some(
            uniform
                .chunks(self.l)
                .map(|chunk| BigUint::from_bytes_be(chunk) % modulus)
                .collect(),
        )
    }

    /// RFC 9380 section 6.6.2's simplified SWU map, as its straight-line
    /// description writes it.
    fn map_to_curve(&self, u: &BigUint) -> (BigUint, BigUint) {
        let f = &self.field;
        let a = self.a();
        let zu2 = f.mul(&self.z, &f.mul(u, u));
        let tv1 = f.inv(&f.add(&f.mul(&zu2, &zu2), &zu2));
        let x1 = match tv1 == BigUint::ZERO {
            true => f.div(&self.b, &f.mul(&self.z, &a)),
            false => f.mul(
                &f.div(&f.neg(&self.b), &a),
                &f.add(&BigUint::from(1u32), &tv1),
            ),
        };
        let gx1 = self.rhs(&x1);
        let (x, y) = match f.is_square(&gx1) {
            true => (x1, f.sqrt_3_mod_4(&gx1).unwrap()),
            false => {
                let x2 = f.mul(&zu2, &x1);
                let y2 = f.sqrt_3_mod_4(&self.rhs(&x2)).unwrap();
                (x2, y2)
            }
        };
        match u.bit(0) == y.bit(0) {
            true => (x, y),
            false => (x, f.neg(&y)),
        }
    }

    /// RFC 9380's `hash_to_curve`, encoded uncompressed, or `None` where
    /// `expand_message_xmd` refuses or the two mapped points cancel.
    pub(crate) fn hash_to_curve(&self, msg: &[u8], dst: &[u8]) -> Option<Vec<u8>> {
        let u = self.hash_to_field(msg, dst, 2, &self.field.p)?;
        let point = self.add(
            &Some(self.map_to_curve(&u[0])),
            &Some(self.map_to_curve(&u[1])),
        );
        point.is_some().then(|| self.encode(&point))
    }

    /// RFC 9497's `HashToScalar`: `hash_to_field` modulo `n`, big-endian.
    pub(crate) fn hash_to_scalar(&self, msg: &[u8], dst: &[u8]) -> Option<Vec<u8>> {
        let scalar = self.hash_to_field(msg, dst, 1, &self.n)?;
        Some(be_bytes(&scalar[0], self.len))
    }
}

/// edwards25519, -x^2 + y^2 = 1 + d x^2 y^2 over 2^255 - 19, from RFC 8032,
/// and ristretto255 over it, from RFC 9496.
pub(crate) struct Edwards {
    pub(crate) field: Field,
    d: BigUint,
    /// The base point's prime order.
    pub(crate) l: BigUint,
    base: (BigUint, BigUint),
    sqrt_m1: BigUint,
}

/// An affine edwards25519 point; the identity is (0, 1).
pub(crate) type EdPoint = (BigUint, BigUint);

/// An edwards25519 point in extended coordinates, `(X / Z, Y / Z)` with
/// `T = XY / Z`.
type Extended = (BigUint, BigUint, BigUint, BigUint);

pub(crate) fn edwards25519() -> Edwards {
    let field = Field {
        p: (BigUint::from(1u32) << 255u32) - 19u32,
    };
    let d = field.div(
        &field.neg(&BigUint::from(121665u32)),
        &BigUint::from(121666u32),
    );
    let l = (BigUint::from(1u32) << 252u32) + dec("27742317777372353535851937790883648493");
    let y = field.div(&BigUint::from(4u32), &BigUint::from(5u32));
    let sqrt_m1 = field.pow(&BigUint::from(2u32), &((&field.p - 1u32) >> 2));
    let mut curve = Edwards {
        field,
        d,
        l,
        base: (BigUint::ZERO, y.clone()),
        sqrt_m1,
    };
    curve.base = curve.decode(&curve.encode(&(BigUint::ZERO, y))).unwrap();
    curve
}

impl Edwards {
    pub(crate) fn identity() -> EdPoint {
        (BigUint::ZERO, BigUint::from(1u32))
    }

    /// The complete twisted Edwards addition law.
    pub(crate) fn add(&self, (x1, y1): &EdPoint, (x2, y2): &EdPoint) -> EdPoint {
        let f = &self.field;
        let one = BigUint::from(1u32);
        let dxxyy = f.mul(&self.d, &f.mul(&f.mul(x1, x2), &f.mul(y1, y2)));
        let x3 = f.div(&f.add(&f.mul(x1, y2), &f.mul(x2, y1)), &f.add(&one, &dxxyy));
        let y3 = f.div(&f.add(&f.mul(y1, y2), &f.mul(x1, x2)), &f.sub(&one, &dxxyy));
        (x3, y3)
    }

    /// `k` times `p`, by double-and-add in extended coordinates
    /// `(X : Y : Z : T)`, with the Explicit-Formulas Database's complete
    /// add-2008-hwcd-3 for a = -1.
    pub(crate) fn mul(&self, k: &BigUint, (x, y): &EdPoint) -> EdPoint {
        let f = &self.field;
        let one = BigUint::from(1u32);
        let two_d = f.add(&self.d, &self.d);
        let add = |(x1, y1, z1, t1): &Extended, (x2, y2, z2, t2): &Extended| -> Extended {
            let a = f.mul(&f.sub(y1, x1), &f.sub(y2, x2));
            let b = f.mul(&f.add(y1, x1), &f.add(y2, x2));
            let c = f.mul(&f.mul(t1, &two_d), t2);
            let d = f.mul(&f.add(z1, z1), z2);
            let (e, ff, g, h) = (f.sub(&b, &a), f.sub(&d, &c), f.add(&d, &c), f.add(&b, &a));
            (f.mul(&e, &ff), f.mul(&g, &h), f.mul(&ff, &g), f.mul(&e, &h))
        };
        let base = (x.clone(), y.clone(), one.clone(), f.mul(x, y));
        let mut acc = (BigUint::ZERO, one.clone(), one, BigUint::ZERO);
        for i in (0..k.bits()).rev() {
            acc = add(&acc, &acc);
            if k.bit(i) {
                acc = add(&acc, &base);
            }
        }
        let z_inv = f.inv(&acc.2);
        (f.mul(&acc.0, &z_inv), f.mul(&acc.1, &z_inv))
    }

    pub(crate) fn base(&self) -> EdPoint {
        self.base.clone()
    }

    /// RFC 8032 section 5.1.2's encoding.
    pub(crate) fn encode(&self, (x, y): &EdPoint) -> [u8; 32] {
        let mut out = [0u8; 32];
        let bytes = y.to_bytes_le();
        out[..bytes.len()].copy_from_slice(&bytes);
        out[31] |= (x.bit(0) as u8) << 7;
        out
    }

    /// RFC 8032 section 5.1.3's decoding, which refuses a `y` of `p` or
    /// more, and `x = 0` with the sign bit set.
    pub(crate) fn decode(&self, bytes: &[u8; 32]) -> Option<EdPoint> {
        let f = &self.field;
        let sign = bytes[31] >> 7 == 1;
        let mut y = *bytes;
        y[31] &= 0x7f;
        let y = BigUint::from_bytes_le(&y);
        if y >= f.p {
            return None;
        }
        let one = BigUint::from(1u32);
        let yy = f.mul(&y, &y);
        let xx = f.div(&f.sub(&yy, &one), &f.add(&f.mul(&self.d, &yy), &one));
        let mut x = f.pow(&xx, &((&f.p + 3u32) >> 3));
        if f.mul(&x, &x) != xx {
            x = f.mul(&x, &self.sqrt_m1);
        }
        if f.mul(&x, &x) != xx || (x == BigUint::ZERO && sign) {
            return None;
        }
        if x.bit(0) != sign {
            x = f.neg(&x);
        }
        Some((x, y))
    }

    fn hash_to_scalar(&self, parts: &[&[u8]]) -> BigUint {
        BigUint::from_bytes_le(&sha512(&parts.concat())) % &self.l
    }

    /// RFC 8032's secret scalar and prefix of a 32-byte seed.
    fn expand(&self, seed: &[u8; 32]) -> (BigUint, Vec<u8>) {
        let h = sha512(seed);
        let mut a = <[u8; 32]>::try_from(&h[..32]).unwrap();
        a[0] &= 248;
        a[31] &= 127;
        a[31] |= 64;
        (BigUint::from_bytes_le(&a), h[32..].to_vec())
    }

    /// Ed25519's public key for a seed.
    pub(crate) fn ed25519_public_key(&self, seed: &[u8; 32]) -> [u8; 32] {
        self.encode(&self.mul(&self.expand(seed).0, &self.base()))
    }

    /// Ed25519's signature of `message` under a seed.
    pub(crate) fn ed25519_sign(&self, seed: &[u8; 32], message: &[u8]) -> [u8; 64] {
        let (a, prefix) = self.expand(seed);
        let public = self.encode(&self.mul(&a, &self.base()));
        let r = self.hash_to_scalar(&[&prefix, message]);
        let big_r = self.encode(&self.mul(&r, &self.base()));
        let k = self.hash_to_scalar(&[&big_r, &public, message]);
        let s = (r + k * a) % &self.l;
        let mut signature = [0u8; 64];
        signature[..32].copy_from_slice(&big_r);
        let s = s.to_bytes_le();
        signature[32..32 + s.len()].copy_from_slice(&s);
        signature
    }

    /// Whether `signature` is Ed25519's over `message` under `public_key`,
    /// by the cofactorless check `[S]B = R + [k]A`.
    pub(crate) fn ed25519_verify(
        &self,
        public_key: &[u8; 32],
        message: &[u8],
        signature: &[u8],
    ) -> bool {
        let Ok(signature) = <&[u8; 64]>::try_from(signature) else {
            return false;
        };
        let big_r_bytes = <[u8; 32]>::try_from(&signature[..32]).unwrap();
        let (Some(a), Some(big_r)) = (self.decode(public_key), self.decode(&big_r_bytes)) else {
            return false;
        };
        let s = BigUint::from_bytes_le(&signature[32..]);
        if s >= self.l {
            return false;
        }
        let k = self.hash_to_scalar(&[&big_r_bytes, public_key, message]);
        self.mul(&s, &self.base()) == self.add(&big_r, &self.mul(&k, &a))
    }

    fn is_negative(x: &BigUint) -> bool {
        x.bit(0)
    }

    fn abs(&self, x: &BigUint) -> BigUint {
        match Self::is_negative(x) {
            true => self.field.neg(x),
            false => x.clone(),
        }
    }

    /// RFC 9496 section 4.2's `SQRT_RATIO_M1`.
    fn sqrt_ratio_m1(&self, u: &BigUint, v: &BigUint) -> (bool, BigUint) {
        let f = &self.field;
        let v3 = f.mul(&f.mul(v, v), v);
        let v7 = f.mul(&f.mul(&v3, &v3), v);
        let r = f.mul(
            &f.mul(u, &v3),
            &f.pow(&f.mul(u, &v7), &((&f.p - 5u32) >> 3)),
        );
        let check = f.mul(v, &f.mul(&r, &r));
        let u_neg = f.neg(u);
        let correct_sign = check == f.reduce(u);
        let flipped_sign = check == u_neg;
        let flipped_sign_i = check == f.mul(&u_neg, &self.sqrt_m1);
        let r = match flipped_sign || flipped_sign_i {
            true => f.mul(&self.sqrt_m1, &r),
            false => r,
        };
        (correct_sign || flipped_sign, self.abs(&r))
    }

    /// RFC 9496's `ONE_MINUS_D_SQ`, `D_MINUS_ONE_SQ`, `SQRT_AD_MINUS_ONE`,
    /// and `INVSQRT_A_MINUS_D`. The two roots are the RFC's, which pick a
    /// sign no definition gives, so each is checked against its square.
    fn ristretto_constants(&self) -> [BigUint; 4] {
        let f = &self.field;
        let one = BigUint::from(1u32);
        let sqrt_ad_minus_one =
            dec("25063068953384623474111414158702152701244531502492656460079210482610430750235");
        let invsqrt_a_minus_d =
            dec("54469307008909316920995813868745141605393597292927456921205312896311721017578");
        let minus_one = f.neg(&one);
        assert_eq!(
            f.mul(&sqrt_ad_minus_one, &sqrt_ad_minus_one),
            f.sub(&f.mul(&minus_one, &self.d), &one)
        );
        assert_eq!(
            f.mul(
                &f.mul(&invsqrt_a_minus_d, &invsqrt_a_minus_d),
                &f.sub(&minus_one, &self.d)
            ),
            one
        );
        [
            f.sub(&one, &f.mul(&self.d, &self.d)),
            f.mul(&f.sub(&self.d, &one), &f.sub(&self.d, &one)),
            sqrt_ad_minus_one,
            invsqrt_a_minus_d,
        ]
    }

    /// RFC 9496 section 4.3.1's decoding, to an affine representative.
    pub(crate) fn ristretto_decode(&self, bytes: &[u8; 32]) -> Option<EdPoint> {
        let f = &self.field;
        let s = BigUint::from_bytes_le(bytes);
        if s >= f.p || Self::is_negative(&s) {
            return None;
        }
        let one = BigUint::from(1u32);
        let ss = f.mul(&s, &s);
        let u1 = f.sub(&one, &ss);
        let u2 = f.add(&one, &ss);
        let u2_sqr = f.mul(&u2, &u2);
        let v = f.sub(&f.neg(&f.mul(&self.d, &f.mul(&u1, &u1))), &u2_sqr);
        let (was_square, invsqrt) = self.sqrt_ratio_m1(&one, &f.mul(&v, &u2_sqr));
        let den_x = f.mul(&invsqrt, &u2);
        let den_y = f.mul(&f.mul(&invsqrt, &den_x), &v);
        let x = self.abs(&f.mul(&f.add(&s, &s), &den_x));
        let y = f.mul(&u1, &den_y);
        let t = f.mul(&x, &y);
        (was_square && !Self::is_negative(&t) && y != BigUint::ZERO).then_some((x, y))
    }

    /// RFC 9496 section 4.3.2's encoding of an affine point, `z = 1`.
    pub(crate) fn ristretto_encode(&self, (x0, y0): &EdPoint) -> [u8; 32] {
        let f = &self.field;
        let [_, _, _, invsqrt_a_minus_d] = self.ristretto_constants();
        let one = BigUint::from(1u32);
        let t0 = f.mul(x0, y0);
        let u1 = f.mul(&f.add(&one, y0), &f.sub(&one, y0));
        let u2 = f.mul(x0, y0);
        let (_, invsqrt) = self.sqrt_ratio_m1(&one, &f.mul(&u1, &f.mul(&u2, &u2)));
        let den1 = f.mul(&invsqrt, &u1);
        let den2 = f.mul(&invsqrt, &u2);
        let z_inv = f.mul(&f.mul(&den1, &den2), &t0);
        let rotate = Self::is_negative(&f.mul(&t0, &z_inv));
        let (x, y, den_inv) = match rotate {
            true => (
                f.mul(y0, &self.sqrt_m1),
                f.mul(x0, &self.sqrt_m1),
                f.mul(&den1, &invsqrt_a_minus_d),
            ),
            false => (x0.clone(), y0.clone(), den2),
        };
        let y = match Self::is_negative(&f.mul(&x, &z_inv)) {
            true => f.neg(&y),
            false => y,
        };
        let s = self.abs(&f.mul(&den_inv, &f.sub(&one, &y)));
        let mut out = [0u8; 32];
        let bytes = s.to_bytes_le();
        out[..bytes.len()].copy_from_slice(&bytes);
        out
    }

    /// RFC 9496 section 4.3.4's `MAP`, to an affine point.
    fn ristretto_map(&self, t: &BigUint) -> EdPoint {
        let f = &self.field;
        let [one_minus_d_sq, d_minus_one_sq, sqrt_ad_minus_one, _] = self.ristretto_constants();
        let one = BigUint::from(1u32);
        let r = f.mul(&self.sqrt_m1, &f.mul(t, t));
        let u = f.mul(&f.add(&r, &one), &one_minus_d_sq);
        let v = f.mul(
            &f.sub(&f.neg(&one), &f.mul(&r, &self.d)),
            &f.add(&r, &self.d),
        );
        let (was_square, s) = self.sqrt_ratio_m1(&u, &v);
        let (s, c) = match was_square {
            true => (s, f.neg(&one)),
            false => (f.neg(&self.abs(&f.mul(&s, t))), r.clone()),
        };
        let n = f.sub(&f.mul(&f.mul(&c, &f.sub(&r, &one)), &d_minus_one_sq), &v);
        let w0 = f.mul(&f.add(&s, &s), &v);
        let w1 = f.mul(&n, &sqrt_ad_minus_one);
        let w2 = f.sub(&one, &f.mul(&s, &s));
        let w3 = f.add(&one, &f.mul(&s, &s));
        // (w0 w3 : w2 w1 : w1 w3), as an affine point.
        let z = f.mul(&w1, &w3);
        (f.div(&f.mul(&w0, &w3), &z), f.div(&f.mul(&w2, &w1), &z))
    }

    /// RFC 9496 section 4.3.4's element from 64 uniform bytes.
    pub(crate) fn ristretto_from_uniform_bytes(&self, bytes: &[u8; 64]) -> EdPoint {
        let half = |half: &[u8]| {
            let mut t = <[u8; 32]>::try_from(half).unwrap();
            t[31] &= 0x7f;
            BigUint::from_bytes_le(&t) % &self.field.p
        };
        self.add(
            &self.ristretto_map(&half(&bytes[..32])),
            &self.ristretto_map(&half(&bytes[32..])),
        )
    }

    /// A scalar from 64 uniform bytes: their little-endian value modulo `l`.
    pub(crate) fn scalar_from_uniform_bytes(&self, bytes: &[u8; 64]) -> BigUint {
        BigUint::from_bytes_le(bytes) % &self.l
    }

    /// A scalar's 32-byte little-endian encoding.
    pub(crate) fn scalar_bytes(x: &BigUint) -> [u8; 32] {
        let mut out = [0u8; 32];
        let bytes = x.to_bytes_le();
        out[..bytes.len()].copy_from_slice(&bytes);
        out
    }
}
