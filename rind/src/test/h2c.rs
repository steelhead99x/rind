// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The oracle for hashing to P-256, P-384, and P-521: RFC 9380's
//! `expand_message_xmd` over the `sha2` crate, and its simplified SWU map
//! (section 6.6.2), on `num-bigint` integers with schoolbook affine
//! arithmetic. It shares no code with rind's field arithmetic, which on
//! armv7 and the portable backend is fiat-crypto's, as RustCrypto's NIST
//! curves' is, so this is the independent reference there. It takes every
//! branch the RFC does, so it is slow and leaks everything: tests only.

use num_bigint::BigUint;
use sha2::{Digest, Sha256, Sha384, Sha512};

/// A suite `P*_XMD:SHA-*_SSWU_RO_`: the curve `y^2 = x^3 - 3x + b` over the
/// prime `p`, its order `n`, and the hash.
pub(crate) struct Suite {
    p: BigUint,
    b: BigUint,
    n: BigUint,
    /// The sign of `Z`, a small negative number: the map's non-square.
    z: u32,
    /// `L`, the bytes `hash_to_field` takes per element (section 5).
    l: usize,
    hash: Hash,
}

#[derive(Clone, Copy)]
enum Hash {
    Sha256,
    Sha384,
    Sha512,
}

impl Hash {
    /// `(b_in_bytes, s_in_bytes)`.
    fn sizes(self) -> (usize, usize) {
        match self {
            Self::Sha256 => (32, 64),
            Self::Sha384 => (48, 128),
            Self::Sha512 => (64, 128),
        }
    }

    fn digest(self, parts: &[&[u8]]) -> Vec<u8> {
        fn run<D: Digest>(parts: &[&[u8]]) -> Vec<u8> {
            let mut h = D::new();
            for part in parts {
                h.update(part);
            }
            h.finalize().to_vec()
        }
        match self {
            Self::Sha256 => run::<Sha256>(parts),
            Self::Sha384 => run::<Sha384>(parts),
            Self::Sha512 => run::<Sha512>(parts),
        }
    }
}

fn int(hex: &str) -> BigUint {
    BigUint::parse_bytes(hex.as_bytes(), 16).unwrap()
}

impl Suite {
    /// `P256_XMD:SHA-256_SSWU_RO_`, with the constants of FIPS 186-5.
    pub(crate) fn p256() -> Self {
        Self {
            p: int("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"),
            b: int("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b"),
            n: int("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"),
            z: 10,
            l: 48,
            hash: Hash::Sha256,
        }
    }

    /// `P384_XMD:SHA-384_SSWU_RO_`.
    pub(crate) fn p384() -> Self {
        Self {
            p: int(concat!(
                "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe",
                "ffffffff0000000000000000ffffffff"
            )),
            b: int(concat!(
                "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875a",
                "c656398d8a2ed19d2a85c8edd3ec2aef"
            )),
            n: int(concat!(
                "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf",
                "581a0db248b0a77aecec196accc52973"
            )),
            z: 12,
            l: 72,
            hash: Hash::Sha384,
        }
    }

    /// `P521_XMD:SHA-512_SSWU_RO_`.
    pub(crate) fn p521() -> Self {
        Self {
            p: (BigUint::from(1u8) << 521) - 1u8,
            b: int(concat!(
                "0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef1",
                "09e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b50",
                "3f00"
            )),
            n: int(concat!(
                "01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "fffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e9138",
                "6409"
            )),
            z: 4,
            l: 98,
            hash: Hash::Sha512,
        }
    }

    /// `L`, the bytes `hash_to_field` takes per element.
    pub(crate) fn l(&self) -> usize {
        self.l
    }

    /// The integer `tv` is, reduced mod `p`.
    pub(crate) fn reduce(&self, tv: &[u8]) -> BigUint {
        BigUint::from_bytes_be(tv) % &self.p
    }

    /// The bytes of a coordinate or scalar.
    pub(crate) fn bytes(&self) -> usize {
        usize::try_from(self.p.bits().div_ceil(8)).unwrap()
    }

    /// RFC 9380's `expand_message_xmd(msg, dst, len)` (section 5.3.1), for
    /// `msg` the concatenation of `msg`.
    pub(crate) fn expand_message_xmd(&self, msg: &[&[u8]], dst: &[u8], len: usize) -> Vec<u8> {
        let (b_in_bytes, s_in_bytes) = self.hash.sizes();
        let ell = len.div_ceil(b_in_bytes);
        assert!(ell <= 255 && len <= 65535 && !dst.is_empty());
        let long_dst;
        let dst = if dst.len() > 255 {
            long_dst = self.hash.digest(&[b"H2C-OVERSIZE-DST-", dst]);
            &long_dst
        } else {
            dst
        };
        let dst_prime = [dst, &[dst.len() as u8]].concat();
        let z_pad = vec![0; s_in_bytes];
        let l_i_b_str = (len as u16).to_be_bytes();

        let mut parts = vec![&z_pad[..]];
        parts.extend(msg);
        parts.extend([&l_i_b_str[..], &[0], &dst_prime]);
        let b0 = self.hash.digest(&parts);
        let mut b = self.hash.digest(&[&b0, &[1], &dst_prime]);
        let mut out = b.clone();
        for i in 2..=ell {
            let xored: Vec<u8> = b0.iter().zip(&b).map(|(x, y)| x ^ y).collect();
            b = self.hash.digest(&[&xored, &[i as u8], &dst_prime]);
            out.extend(&b);
        }
        out.truncate(len);
        out
    }

    /// `hash_to_field` (section 5.2) to `count` elements mod `modulus`.
    fn hash_to_field(
        &self,
        msg: &[&[u8]],
        dst: &[u8],
        count: usize,
        modulus: &BigUint,
    ) -> Vec<BigUint> {
        let uniform = self.expand_message_xmd(msg, dst, count * self.l);
        uniform
            .chunks(self.l)
            .map(|tv| BigUint::from_bytes_be(tv) % modulus)
            .collect()
    }

    /// Hashes to a scalar mod `n`, as RFC 9497 and RFC 9591 do, in `bytes()`
    /// big-endian bytes.
    pub(crate) fn hash_to_scalar(&self, msg: &[&[u8]], dst: &[u8]) -> Vec<u8> {
        let [s] = &self.hash_to_field(msg, dst, 1, &self.n)[..] else {
            unreachable!()
        };
        self.be(s)
    }

    fn be(&self, x: &BigUint) -> Vec<u8> {
        let bytes = x.to_bytes_be();
        let mut out = vec![0; self.bytes() - bytes.len()];
        out.extend(bytes);
        out
    }

    fn inv(&self, x: &BigUint) -> BigUint {
        x.modpow(&(&self.p - 2u8), &self.p)
    }

    fn neg(&self, x: &BigUint) -> BigUint {
        (&self.p - x % &self.p) % &self.p
    }

    fn is_square(&self, x: &BigUint) -> bool {
        // Euler's criterion; zero is a square.
        let e = x.modpow(&((&self.p - 1u8) >> 1), &self.p);
        e == BigUint::from(1u8) || x % &self.p == BigUint::ZERO
    }

    /// The square root that is `x^((p + 1) / 4)`, for `p = 3 mod 4`.
    fn sqrt(&self, x: &BigUint) -> BigUint {
        let r = x.modpow(&((&self.p + 1u8) >> 2), &self.p);
        assert_eq!(&r * &r % &self.p, x % &self.p);
        r
    }

    fn sgn0(x: &BigUint) -> bool {
        x.bit(0)
    }

    /// `map_to_curve_simple_swu` (section 6.6.2), with `A = -3`.
    fn map_to_curve(&self, u: &BigUint) -> (BigUint, BigUint) {
        let p = &self.p;
        let a = self.neg(&BigUint::from(3u8));
        let z = self.neg(&BigUint::from(self.z));
        let u2 = u * u % p;
        let tv1 = (&z * &z % p * &u2 % p * &u2 + &z * &u2) % p;
        // `inv0`: zero maps to zero.
        let tv1 = if tv1 == BigUint::ZERO {
            tv1
        } else {
            self.inv(&tv1)
        };
        let x1 = if tv1 == BigUint::ZERO {
            &self.b * self.inv(&(&z * &a % p)) % p
        } else {
            self.neg(&self.b) * self.inv(&a) % p * (BigUint::from(1u8) + tv1) % p
        };
        let g = |x: &BigUint| (x * x % p * x + &a * x + &self.b) % p;
        let gx1 = g(&x1);
        let (x, y) = if self.is_square(&gx1) {
            (x1, self.sqrt(&gx1))
        } else {
            let x2 = &z * &u2 % p * &x1 % p;
            let y = self.sqrt(&g(&x2));
            (x2, y)
        };
        let y = if Self::sgn0(u) == Self::sgn0(&y) {
            y
        } else {
            self.neg(&y)
        };
        (x, y)
    }

    /// The sum of two affine points, `None` for infinity.
    fn add(&self, q0: &(BigUint, BigUint), q1: &(BigUint, BigUint)) -> Option<(BigUint, BigUint)> {
        let p = &self.p;
        let lambda = if q0.0 == q1.0 {
            if q0.1 != q1.1 || q0.1 == BigUint::ZERO {
                return None;
            }
            let a = self.neg(&BigUint::from(3u8));
            (BigUint::from(3u8) * &q0.0 * &q0.0 + a) % p
                * self.inv(&(BigUint::from(2u8) * &q0.1 % p))
                % p
        } else {
            (self.neg(&q0.1) + &q1.1) % p * self.inv(&((self.neg(&q0.0) + &q1.0) % p)) % p
        };
        let x = (&lambda * &lambda + self.neg(&q0.0) + self.neg(&q1.0)) % p;
        let y = (&lambda * ((self.neg(&x) + &q0.0) % p) + self.neg(&q0.1)) % p;
        Some((x, y))
    }

    /// `hash_to_curve` (section 3), for `msg` the concatenation of its parts,
    /// as an X9.62 uncompressed point. The cofactor is one. `None` is the
    /// point at infinity, which rind refuses.
    pub(crate) fn hash_to_curve(&self, msg: &[u8], dst: &[u8]) -> Option<Vec<u8>> {
        let u = self.hash_to_field(&[msg], dst, 2, &self.p);
        let (x, y) = self.add(&self.map_to_curve(&u[0]), &self.map_to_curve(&u[1]))?;
        let mut out = vec![4];
        out.extend(self.be(&x));
        out.extend(self.be(&y));
        Some(out)
    }

    /// The map alone to `u`, as an uncompressed point.
    pub(crate) fn map_to_curve_bytes(&self, u: &BigUint) -> Vec<u8> {
        let (x, y) = self.map_to_curve(u);
        [&[4][..], &self.be(&x), &self.be(&y)].concat()
    }
}
