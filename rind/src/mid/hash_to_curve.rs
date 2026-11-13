// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! [RFC 9380]'s hashing to P-256, P-384, and P-521: `expand_message_xmd`
//! over SHA-2, and the simplified SWU map, written once over [`Curve`].
//!
//! The map is the RFC's straight-line form (Appendix F.2), with the square
//! root ratio for `p = 3 mod 4` (Appendix F.2.1.2): it has no branch or
//! index on its input, and selects with `bignum_mux`. Each curve runs it on
//! the field arithmetic its key agreement already does, s2n-bignum's
//! verified routines or, on armv7 and the portable backend, fiat-crypto's,
//! so their proofs cover each step; the composition is the RFC's, checked
//! by its vectors and against aws-lc and RustCrypto.
//!
//! [RFC 9380]: https://www.rfc-editor.org/rfc/rfc9380.html

use crate::error::Error;
use crate::mid::sha2::{Sha256Context, Sha384Context, Sha512Context};

/// A SHA-2 hash, as `expand_message_xmd` takes it.
pub(crate) trait Xmd {
    /// The input block size, `s_in_bytes`.
    const BLOCK: usize;

    /// The output size, `b_in_bytes`.
    const OUTPUT: usize;

    fn new() -> Self;

    fn update(&mut self, bytes: &[u8]);

    /// Writes the hash to the start of `out`.
    fn finish_into(&self, out: &mut [u8; MAX_OUTPUT]);
}

const MAX_OUTPUT: usize = Sha512Context::OUTPUT_SZ;

impl Xmd for Sha256Context {
    const BLOCK: usize = Self::BLOCK_SZ;
    const OUTPUT: usize = Self::OUTPUT_SZ;

    fn new() -> Self {
        Self::new()
    }

    fn update(&mut self, bytes: &[u8]) {
        self.update(bytes);
    }

    fn finish_into(&self, out: &mut [u8; MAX_OUTPUT]) {
        out[..Self::OUTPUT].copy_from_slice(&self.finish());
    }
}

impl Xmd for Sha384Context {
    const BLOCK: usize = Sha512Context::BLOCK_SZ;
    const OUTPUT: usize = Self::OUTPUT_SZ;

    fn new() -> Self {
        Self::new()
    }

    fn update(&mut self, bytes: &[u8]) {
        self.update(bytes);
    }

    fn finish_into(&self, out: &mut [u8; MAX_OUTPUT]) {
        out[..Self::OUTPUT].copy_from_slice(&self.finish());
    }
}

impl Xmd for Sha512Context {
    const BLOCK: usize = Self::BLOCK_SZ;
    const OUTPUT: usize = Self::OUTPUT_SZ;

    fn new() -> Self {
        Self::new()
    }

    fn update(&mut self, bytes: &[u8]) {
        self.update(bytes);
    }

    fn finish_into(&self, out: &mut [u8; MAX_OUTPUT]) {
        *out = self.finish();
    }
}

/// Fills `out` with RFC 9380's `expand_message_xmd(msg, dst, out.len())`
/// over `H` (section 5.3.1), for `msg` the concatenation of its parts.
///
/// A `dst` over 255 bytes is hashed down, as section 5.3.3 says. An empty
/// `dst`, which the RFC forbids, and an `out` longer than 255 hashes are
/// refused, as aws-lc refuses them.
pub(crate) fn expand_message_xmd<H: Xmd>(
    msg: &[&[u8]],
    dst: &[u8],
    out: &mut [u8],
) -> Result<(), Error> {
    let len = u16::try_from(out.len()).map_err(|_| Error::WrongLength)?;
    if dst.is_empty() || out.len().div_ceil(H::OUTPUT) > 255 {
        return Err(Error::WrongLength);
    }

    let mut oversize = [0u8; MAX_OUTPUT];
    let dst = match dst.len() {
        ..=255 => dst,
        _ => {
            let mut h = H::new();
            h.update(b"H2C-OVERSIZE-DST-");
            h.update(dst);
            h.finish_into(&mut oversize);
            &oversize[..H::OUTPUT]
        }
    };
    // unwrap: `dst` is at most 255 bytes now.
    let dst_len = [u8::try_from(dst.len()).unwrap()];

    let mut h = H::new();
    h.update(&[0; 128][..H::BLOCK]);
    for part in msg {
        h.update(part);
    }
    h.update(&len.to_be_bytes());
    h.update(&[0]);
    h.update(dst);
    h.update(&dst_len);
    let mut b_0 = [0u8; MAX_OUTPUT];
    h.finish_into(&mut b_0);

    // `b_i` hashes `b_0 ^ b_(i - 1)`, and `b_1` hashes `b_0` alone, as
    // `b_i` starts zero.
    let mut b_i = [0u8; MAX_OUTPUT];
    for (i, chunk) in (1..=255u8).zip(out.chunks_mut(H::OUTPUT)) {
        for (b, b0) in b_i.iter_mut().zip(b_0) {
            *b ^= b0;
        }
        let mut h = H::new();
        h.update(&b_i[..H::OUTPUT]);
        h.update(&[i]);
        h.update(dst);
        h.update(&dst_len);
        h.finish_into(&mut b_i);
        chunk.copy_from_slice(&b_i[..chunk.len()]);
    }
    Ok(())
}

/// A NIST curve, `y^2 = x^3 - 3x + B` over a field of prime order
/// `p = 3 mod 4`, and its RFC 9380 suite, given by its field element type.
///
/// Every element is fully reduced. The constants and arithmetic are in
/// whatever form the type keeps, Montgomery's for P-256 and P-384.
pub(crate) trait Curve: Copy {
    /// `L`, the bytes `hash_to_field` reduces to one element.
    const L: usize;

    const ZERO: Self;
    const ONE: Self;
    const A: Self;
    const B: Self;

    /// The suite's `Z`, the non-square the map is built on.
    const Z: Self;

    /// A square root of `-Z`, the square root ratio's `c2`.
    const SQRT_MINUS_Z: Self;

    /// The element `bytes`, an `L`-byte big-endian integer, is congruent to.
    fn from_wide(bytes: &[u8]) -> Self;

    fn mul(&self, other: &Self) -> Self;

    fn sqr(&self) -> Self;

    fn add(&self, other: &Self) -> Self;

    fn neg(&self) -> Self;

    /// `self^((p - 3) / 4)`, the square root ratio's `c1`, by an addition
    /// chain.
    fn pow_c1(&self) -> Self;

    /// The parity of this element's integer value, RFC 9380's `sgn0`.
    fn sgn0(&self) -> u8;

    /// Whether `self` and `other` are equal, in constant time.
    fn ct_eq(&self, other: &Self) -> bool;

    /// `other` if `choice`, else `self`, in constant time.
    fn select(&self, other: &Self, choice: bool) -> Self;

    /// `p + q`, by the curve's Jacobian addition, for points neither equal,
    /// opposite, nor at infinity.
    fn add_points(p: &[Self; 3], q: &[Self; 3]) -> [Self; 3];

    /// `2p`, by the curve's Jacobian doubling.
    fn double_point(p: &[Self; 3]) -> [Self; 3];
}

/// The largest `L`, P-521's.
const MAX_L: usize = 98;

/// RFC 9380's `hash_to_curve` for `C`'s suite over `H`, as a Jacobian point
/// `(X, Y, Z)`, which is affine `(X / Z^2, Y / Z^3)`, or infinity if `Z` is
/// zero.
///
/// The cofactor is one, so `clear_cofactor` does nothing.
pub(crate) fn hash_to_curve<C: Curve, H: Xmd>(msg: &[u8], dst: &[u8]) -> Result<[C; 3], Error> {
    let mut uniform = [0u8; 2 * MAX_L];
    let uniform = &mut uniform[..2 * C::L];
    expand_message_xmd::<H>(&[msg], dst, uniform)?;
    let (u0, u1) = uniform.split_at(C::L);
    let q0 = map_to_curve(&C::from_wide(u0));
    let q1 = map_to_curve(&C::from_wide(u1));
    Ok(sum(&q0, &q1))
}

/// RFC 9380's `map_to_curve_simple_swu` for an `A` of -3, by its
/// straight-line form (Appendix F.2), as a Jacobian point never at infinity.
///
/// Rather than divide `x` by `tv4`, this returns `(x * tv4, y * tv4^3,
/// tv4)`, as aws-lc does: `tv4` is `A` times `Z` or a nonzero `-tv2`, so
/// never zero.
fn map_to_curve<C: Curve>(u: &C) -> [C; 3] {
    let tv1 = C::Z.mul(&u.sqr());
    let tv2 = tv1.sqr().add(&tv1);
    let tv3 = C::B.mul(&tv2.add(&C::ONE));
    let tv4 = C::A.mul(&C::Z.select(&tv2.neg(), !tv2.ct_eq(&C::ZERO)));
    let tv6 = tv4.sqr();
    let tv5 = C::A.mul(&tv6);
    let tv2 = tv3.sqr().add(&tv5).mul(&tv3);
    let tv6 = tv6.mul(&tv4);
    let tv2 = tv2.add(&C::B.mul(&tv6));
    let x = tv1.mul(&tv3);
    let (is_gx1_square, y1) = sqrt_ratio(&tv2, &tv6);
    let y = tv1.mul(u).mul(&y1);
    let x = x.select(&tv3, is_gx1_square);
    let y = y.select(&y1, is_gx1_square);
    let y = y.neg().select(&y, u.sgn0() == y.sgn0());
    [x.mul(&tv4), y.mul(&tv6), tv4]
}

/// RFC 9380's `sqrt_ratio` for `p = 3 mod 4` (Appendix F.2.1.2): whether
/// `u / v` is square, and its root if so, else the root of `Z * u / v`.
fn sqrt_ratio<C: Curve>(u: &C, v: &C) -> (bool, C) {
    let tv2 = u.mul(v);
    let tv1 = v.sqr().mul(&tv2);
    let y1 = tv1.pow_c1().mul(&tv2);
    let y2 = y1.mul(&C::SQRT_MINUS_Z);
    let is_qr = y1.sqr().mul(v).ct_eq(u);
    (is_qr, y2.select(&y1, is_qr))
}

/// `q0 + q1`, for Jacobian points not at infinity, in constant time.
///
/// The curves' additions are proven only for points neither equal nor,
/// for P-521's, opposite, so equal points take the doubling and opposite
/// ones infinity, compared by their coordinates scaled to a common `Z`.
fn sum<C: Curve>(q0: &[C; 3], q1: &[C; 3]) -> [C; 3] {
    let [x0, y0, z0] = q0;
    let [x1, y1, z1] = q1;
    let (z0z0, z1z1) = (z0.sqr(), z1.sqr());
    let same_x = x0.mul(&z1z1).ct_eq(&x1.mul(&z0z0));
    let same_y = y0.mul(&z1z1.mul(z1)).ct_eq(&y1.mul(&z0z0.mul(z0)));

    let added = C::add_points(q0, q1);
    let doubled = C::double_point(q0);
    let same = same_x & same_y;
    let opposite = same_x & !same_y;
    let [x, y, z] = [0, 1, 2].map(|i| added[i].select(&doubled[i], same));
    [x, y, z.select(&C::ZERO, opposite)]
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
pub(crate) mod tests {
    use std::fs::File;
    use std::io::BufReader;

    use serde::Deserialize;

    use super::*;
    use crate::low;

    #[derive(Deserialize)]
    struct ExpandFile {
        #[serde(rename = "DST")]
        dst: String,
        hash: String,
        tests: Vec<ExpandTest>,
    }

    #[derive(Deserialize)]
    struct ExpandTest {
        msg: String,
        #[serde(with = "hex::serde")]
        uniform_bytes: Vec<u8>,
    }

    /// Reads `thirdparty/vectors/rfc9380/<name>.json`.
    pub(crate) fn vectors<T: for<'de> Deserialize<'de>>(name: &str) -> T {
        let path = format!(
            "{}/../thirdparty/vectors/rfc9380/{name}.json",
            env!("CARGO_MANIFEST_DIR")
        );
        serde_json::from_reader(BufReader::new(File::open(&path).unwrap())).unwrap()
    }

    fn expand(hash: &str, msg: &[u8], dst: &[u8], out: &mut [u8]) -> Result<(), Error> {
        let _entry = low::Entry::new_public();
        match hash {
            "SHA256" => expand_message_xmd::<Sha256Context>(&[msg], dst, out),
            "SHA384" => expand_message_xmd::<Sha384Context>(&[msg], dst, out),
            "SHA512" => expand_message_xmd::<Sha512Context>(&[msg], dst, out),
            _ => unreachable!(),
        }
    }

    /// RFC 9380's Appendix K.1 and K.3, and the long-DST cases beside them.
    #[test]
    fn expand_message_xmd_vectors() {
        let mut count = 0;
        for name in [
            "expand_message_xmd_SHA256_38",
            "expand_message_xmd_SHA256_256",
            "expand_message_xmd_SHA512_38",
        ] {
            let file: ExpandFile = vectors(name);
            for test in file.tests {
                let mut out = vec![0; test.uniform_bytes.len()];
                expand(
                    &file.hash,
                    test.msg.as_bytes(),
                    file.dst.as_bytes(),
                    &mut out,
                )
                .unwrap();
                assert_eq!(out, test.uniform_bytes);
                count += 1;
            }
        }
        assert_eq!(count, 30);
    }

    #[test]
    fn expand_message_xmd_lengths() {
        for hash in ["SHA256", "SHA384", "SHA512"] {
            let size = match hash {
                "SHA256" => 32,
                "SHA384" => 48,
                _ => 64,
            };
            let mut out = vec![0; 255 * size + 1];
            assert_eq!(
                expand(hash, b"msg", b"", &mut out[..32]),
                Err(Error::WrongLength)
            );
            assert_eq!(
                expand(hash, b"msg", b"d", &mut out),
                Err(Error::WrongLength)
            );
            let mut longest = vec![0; 255 * size];
            expand(hash, b"msg", b"d", &mut longest).unwrap();

            // Each output is a prefix of a longer one's within a hash, but
            // the length is hashed in, so not across lengths.
            let mut short = [0; 31];
            expand(hash, b"msg", b"d", &mut short).unwrap();
            assert_ne!(short[..], longest[..31]);
            expand(hash, b"msg", b"d", &mut []).unwrap();
        }
    }

    /// A 256-byte DST is hashed; a 255-byte one is not.
    #[test]
    fn expand_message_xmd_oversize_dst() {
        let dst = [b'D'; 256];
        let mut hashed = [0; 32];
        let mut short = [0; 32];
        let mut long = [0; 32];
        let _entry = low::Entry::new_public();
        let mut h = Sha256Context::new();
        h.update(b"H2C-OVERSIZE-DST-");
        h.update(&dst);
        expand_message_xmd::<Sha256Context>(&[b"msg"], &h.finish(), &mut hashed).unwrap();
        expand_message_xmd::<Sha256Context>(&[b"msg"], &dst, &mut long).unwrap();
        expand_message_xmd::<Sha256Context>(&[b"msg"], &dst[..255], &mut short).unwrap();
        assert_eq!(long, hashed);
        assert_ne!(short, hashed);
    }

    /// One suite's file of RFC 9380's Appendix J vectors.
    #[derive(Deserialize)]
    pub(crate) struct SuiteFile {
        pub(crate) dst: String,
        pub(crate) vectors: Vec<SuiteVector>,
    }

    #[derive(Deserialize)]
    pub(crate) struct SuiteVector {
        pub(crate) msg: String,
        #[serde(rename = "P")]
        pub(crate) p: Point,
        pub(crate) u: [String; 2],
        #[serde(rename = "Q0")]
        pub(crate) q0: Point,
        #[serde(rename = "Q1")]
        pub(crate) q1: Point,
    }

    #[derive(Deserialize)]
    pub(crate) struct Point {
        pub(crate) x: String,
        pub(crate) y: String,
    }

    impl Point {
        /// The X9.62 uncompressed encoding, each coordinate `len` bytes.
        pub(crate) fn uncompressed(&self, len: usize) -> Vec<u8> {
            let mut out = vec![4];
            out.extend(be(&self.x, len));
            out.extend(be(&self.y, len));
            out
        }
    }

    /// The big-endian `len` bytes of a `0x`-prefixed hex integer.
    pub(crate) fn be(hex: &str, len: usize) -> Vec<u8> {
        let hex = hex.strip_prefix("0x").unwrap();
        let bytes = hex::decode(format!("{hex:0>width$}", width = 2 * len)).unwrap();
        assert_eq!(bytes.len(), len);
        bytes
    }

    /// Checks `C`'s suite against its Appendix J vectors, each step of the
    /// map and the sum, given each point's affine coordinates.
    pub(crate) fn check_suite<C: Curve, H: Xmd>(
        name: &str,
        bytes: usize,
        affine: impl Fn(&[C; 3]) -> Vec<u8>,
    ) {
        let file: SuiteFile = vectors(name);
        let _entry = low::Entry::new_public();
        for v in &file.vectors {
            let mut uniform = vec![0; 2 * C::L];
            expand_message_xmd::<H>(&[v.msg.as_bytes()], file.dst.as_bytes(), &mut uniform)
                .unwrap();
            let u: Vec<_> = uniform.chunks(C::L).map(C::from_wide).collect();
            for (u, expect) in u.iter().zip(&v.u) {
                // `(u, u)` is not on the curve, but encodes `u` all the same.
                let point = Point {
                    x: expect.clone(),
                    y: expect.clone(),
                };
                assert_eq!(affine(&[*u, *u, C::ONE]), point.uncompressed(bytes));
            }
            assert_eq!(affine(&map_to_curve(&u[0])), v.q0.uncompressed(bytes));
            assert_eq!(affine(&map_to_curve(&u[1])), v.q1.uncompressed(bytes));
            let p = hash_to_curve::<C, H>(v.msg.as_bytes(), file.dst.as_bytes()).unwrap();
            assert_eq!(affine(&p), v.p.uncompressed(bytes));
        }
        assert_eq!(file.vectors.len(), 5);
    }

    /// `sum` doubles equal points and gives infinity for opposite ones,
    /// whatever `Z` each has.
    pub(crate) fn check_sum<C: Curve>(affine: impl Fn(&[C; 3]) -> Vec<u8>) {
        let _entry = low::Entry::new_public();
        let q = map_to_curve(&C::from_wide(&[7; MAX_L][..C::L]));
        let r = map_to_curve(&C::from_wide(&[9; MAX_L][..C::L]));
        // `q` again, under another `Z`.
        let k = C::ONE.add(&C::ONE).add(&C::ONE);
        let (k2, k3) = (k.sqr(), k.sqr().mul(&k));
        let scaled = [q[0].mul(&k2), q[1].mul(&k3), q[2].mul(&k)];
        let neg = [scaled[0], scaled[1].neg(), scaled[2]];

        assert_eq!(affine(&sum(&q, &scaled)), affine(&C::double_point(&q)));
        assert!(sum(&q, &neg)[2].ct_eq(&C::ZERO));
        assert_eq!(affine(&sum(&q, &r)), affine(&C::add_points(&q, &r)));
        assert_eq!(affine(&sum(&q, &r)), affine(&sum(&r, &q)));
    }

    /// `pow_c1` raises to `(p - 3) / 4`: one more factor gives
    /// `(p + 1) / 4`, which `sqrt_candidate` raises to.
    pub(crate) fn check_pow_c1<C: Curve>(sqrt_candidate: impl Fn(&C) -> C) {
        let _entry = low::Entry::new_public();
        for seed in 1..=8u8 {
            let x = C::from_wide(&[seed; MAX_L][..C::L]);
            assert!(x.pow_c1().mul(&x).ct_eq(&sqrt_candidate(&x)));
        }
    }

    /// `from_wide` against Horner's rule, `r = 256r + b` for each byte, on
    /// the extremes and random inputs.
    pub(crate) fn check_from_wide<C: Curve>() {
        let _entry = low::Entry::new_public();
        let mut b256 = C::ONE;
        for _ in 0..8 {
            b256 = b256.add(&b256);
        }
        let byte = |b: u8| {
            let mut r = C::ZERO;
            for bit in (0..8).rev() {
                r = r.add(&r);
                if (b >> bit) & 1 == 1 {
                    r = r.add(&C::ONE);
                }
            }
            r
        };
        let mut inputs = vec![vec![0; C::L], vec![0xff; C::L]];
        for _ in 0..32 {
            let mut random = vec![0; C::L];
            crate::mid::rng::RandomSource::fill(&mut crate::mid::rng::SystemRandom, &mut random)
                .unwrap();
            inputs.push(random);
        }
        for input in inputs {
            let horner = input
                .iter()
                .fold(C::ZERO, |r, &b| r.mul(&b256).add(&byte(b)));
            assert!(C::from_wide(&input).ct_eq(&horner));
        }
    }

    /// Hashes a secret message, so `admin/ctgrind` checks nothing branches
    /// on or indexes by it, and the map's input, its `u`.
    pub(crate) fn hashes_in_constant_time<C: Curve, H: Xmd>(public: impl Fn(&[C; 3]) -> Vec<u8>) {
        let _entry = low::Entry::new_secret();
        for msg in [&b""[..], b"abc", &[0xff; 200]] {
            let msg = msg.to_vec();
            low::ct::secret_slice(&msg);
            let p = hash_to_curve::<C, H>(&msg, b"QUUX-V01-CS02").unwrap();
            public(&p);
        }
    }
}
