// Copyright (c) 2020 Peter Dettman
// Copyright (c) 2013 Pieter Wuille
// SPDX-License-Identifier: MIT

//! The s2n-bignum routines `low::PosInt` uses to invert modulo an odd number
//! and to test coprimality, with their contracts, in portable Rust over
//! limbs of the width the parent module picks, for armv7 and the portable
//! backend.
//!
//! Both run Bernstein and Yang's safegcd: libsecp256k1's constant-time
//! `secp256k1_modinv32` and `secp256k1_modinv64`, from `src/modinv32_impl.h`
//! and `src/modinv64_impl.h`, generalised from 256 bits to any length. Its
//! `doc/safegcd_implementation.md` derives the code step by step from the
//! paper. Each batch of `B` divsteps, two bits short of a limb, runs on the
//! bottom limbs alone and gives a matrix of entries at most 2^B in
//! magnitude, which one pass per value then applies to the whole of `f` and
//! `g`, and, for the inverse, of `d` and `e` modulo `m`. Values are signed,
//! in limbs of `B` bits below a signed top limb, so each product of a limb
//! and a matrix entry fits `SignedWide` with room for the sums.
//!
//! The steps are half-delta divsteps, whose count Wuille's safegcd-bounds
//! (`genproofhd.md`) proves, partly by computer, for any `0 <= f, g <= M`:
//! at most floor((45907 log2(M) + 30179) / 19929), so for values below
//! 2^(64k) that with 64k for log2(M), as crypto-bigint takes it. Steps past
//! the gcd leave `f`, `g`, `d`, and `e` as they are, so batches round up.
//!
//! Each runs in time that depends only on its lengths, never on its values:
//! loops run a count fixed by those, and selects are masks, kept from the
//! compiler as libsecp256k1 keeps them in `volatile`s. Arithmetic on values
//! wraps, though the bounds rule out overflow, since a debug build's
//! overflow check would branch on them.

use core::hint::black_box;

use super::super::bignum::{MAX_WORDS, nonzero, select, word};
use super::{Limb, Signed, SignedWide};

/// The bits of each signed limb below the top one, and the divsteps a batch
/// takes: a batch's matrix entries reach 2^B in magnitude, so each pass's
/// sum of two products with a limb stays within `SignedWide`.
const B: u32 = Limb::BITS - 2;

/// A signed limb's low `B` bits.
const LOW: Signed = (1 << B) - 1;

/// Signed limbs for `MAX_WORDS`.
const MAX_SIGNED: usize = signed_len(MAX_WORDS);

/// Signed limbs for values of `k` words, with room for `d` and `e`, which
/// stay above `-2m`: `B` bits a limb for 64k + 2 bits, leaving the top limb
/// below 2^(B - 1) in magnitude.
const fn signed_len(k: usize) -> usize {
    (64 * k + 2).div_ceil(B as usize)
}

/// Batches of `B` divsteps that find the gcd of values of `k` words.
const fn batches(k: usize) -> usize {
    ((45907 * 64 * k + 30179) / 19929).div_ceil(B as usize)
}

/// Invert modulo m, z = (1/a) mod b, assuming b is an odd number > 1, coprime a
///
/// Inputs a[k], b[k]; output z[k]; temporary buffer t[>=3*k]
///
/// `_t` is s2n-bignum's scratch space, which this does not need.
pub(crate) fn bignum_modinv(z: &mut [u64], a: &[u64], b: &[u64], _t: &mut [u64]) {
    let k = b.len();
    assert!(a.len() <= k && z.len() == k);
    let n = signed_len(k);
    let mut buf = [[0; MAX_SIGNED]; 5];
    let [m, f, g, d, e] = &mut buf;
    let (m, f, g, d, e) = (
        &mut m[..n],
        &mut f[..n],
        &mut g[..n],
        &mut d[..n],
        &mut e[..n],
    );
    to_signed(b, m);
    f.copy_from_slice(m);
    to_signed(a, g);
    e[0] = 1;
    let m_inv = inverse(m[0] as Limb);

    // f = m and g = a, with d * a = f and e * a = g (mod m) throughout. Once
    // g is zero, f is +-gcd(a, m) = +-1, so +-d is 1/a. zeta is -(delta +
    // 1/2), from delta = 1/2.
    let mut zeta = -1;
    for _ in 0..batches(k) {
        let t;
        (zeta, t) = divsteps(zeta, f[0], g[0]);
        update_de(d, e, &t, m, m_inv);
        update_fg(f, g, &t);
    }
    normalize(d, f[n - 1], m);
    from_signed(d, z);
}

/// Test bignums for coprimality, gcd(x,y) = 1
///
/// Inputs x[m], y[n]; output function return; temporary buffer t[>=2*max(m,n)]
///
/// `_t` is s2n-bignum's scratch space, which this does not need.
pub(crate) fn bignum_coprime(x: &[u64], y: &[u64], _t: &mut [u64]) -> bool {
    let k = x.len().max(y.len());
    let n = signed_len(k);

    // One of x and y must be odd, or 2 divides both. The odd one is f, as
    // divsteps take it, and |f| ends as the gcd.
    let x_odd = word(x, 0) & 1;
    let y_odd = word(y, 0) & 1;
    let mut words = [[0; MAX_WORDS]; 2];
    let [fw, gw] = &mut words;
    for i in 0..k {
        fw[i] = select(x_odd, word(x, i), word(y, i));
        gw[i] = select(x_odd, word(y, i), word(x, i));
    }
    let mut buf = [[0; MAX_SIGNED]; 2];
    let [f, g] = &mut buf;
    let (f, g) = (&mut f[..n], &mut g[..n]);
    to_signed(&fw[..k], f);
    to_signed(&gw[..k], g);

    let mut zeta = -1;
    for _ in 0..batches(k) {
        let t;
        (zeta, t) = divsteps(zeta, f[0], g[0]);
        update_fg(f, g, &t);
    }

    // +1 and -1 are the only values with these limbs.
    let (mut plus, mut minus) = (0, 0);
    for (i, limb) in f.iter().enumerate() {
        let minus_one = if i + 1 == n { -1 } else { LOW };
        plus |= (limb ^ Signed::from(i == 0)) as Limb;
        minus |= (limb ^ minus_one) as Limb;
    }
    let one = (nonzero(u64::from(plus)) & nonzero(u64::from(minus))) ^ 1;
    one & (x_odd | y_odd) == 1
}

/// `B` divsteps on the bottom limbs of `f` and `g` from `zeta`, returning
/// the new `zeta` and the matrix `[u, v, q, r]` that takes `[f, g]` to
/// `2^B` times their new values: libsecp256k1's `divsteps_30` and
/// `divsteps_62`.
fn divsteps(mut zeta: Signed, f0: Signed, g0: Signed) -> (Signed, [Signed; 4]) {
    // Each is a signed value of magnitude at most 2^B, carried unsigned so
    // the shifts are defined.
    let (mut u, mut v, mut q, mut r): (Limb, Limb, Limb, Limb) = (1, 0, 0, 1);
    let (mut f, mut g) = (f0 as Limb, g0 as Limb);
    for _ in 0..B {
        // All ones where zeta < 0, that is, delta > 0, and where g is odd.
        let c1 = black_box((zeta >> (Signed::BITS - 1)) as Limb);
        let c2 = black_box(Limb::wrapping_sub(0, g & 1));
        // -f, -u, -v where delta > 0, added to g, q, r where g is odd.
        let x = (f ^ c1).wrapping_sub(c1);
        let y = (u ^ c1).wrapping_sub(c1);
        let z = (v ^ c1).wrapping_sub(c1);
        g = g.wrapping_add(x & c2);
        q = q.wrapping_add(y & c2);
        r = r.wrapping_add(z & c2);
        // Where both: zeta := -zeta - 2, and f, u, v take g's old values,
        // which adding the new g, q, r gives. Else zeta := zeta - 1.
        let c = c1 & c2;
        zeta = (zeta ^ c as Signed).wrapping_sub(1);
        f = f.wrapping_add(g & c);
        u = u.wrapping_add(q & c);
        v = v.wrapping_add(r & c);
        g >>= 1;
        u <<= 1;
        v <<= 1;
    }
    (zeta, [u as Signed, v as Signed, q as Signed, r as Signed])
}

/// `[f, g] := t [f, g] / 2^B`, which is exact: libsecp256k1's
/// `update_fg_30` and `update_fg_62`.
fn update_fg(f: &mut [Signed], g: &mut [Signed], t: &[Signed; 4]) {
    let [u, v, q, r] = t.map(SignedWide::from);
    let mut cf = mul(u, f[0]).wrapping_add(mul(v, g[0])) >> B;
    let mut cg = mul(q, f[0]).wrapping_add(mul(r, g[0])) >> B;
    for i in 1..f.len() {
        cf = cf.wrapping_add(mul(u, f[i])).wrapping_add(mul(v, g[i]));
        cg = cg.wrapping_add(mul(q, f[i])).wrapping_add(mul(r, g[i]));
        f[i - 1] = cf as Signed & LOW;
        g[i - 1] = cg as Signed & LOW;
        cf >>= B;
        cg >>= B;
    }
    let n = f.len();
    f[n - 1] = cf as Signed;
    g[n - 1] = cg as Signed;
}

/// `[d, e] := t [d, e] / 2^B mod m`, for `d` and `e` in (-2m, m), which
/// stay there, where `m_inv` is `m^-1 mod 2^B`: libsecp256k1's
/// `update_de_30` and `update_de_62`.
fn update_de(d: &mut [Signed], e: &mut [Signed], t: &[Signed; 4], m: &[Signed], m_inv: Limb) {
    let n = d.len();
    let [u, v, q, r] = *t;
    // Multiples of m to add: u and q where d is negative, v and r where e is,
    // then less what clears the bottom B bits of the sum.
    let sd = d[n - 1] >> (Signed::BITS - 1);
    let se = e[n - 1] >> (Signed::BITS - 1);
    let mut md = (u & sd).wrapping_add(v & se);
    let mut me = (q & sd).wrapping_add(r & se);
    let [u, v, q, r] = t.map(SignedWide::from);
    let mut cd = mul(u, d[0]).wrapping_add(mul(v, e[0]));
    let mut ce = mul(q, d[0]).wrapping_add(mul(r, e[0]));
    md = md.wrapping_sub((m_inv.wrapping_mul(cd as Limb).wrapping_add(md as Limb) as Signed) & LOW);
    me = me.wrapping_sub((m_inv.wrapping_mul(ce as Limb).wrapping_add(me as Limb) as Signed) & LOW);
    let (md, me) = (SignedWide::from(md), SignedWide::from(me));
    cd = cd.wrapping_add(mul(md, m[0])) >> B;
    ce = ce.wrapping_add(mul(me, m[0])) >> B;
    for i in 1..n {
        cd = cd.wrapping_add(mul(u, d[i])).wrapping_add(mul(v, e[i]));
        ce = ce.wrapping_add(mul(q, d[i])).wrapping_add(mul(r, e[i]));
        cd = cd.wrapping_add(mul(md, m[i]));
        ce = ce.wrapping_add(mul(me, m[i]));
        d[i - 1] = cd as Signed & LOW;
        e[i - 1] = ce as Signed & LOW;
        cd >>= B;
        ce >>= B;
    }
    d[n - 1] = cd as Signed;
    e[n - 1] = ce as Signed;
}

/// `r := r mod m`, negated first where `sign` is negative, for `r` in (-2m,
/// m), leaving every limb in [0, 2^B): libsecp256k1's `normalize_30` and
/// `normalize_62`.
fn normalize(r: &mut [Signed], sign: Signed, m: &[Signed]) {
    let n = r.len();
    let add = black_box(r[n - 1] >> (Signed::BITS - 1));
    for (r, m) in r.iter_mut().zip(m) {
        *r = r.wrapping_add(m & add);
    }
    let negate = black_box(sign >> (Signed::BITS - 1));
    for r in r.iter_mut() {
        *r = (*r ^ negate).wrapping_sub(negate);
    }
    carry(r);
    // r is in (-m, m) now; add m once more if it is negative.
    let add = black_box(r[n - 1] >> (Signed::BITS - 1));
    for (r, m) in r.iter_mut().zip(m) {
        *r = r.wrapping_add(m & add);
    }
    carry(r);
}

/// Moves each limb's bits above `B` into the next, leaving it in [0, 2^B).
fn carry(r: &mut [Signed]) {
    for i in 1..r.len() {
        r[i] = r[i].wrapping_add(r[i - 1] >> B);
        r[i - 1] &= LOW;
    }
}

/// `a * b`.
fn mul(a: SignedWide, b: Signed) -> SignedWide {
    a.wrapping_mul(SignedWide::from(b))
}

/// `m^-1 mod 2^B`, for an odd `m`.
fn inverse(m: Limb) -> Limb {
    // Correct to 5 bits, then Newton's iteration doubles that each time.
    let mut inv = m.wrapping_mul(3) ^ 2;
    for _ in 0..Limb::BITS.ilog2() - 2 {
        inv = inv.wrapping_mul(Limb::wrapping_sub(2, m.wrapping_mul(inv)));
    }
    inv
}

/// `x`'s bits in `B`-bit limbs, low first, as `out` holds them.
fn to_signed(x: &[u64], out: &mut [Signed]) {
    for (i, out) in out.iter_mut().enumerate() {
        let (at, shift) = ((B as usize * i) / 64, (B as usize * i) % 64);
        let bits =
            word(x, at) >> shift | word(x, at + 1).checked_shl(64 - shift as u32).unwrap_or(0);
        *out = bits as Signed & LOW;
    }
}

/// The value of `x`, whose limbs are all in [0, 2^B), in the words of `z`.
fn from_signed(x: &[Signed], z: &mut [u64]) {
    z.fill(0);
    for (i, limb) in x.iter().enumerate() {
        let (at, shift) = ((B as usize * i) / 64, (B as usize * i) % 64);
        let limb = u64::from(*limb as Limb);
        if let Some(z) = z.get_mut(at) {
            *z |= limb << shift;
        }
        if let Some(z) = z.get_mut(at + 1) {
            *z |= limb.checked_shr(64 - shift as u32).unwrap_or(0);
        }
    }
}

/// Checks each routine against num-bigint and aws-lc's vectors on every
/// backend, and against s2n-bignum's word for word on x86_64 and aarch64.
///
/// The values are marked secret, so under `admin/ctgrind` these also check
/// each routine is constant time in them.
#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use num_bigint::BigUint;
    use proptest::prelude::*;

    use super::*;
    use crate::low::ct::{into_public, public_slice, secret_slice};
    use crate::test::file_test;

    /// A word: random, or one where a carry or sign goes wrong.
    fn any_word() -> impl Strategy<Value = u64> {
        prop_oneof![
            4 => any::<u64>(),
            1 => Just(0),
            1 => Just(1),
            1 => Just(u64::MAX),
            1 => Just(1 << 63),
        ]
    }

    /// An odd modulus above one of up to `max` words, its top words possibly
    /// zero, and a value as wide, possibly above it.
    fn modulus(max: usize) -> impl Strategy<Value = (Vec<u64>, Vec<u64>)> {
        (1..=max).prop_flat_map(|k| {
            let m = prop::collection::vec(any_word(), k).prop_map(|mut m| {
                m[0] |= 1;
                if m[1..].iter().all(|w| *w == 0) && m[0] == 1 {
                    m[0] = 3;
                }
                m
            });
            (m, prop::collection::vec(any_word(), k))
        })
    }

    fn big(x: &[u64]) -> BigUint {
        BigUint::from_bytes_le(&x.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<_>>())
    }

    /// `x` in `k` words.
    fn words(x: &BigUint, k: usize) -> Vec<u64> {
        let mut words = x.to_u64_digits();
        words.resize(k, 0);
        words
    }

    fn gcd(mut a: BigUint, mut b: BigUint) -> BigUint {
        while b != BigUint::ZERO {
            (a, b) = (b.clone(), a % b);
        }
        a
    }

    /// `x` marked secret.
    fn secret(x: &[u64]) -> Vec<u64> {
        let x = x.to_vec();
        secret_slice(&x);
        x
    }

    /// The inverse, made public to compare.
    fn modinv(a: &[u64], m: &[u64]) -> Vec<u64> {
        let mut z = vec![0; m.len()];
        bignum_modinv(&mut z, &secret(a), &secret(m), &mut []);
        public_slice(&z);
        z
    }

    fn coprime(x: &[u64], y: &[u64]) -> bool {
        into_public(bignum_coprime(&secret(x), &secret(y), &mut []))
    }

    proptest! {
        #[test]
        fn inverse((m, a) in modulus(20)) {
            let (bm, ba) = (big(&m), big(&a));
            let want = ba.modinv(&bm);
            prop_assert_eq!(coprime(&a, &m), want.is_some());
            if let Some(want) = want {
                prop_assert_eq!(modinv(&a, &m), words(&want, m.len()));
            }
        }

        #[test]
        fn gcd_one(x in prop::collection::vec(any_word(), 0..6), y in prop::collection::vec(any_word(), 0..6)) {
            prop_assert_eq!(coprime(&x, &y), gcd(big(&x), big(&y)) == BigUint::from(1u8));
        }
    }

    /// aws-lc's `ModInv` vectors with an odd modulus above one, each `A`
    /// as is and reduced.
    #[test]
    fn aws_lc() {
        let mut ran = 0;
        for test in file_test::tests("aws-lc/crypto/fipsmodule/bn/test/mod_inv_tests.txt") {
            let value = |name| BigUint::parse_bytes(test.str(name).as_bytes(), 16).unwrap();
            let (m, a, want) = (value("M"), value("A"), value("ModInv"));
            if !m.bit(0) || m == BigUint::from(1u8) {
                continue;
            }
            let k = m.to_u64_digits().len();
            let (mw, want) = (words(&m, k), words(&want, k));
            for a in [&a % &m, a] {
                if a.to_u64_digits().len() <= k {
                    assert_eq!(modinv(&words(&a, k), &mw), want, "{test}");
                    assert!(coprime(&words(&a, k), &mw), "{test}");
                    ran += 1;
                }
            }
        }
        assert!(ran >= 15);
    }

    /// 3 against 2^(64k - 1) and 3 * 2^(64k - 2), which set the gcd only
    /// after a step per bit of the wider, and inverses of 1, 2, and -1, up to
    /// the widest the buffers hold.
    #[test]
    fn widths() {
        for k in [1, 2, 20, MAX_WORDS] {
            let mut top = vec![0; k];
            top[k - 1] = 1 << 63;
            assert!(coprime(&[3], &top));
            assert!(coprime(&top, &[3]));
            top[k - 1] = 3 << 62;
            assert!(!coprime(&[3], &top));
            assert!(!coprime(&[2], &top));
            assert!(!coprime(&[], &top));
            assert!(!coprime(&[], &[]));

            let full = vec![u64::MAX; k];
            let one = words(&BigUint::from(1u8), k);
            assert_eq!(modinv(&one, &full), one);
            let mut minus_one = full.clone();
            minus_one[0] -= 1;
            assert_eq!(modinv(&minus_one, &full), minus_one);
            // 1/2 is (m + 1) / 2, which is 2^(64k - 1).
            let mut half = vec![0; k];
            half[k - 1] = 1 << 63;
            assert_eq!(modinv(&words(&BigUint::from(2u8), k), &full), half);
        }
    }

    #[cfg(any(rind_backend = "x86_64", rind_backend = "aarch64"))]
    mod s2n_bignum {
        use super::super::super::super::bignum::tests::modulus;
        use super::*;
        use crate::low;
        use crate::test::bignum::words;

        proptest! {
            #[test]
            fn matches(x in words(0, 6), y in words(0, 6), (m, a, _) in modulus(20)) {
                let w = x.len().max(y.len());
                prop_assert_eq!(coprime(&x, &y), low::bignum_coprime(&x, &y, &mut vec![0; 2 * w]));

                let k = m.len();
                if low::bignum_coprime(&a, &m, &mut vec![0; 2 * k]) {
                    let mut theirs = vec![0; k];
                    low::bignum_modinv(&mut theirs, &a, &m, &mut vec![0; 3 * k]);
                    prop_assert_eq!(modinv(&a, &m), theirs);
                }
            }
        }

        /// The widest values, which the fixed buffers must hold: m of all
        /// ones and m - 2, which is coprime to it.
        #[test]
        fn widest() {
            let m = [u64::MAX; MAX_WORDS];
            let mut x = m;
            x[0] -= 2;
            let mut theirs = [0; MAX_WORDS];
            low::bignum_modinv(&mut theirs, &x, &m, &mut [0; MAX_WORDS * 3]);
            assert_eq!(modinv(&x, &m), theirs);
        }
    }
}
