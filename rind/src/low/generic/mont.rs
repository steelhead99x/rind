// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The s2n-bignum routines `low::PosInt` uses that multiply, with their
//! contracts, in portable Rust over limbs of the width the parent module
//! picks, and the portable backend's Montgomery multiplication and squaring,
//! which armv7 runs aws-lc's assembly for.
//!
//! A limb is half of `Wide`, so its products are one multiply instruction,
//! or two for a 64-bit limb's low and high halves: 32-bit limbs where a 64
//! by 64-bit product's high half would be a library call, and 64-bit ones
//! where the CPU has that instruction, for a quarter of the products.
//!
//! Each runs in time that depends only on its lengths, and its modulus's
//! width in `bignum_montifier`, never on its values: loops run a count fixed
//! by those, and selects are masks. A half-difference's sign and the carry
//! into a Karatsuba product's high half are masks too, never branches.
//! Arithmetic on values wraps, though the bounds rule out overflow, since a
//! debug build's overflow check would branch on them.
//!
//! The algorithms are the textbook ones, each stated with its bound where
//! it is defined: Montgomery multiplication by Koç, Acar, and Kaliski's CIOS
//! method, Montgomery reduction (HAC 14.32), and a square formed with each
//! cross product once (HAC 14.16). At and above [`MUL_KARATSUBA`] limbs the
//! product, and at and above [`SQR_KARATSUBA`] the square, are Karatsuba's
//! (Knuth, The Art of Computer Programming, vol. 2, sec. 4.3.3): for halves
//! `a0 + a1 B` and `b0 + b1 B`,
//! `(a0 - a1) (b1 - b0) + a0 b0 + a1 b1 = a0 b1 + a1 b0`, and
//! `(a0 - a1)^2 = a0^2 + a1^2 - 2 a0 a1`. The absolute values and the sign of
//! that product are masks. The schoolbook loops stay, for shorter inputs and
//! for proofs of this file.

use super::super::bignum::{MAX_WORDS, nonzero, select, word};
use super::{Limb, Wide, join, limbs};
use crate::low::ct;

/// Limbs in a 64-bit word.
const PER_WORD: usize = (u64::BITS / Limb::BITS) as usize;

/// `MAX_WORDS` in limbs.
const MAX_LIMBS: usize = MAX_WORDS * PER_WORD;

/// Lengths, in limbs, from which Karatsuba beats this file's schoolbook.
///
/// Measured on an Intel Xeon (family 6, model 207) on 2026-11-12, release,
/// with the product and scratch sized to `2n` and `4n` limbs. A square at a
/// signing prime (32, 48, and 64 limbs when a limb is 64 bits) stays slower
/// than the schoolbook square plus the same [`redc`]: three interleaved
/// rounds gave schoolbook 1.15 µs and Karatsuba 1.25 µs at 32 limbs, 2.51 µs
/// and 2.55 µs at 48, and 4.48 µs and 4.55 µs at 64. A 64-bit product wins
/// from 48 limbs and a square from 96; 32-bit limbs from 96 and 128. Below
/// that, the schoolbook loop runs.
const MUL_KARATSUBA: usize = match Limb::BITS {
    64 => 48,
    _ => 96,
};
const SQR_KARATSUBA: usize = match Limb::BITS {
    64 => 96,
    _ => 128,
};

/// `n` is long enough, and even, for one Karatsuba split.
fn karatsuba(n: usize, crossover: usize) -> bool {
    n >= crossover && n & 1 == 0
}

/// Compute "montification" constant z := 2^{128k} mod m
///
/// Input m[k]; output z[k]; temporary buffer t[>=k]
///
/// For an odd m above one, as Montgomery multiplication needs. `_t` is
/// s2n-bignum's scratch space, which this does not need. Its time also
/// depends on, and so reveals, m's width in limbs, as aws-lc's reveals its
/// width in bits: an RSA key's encoding gives its primes' widths.
pub(crate) fn bignum_montifier(z: &mut [u64], m: &[u64], _t: &mut [u64]) {
    let mut m_limbs = [0; MAX_LIMBS];
    let m = limbs(m, &mut m_limbs);
    let n = m.len();
    let n0 = neg_inverse(m[0]);

    // 2^(bt) for m's top nonzero limb t, with b bits a limb, is below m, as
    // m is odd and above one. Doubling it (b(n - t) + 1) times gives
    // 2^(bn + 1) mod m, which is 2 in Montgomery form. Squaring 2^e there
    // gives 2^2e, and doubling 2^(e + 1), so squaring and doubling by the
    // bits of bn below its top one raise it to 2^bn, whose Montgomery form
    // 2^2bn is the montifier.
    let mut top = 0;
    for (i, limb) in m.iter().enumerate() {
        top = select(nonzero(u64::from(*limb)), i as u64, top);
    }
    let top = ct::into_public(top) as usize;
    let mut r = [0; MAX_LIMBS];
    let r = &mut r[..n];
    r[top] = 1;
    for _ in 0..=Limb::BITS as usize * (n - top) {
        mod_double(r, m);
    }
    let e = Limb::BITS as usize * n;
    let mut square = [0; MAX_LIMBS * 2];
    for bit in (0..e.ilog2()).rev() {
        mont_sqr_limbs(&mut square[..2 * n], r, m, n0);
        r.copy_from_slice(&square[n..2 * n]);
        if e >> bit & 1 == 1 {
            mod_double(r, m);
        }
    }
    join(r, z);
}

/// Montgomery reduce, z := (x' / 2^{64p}) MOD m
///
/// Inputs x[n], m[k], p; output z[k]
///
/// Does a := (x' / 2^{64p}) mod m where x' = x if n <= p + k and in general
/// is the lowest (p+k) digits of x, assuming x' <= 2^{64p} * m. That is,
/// p-fold Montgomery reduction w.r.t. a k-digit modulus m giving a k-digit
/// answer.
pub(crate) fn bignum_montredc(z: &mut [u64], x: &[u64], m: &[u64], p: u64) {
    let mut m_limbs = [0; MAX_LIMBS];
    let m = limbs(m, &mut m_limbs);
    let p = p as usize * PER_WORD;
    let mut t = [0; MAX_LIMBS * 2];
    let t = &mut t[..p + m.len()];
    for (i, t) in t.iter_mut().enumerate() {
        *t = (word(x, i / PER_WORD) >> (Limb::BITS as usize * (i % PER_WORD))) as Limb;
    }
    redc(t, m, neg_inverse(m[0]));
    join(&t[p..], z);
}

/// Multiply z := x * y
///
/// Inputs x[m], y[n]; output z[k]
///
/// Truncates the result in general unless k >= m + n
pub(crate) fn bignum_mul(z: &mut [u64], x: &[u64], y: &[u64]) {
    let (mut x_limbs, mut y_limbs) = ([0; MAX_LIMBS], [0; MAX_LIMBS]);
    let (x, y) = (limbs(x, &mut x_limbs), limbs(y, &mut y_limbs));
    // The product is `x.len() + y.len()` limbs, not the maximum: zeroing a
    // fixed `MAX_LIMBS * 2` buffer made every width pay for an 8192-bit
    // product.
    let mut product = vec![0; x.len() + y.len()];
    if x.len() == y.len() && karatsuba(x.len(), MUL_KARATSUBA) {
        let mut scratch = vec![0; 4 * x.len()];
        mul_karatsuba(&mut product, x, y, &mut scratch, MUL_KARATSUBA);
        crate::low::zeroise(&mut scratch);
    } else {
        mul_schoolbook(&mut product, x, y);
    }
    z.fill(0);
    join(&product, z);
    crate::low::zeroise(&mut product);
}

/// `z = x * y / 2^(64k) mod m`, for `x` and `y` below the odd `m`, where `k`
/// is the length of each and `n0` is `-m^-1 mod 2^64`.
///
/// HACL*'s verified `Hacl_Bignum` has this, but its Rust allocates scratch
/// for each call and frees it unwiped, though RSA's private operations put
/// their secrets there.
#[cfg(any(
    rind_backend = "portable",
    all(test, any(rind_backend = "x86_64", rind_backend = "aarch64"))
))]
pub(crate) fn mont_mul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64], n0: u64) {
    let k = m.len();
    assert!(k >= 1 && z.len() == k && x.len() == k && y.len() == k);
    let mut buf = [[0; MAX_LIMBS]; 3];
    let [x_limbs, y_limbs, m_limbs] = &mut buf;
    let (x, y, m) = (limbs(x, x_limbs), limbs(y, y_limbs), limbs(m, m_limbs));
    // The low limb of `-m^-1 mod 2^64` is `-m^-1` mod a limb.
    let n0 = n0 as Limb;
    if karatsuba(m.len(), MUL_KARATSUBA) {
        mont_mul_karatsuba(z, x, y, m, n0);
    } else {
        let mut t = [0; MAX_LIMBS + 2];
        mont_mul_limbs(&mut t[..m.len() + 2], x, y, m, n0);
        join(&t, z);
    }
}

/// `z = x^2 / 2^(64k) mod m`, as [`mont_mul`] takes them.
#[cfg(any(
    rind_backend = "portable",
    all(test, any(rind_backend = "x86_64", rind_backend = "aarch64"))
))]
pub(crate) fn mont_sqr(z: &mut [u64], x: &[u64], m: &[u64], n0: u64) {
    let k = m.len();
    assert!(k >= 1 && z.len() == k && x.len() == k);
    let (mut x_limbs, mut m_limbs) = ([0; MAX_LIMBS], [0; MAX_LIMBS]);
    let (x, m) = (limbs(x, &mut x_limbs), limbs(m, &mut m_limbs));
    let n = m.len();
    let n0 = n0 as Limb;
    if karatsuba(n, SQR_KARATSUBA) {
        mont_sqr_karatsuba(z, x, m, n0);
    } else {
        let mut t = [0; MAX_LIMBS * 2];
        mont_sqr_limbs(&mut t[..2 * n], x, m, n0);
        join(&t[n..2 * n], z);
    }
}

/// `t[..n] := x * y / 2^bn mod m`, for `x` and `y` below the odd `m`, each
/// `n` limbs of `b` bits, where `t` is `n + 2` zero limbs and `n0` is
/// `-m^-1 mod 2^b`.
///
/// Koç, Acar, and Kaliski's CIOS method: each step adds `x[i] * y` to `t`,
/// then the multiple of `m` that clears its lowest limb, shifting `t` down a
/// limb as it adds, which keeps `t` below 2m.
#[cfg(any(
    rind_backend = "portable",
    all(test, any(rind_backend = "x86_64", rind_backend = "aarch64"))
))]
fn mont_mul_limbs(t: &mut [Limb], x: &[Limb], y: &[Limb], m: &[Limb], n0: Limb) {
    let n = m.len();
    let t = &mut t[..n + 2];
    for x in x {
        let sum = Wide::from(t[n]).wrapping_add(mul_add(&mut t[..n], y, *x));
        t[n] = sum as Limb;
        t[n + 1] = (sum >> Limb::BITS) as Limb;

        let u = t[0].wrapping_mul(n0);
        let mut carry = mul_add_limb(u, m[0], t[0], 0) >> Limb::BITS;
        for j in 1..n {
            let s = mul_add_limb(u, m[j], t[j], carry);
            t[j - 1] = s as Limb;
            carry = s >> Limb::BITS;
        }
        let sum = Wide::from(t[n]).wrapping_add(carry);
        t[n - 1] = sum as Limb;
        t[n] = t[n + 1].wrapping_add((sum >> Limb::BITS) as Limb);
    }
    let below = cmp_lt_limbs(&t[..n], m);
    let keep = Limb::wrapping_sub(0, t[n] | (below ^ 1));
    sub_limbs_masked(&mut t[..n], m, keep);
}

/// `t[n..] := x^2 / 2^bn mod m`, for `x` below the odd `m`, each `n` limbs
/// of `b` bits, where `t` is `2n` zero limbs and `n0` is `-m^-1 mod 2^b`.
///
/// The square takes each product of two different limbs once, doubled, plus
/// the square of each limb: n(n + 1) / 2 products where a multiplication
/// takes n^2.
fn mont_sqr_limbs(t: &mut [Limb], x: &[Limb], m: &[Limb], n0: Limb) {
    let n = x.len();
    let t = &mut t[..2 * n];
    for i in 0..n {
        t[i + n] = mul_add(&mut t[2 * i + 1..i + n], &x[i + 1..], x[i]) as Limb;
    }

    // The products sum to below x^2 / 2, so doubling them cannot overflow.
    let mut out = 0;
    for t in t.iter_mut() {
        let next = *t >> (Limb::BITS - 1);
        *t = *t << 1 | out;
        out = next;
    }

    let mut carry = 0;
    for (i, x) in x.iter().enumerate() {
        let s = mul_add_limb(*x, *x, t[2 * i], carry);
        t[2 * i] = s as Limb;
        let s = Wide::from(t[2 * i + 1]).wrapping_add(s >> Limb::BITS);
        t[2 * i + 1] = s as Limb;
        carry = s >> Limb::BITS;
    }

    // x^2 is below m^2, so below 2^bn * m.
    redc(t, m, n0);
}

/// `t[p..] := t / 2^bp mod m`, for `t` below 2^bp * m, where `p` is the
/// limbs of `t` beyond `m`'s, each of `b` bits, and `n0` is `-m^-1 mod
/// 2^b`.
///
/// Each step clears the lowest limb by adding a multiple of m. The carry out
/// of the top of a step's sum waits in `top` for the next, as it lands where
/// the next step's sum ends. The result is below 2m, as the multiples are
/// below 2^bp * m too, so one subtraction reduces it.
fn redc(t: &mut [Limb], m: &[Limb], n0: Limb) {
    let k = m.len();
    let p = t.len() - k;
    let mut top = 0;
    for i in 0..p {
        let u = t[i].wrapping_mul(n0);
        let carry = mul_add(&mut t[i..i + k], m, u);
        let sum = Wide::from(t[i + k]).wrapping_add(carry).wrapping_add(top);
        t[i + k] = sum as Limb;
        top = sum >> Limb::BITS;
    }

    let r = &mut t[p..];
    let below = cmp_lt_limbs(r, m);
    sub_limbs_masked(r, m, Limb::wrapping_sub(0, top as Limb | (below ^ 1)));
}

/// `x += y * u`, returning the carry out of the top limb.
fn mul_add(x: &mut [Limb], y: &[Limb], u: Limb) -> Wide {
    let mut carry = 0;
    for (x, y) in x.iter_mut().zip(y) {
        let t = mul_add_limb(u, *y, *x, carry);
        *x = t as Limb;
        carry = t >> Limb::BITS;
    }
    carry
}

/// `a * b + c + d`, for a `d` that fits a limb, which fits `Wide`: at most
/// (2^b - 1)^2 + 2 (2^b - 1) = 2^2b - 1.
fn mul_add_limb(a: Limb, b: Limb, c: Limb, d: Wide) -> Wide {
    Wide::from(a)
        .wrapping_mul(Wide::from(b))
        .wrapping_add(Wide::from(c))
        .wrapping_add(d)
}

/// `z = x * y`, schoolbook, for a `z` at least `x.len() + y.len()` limbs.
///
/// The same accumulation as the product this file started with.
fn mul_schoolbook(z: &mut [Limb], x: &[Limb], y: &[Limb]) {
    let yn = y.len();
    let z = &mut z[..x.len() + yn];
    z.fill(0);
    for (i, xi) in x.iter().enumerate() {
        z[i + yn] = mul_add(&mut z[i..i + yn], y, *xi) as Limb;
    }
}

/// `z = x^2`, schoolbook, each cross product once, for a `z` of `2 x.len()`
/// limbs. The products of distinct limbs sum to below `x^2 / 2`, so doubling
/// them cannot overflow a `2n`-limb buffer.
fn sqr_schoolbook(z: &mut [Limb], x: &[Limb]) {
    let n = x.len();
    let z = &mut z[..2 * n];
    z.fill(0);
    for i in 0..n {
        z[i + n] = mul_add(&mut z[2 * i + 1..i + n], &x[i + 1..], x[i]) as Limb;
    }
    let mut out = 0;
    for z in z.iter_mut() {
        let next = *z >> (Limb::BITS - 1);
        *z = *z << 1 | out;
        out = next;
    }
    let mut carry = 0;
    for (i, x) in x.iter().enumerate() {
        let s = mul_add_limb(*x, *x, z[2 * i], carry);
        z[2 * i] = s as Limb;
        let s = Wide::from(z[2 * i + 1]).wrapping_add(s >> Limb::BITS);
        z[2 * i + 1] = s as Limb;
        carry = s >> Limb::BITS;
    }
}

/// All ones where `bit` is one and zero where it is zero, hidden from the
/// optimizer so the select it feeds cannot become a branch.
fn bit_mask(bit: Limb) -> Limb {
    core::hint::black_box(Limb::wrapping_sub(0, bit))
}

/// `r = x + y`, returning the carry, which is 0 or 1.
fn add_limbs(r: &mut [Limb], x: &[Limb], y: &[Limb]) -> Limb {
    let mut carry = 0;
    for ((r, x), y) in r.iter_mut().zip(x).zip(y) {
        let s = Wide::from(*x)
            .wrapping_add(Wide::from(*y))
            .wrapping_add(carry);
        *r = s as Limb;
        carry = s >> Limb::BITS;
    }
    carry as Limb
}

/// `r = x - y`, returning the borrow, which is 0 or 1.
///
/// The borrow is the top bit of the wrapped difference, not
/// `overflowing_sub`'s flag: that flag lowers to a branch valgrind reports
/// on a secret.
fn sub_limbs(r: &mut [Limb], x: &[Limb], y: &[Limb]) -> Limb {
    let mut borrow = 0;
    for ((r, x), y) in r.iter_mut().zip(x).zip(y) {
        let d = Wide::from(*x)
            .wrapping_sub(Wide::from(*y))
            .wrapping_sub(borrow);
        *r = d as Limb;
        borrow = d >> (Wide::BITS - 1);
    }
    borrow as Limb
}

/// `r = if_ones` where `mask` is all ones, and `if_zero` where it is zero.
fn select_limbs(mask: Limb, r: &mut [Limb], if_ones: &[Limb], if_zero: &[Limb]) {
    let mask = core::hint::black_box(mask);
    for ((r, a), b) in r.iter_mut().zip(if_ones).zip(if_zero) {
        *r = *b ^ ((*a ^ *b) & mask);
    }
}

/// `if_ones` where `mask` is all ones, and `if_zero` where it is zero.
fn select_i128(mask: Limb, if_ones: i128, if_zero: i128) -> i128 {
    let m = i128::from(core::hint::black_box(mask) >> (Limb::BITS - 1)).wrapping_neg();
    if_zero ^ ((if_ones ^ if_zero) & m)
}

/// `r += add`, then `high` just above `add`.
///
/// `high` is the carry out of `add`'s own limbs (about -1, 0, 1, or 2), not
/// a carry into its first limb. The walk still runs to the end of `r` when
/// that carry is zero.
fn add_high(r: &mut [Limb], add: &[Limb], high: i128) {
    let mut carry = 0i128;
    let mut i = 0;
    while i < add.len() {
        let sum = i128::from(r[i]) + i128::from(add[i]) + carry;
        r[i] = sum as Limb;
        carry = sum >> Limb::BITS;
        i += 1;
    }
    carry += high;
    while i < r.len() {
        let sum = i128::from(r[i]) + carry;
        r[i] = sum as Limb;
        carry = sum >> Limb::BITS;
        i += 1;
    }
}

/// `|a - b|`, and a mask of all ones when `a < b`.
fn abs_sub(r: &mut [Limb], a: &[Limb], b: &[Limb], tmp: &mut [Limb]) -> Limb {
    let borrow = sub_limbs(tmp, a, b);
    sub_limbs(r, b, a);
    let mask = bit_mask(borrow);
    for (r, tmp) in r.iter_mut().zip(tmp.iter()) {
        *r = *tmp ^ ((*r ^ *tmp) & mask);
    }
    mask
}

/// `z = x * y` by Karatsuba where `x` and `y` have the same even length at or
/// above `crossover`, and by [`mul_schoolbook`] otherwise.
///
/// `t` is `4n` limbs. Its low `n` hold the two half-differences, the next
/// `n` the product of those, and the upper `2n` the recursive scratch, which
/// is `4` times a half. `z` is `2n` limbs and shares nothing with `x`, `y`,
/// or `t`.
fn mul_karatsuba(z: &mut [Limb], x: &[Limb], y: &[Limb], t: &mut [Limb], crossover: usize) {
    let n = x.len();
    if !karatsuba(n, crossover) {
        mul_schoolbook(z, x, y);
        return;
    }
    let h = n >> 1;
    // `|b1 - b0|` next to `|a0 - a1|`, so the product of the two differences
    // has the sign of `(a0 - a1) (b1 - b0)`. The temporary is the recursive
    // scratch, still unused.
    let neg = {
        let (lo, scratch) = t.split_at_mut(2 * n);
        let sign_a = abs_sub(&mut lo[..h], &x[..h], &x[h..n], &mut scratch[..h]);
        let sign_b = abs_sub(&mut lo[h..n], &y[h..n], &y[..h], &mut scratch[..h]);
        sign_a ^ sign_b
    };

    {
        let (lo, scratch) = t.split_at_mut(2 * n);
        let (diffs, prod) = lo.split_at_mut(n);
        let (diff_a, diff_b) = diffs.split_at_mut(h);
        mul_karatsuba(prod, diff_a, diff_b, scratch, crossover);
    }
    mul_karatsuba(
        &mut z[..n],
        &x[..h],
        &y[..h],
        &mut t[2 * n..4 * n],
        crossover,
    );
    mul_karatsuba(
        &mut z[n..2 * n],
        &x[h..n],
        &y[h..n],
        &mut t[2 * n..4 * n],
        crossover,
    );

    // `t[..n] = z0 + z2`, whose carry is 0 or 1. `t[n..2n]` still holds
    // `|(a0 - a1) (b1 - b0)|`.
    let carry = add_limbs(&mut t[..n], &z[..n], &z[n..2 * n]);
    let borrow = {
        let (sum, rest) = t.split_at_mut(n);
        let (prod, dest) = rest.split_at_mut(n);
        sub_limbs(&mut dest[..n], sum, &prod[..n])
    };
    let extra = {
        let (sum, rest) = t.split_at_mut(n);
        let (prod, dest) = rest.split_at_mut(n);
        add_limbs(&mut dest[n..2 * n], sum, &prod[..n])
    };
    {
        let (_, rest) = t.split_at_mut(n);
        let (mid, both) = rest.split_at_mut(n);
        let (below, above) = both.split_at_mut(n);
        // A negative product subtracts; a positive one adds.
        select_limbs(neg, mid, below, &above[..n]);
    }
    let c = select_i128(
        neg,
        i128::from(carry) - i128::from(borrow),
        i128::from(carry) + i128::from(extra),
    );
    add_high(&mut z[h..2 * n], &t[n..2 * n], c);
}

/// `z = x^2` by Karatsuba where `x` has an even length at or above
/// `crossover`, and by [`sqr_schoolbook`] otherwise.
///
/// The square of the half-difference is always subtracted: it equals
/// `a0^2 + a1^2 - 2 a0 a1` whichever half is larger, and [`abs_sub`] still
/// picks that absolute value by a mask. `t` and `z` are laid out as in
/// [`mul_karatsuba`].
fn sqr_karatsuba(z: &mut [Limb], x: &[Limb], t: &mut [Limb], crossover: usize) {
    let n = x.len();
    if !karatsuba(n, crossover) {
        sqr_schoolbook(z, x);
        return;
    }
    let h = n >> 1;
    {
        let (lo, scratch) = t.split_at_mut(2 * n);
        abs_sub(&mut lo[..h], &x[..h], &x[h..n], &mut scratch[..h]);
        let (diff, rest) = lo.split_at_mut(h);
        // `rest[h..]` is `t[n..2n]`, the `n` limbs the difference's square fills.
        sqr_karatsuba(&mut rest[h..], diff, scratch, crossover);
    }
    sqr_karatsuba(&mut z[..n], &x[..h], &mut t[2 * n..4 * n], crossover);
    sqr_karatsuba(&mut z[n..2 * n], &x[h..n], &mut t[2 * n..4 * n], crossover);

    let carry = add_limbs(&mut t[..n], &z[..n], &z[n..2 * n]);
    let borrow = {
        let (sum, rest) = t.split_at_mut(n);
        let (diff_sqr, dest) = rest.split_at_mut(n);
        sub_limbs(&mut dest[..n], sum, &diff_sqr[..n])
    };
    add_high(
        &mut z[h..2 * n],
        &t[2 * n..3 * n],
        i128::from(carry) - i128::from(borrow),
    );
}

/// `z = x * y / 2^bn mod m` by a Karatsuba product and [`redc`].
///
/// `x` and `y` are below the odd `m`, so their product is below `2^bn * m`
/// and one reduction brings it below `2m`, which [`redc`] finishes.
fn mont_mul_karatsuba(z: &mut [u64], x: &[Limb], y: &[Limb], m: &[Limb], n0: Limb) {
    let n = m.len();
    // `2n` and `4n` limbs, not `MAX_LIMBS`. A fixed buffer zeroed every call
    // was about 6 KiB on 64-bit limbs whatever `n` was, which is most of a
    // short product and pushed the crossover out past RSA's primes.
    let mut product = vec![0; 2 * n];
    let mut scratch = vec![0; 4 * n];
    mul_karatsuba(&mut product, x, y, &mut scratch, MUL_KARATSUBA);
    redc(&mut product, m, n0);
    join(&product[n..], z);
    // Heap scratch from a private operation is as good as the prime.
    crate::low::zeroise(&mut product);
    crate::low::zeroise(&mut scratch);
}

/// `z = x^2 / 2^bn mod m` by a Karatsuba square and [`redc`].
fn mont_sqr_karatsuba(z: &mut [u64], x: &[Limb], m: &[Limb], n0: Limb) {
    let n = m.len();
    let mut square = vec![0; 2 * n];
    let mut scratch = vec![0; 4 * n];
    sqr_karatsuba(&mut square, x, &mut scratch, SQR_KARATSUBA);
    redc(&mut square, m, n0);
    join(&square[n..], z);
    crate::low::zeroise(&mut square);
    crate::low::zeroise(&mut scratch);
}

/// `r := 2r mod m`, for `r` below `m`.
fn mod_double(r: &mut [Limb], m: &[Limb]) {
    let mut out = 0;
    for r in r.iter_mut() {
        let next = *r >> (Limb::BITS - 1);
        *r = *r << 1 | out;
        out = next;
    }
    let below = cmp_lt_limbs(r, m);
    sub_limbs_masked(r, m, Limb::wrapping_sub(0, out | (below ^ 1)));
}

/// `-m^-1` mod a limb, for an odd `m`.
fn neg_inverse(m: Limb) -> Limb {
    // Correct to 5 bits, then Newton's iteration doubles that each time.
    let mut inv = m.wrapping_mul(3) ^ 2;
    for _ in 0..Limb::BITS.ilog2() - 2 {
        inv = inv.wrapping_mul(Limb::wrapping_sub(2, m.wrapping_mul(inv)));
    }
    inv.wrapping_neg()
}

/// `bignum_cmp_lt` for limbs of one length.
fn cmp_lt_limbs(x: &[Limb], y: &[Limb]) -> Limb {
    let mut borrow = 0;
    for (x, y) in x.iter().zip(y) {
        let (diff, b1) = x.overflowing_sub(*y);
        let (_, b2) = diff.overflowing_sub(borrow);
        borrow = Limb::from(b1 | b2);
    }
    borrow
}

/// `x := x - y` where `keep` is all ones.
fn sub_limbs_masked(x: &mut [Limb], y: &[Limb], keep: Limb) {
    let mut borrow = 0;
    for (x, y) in x.iter_mut().zip(y) {
        let (diff, b1) = x.overflowing_sub(y & keep);
        let (diff, b2) = diff.overflowing_sub(borrow);
        *x = diff;
        borrow = Limb::from(b1 | b2);
    }
}

/// Checks each routine against s2n-bignum's, word for word.
///
/// The values are marked secret, so under `admin/ctgrind` these also check
/// each routine is constant time in them.
#[cfg(all(test, any(rind_backend = "x86_64", rind_backend = "aarch64")))]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use proptest::prelude::*;

    use super::super::super::bignum::tests::{modulus, public, secret};
    use super::*;
    use crate::low;
    use crate::low::ct::into_secret;
    use crate::test::bignum::words;

    proptest! {
        #[test]
        fn product(x in words(0, 8), y in words(0, 8), extra in 0..3usize) {
            // rind's s2n-bignum wrappers refuse to truncate a product.
            let wide = x.len() + y.len() + extra;
            let (mut ours, mut theirs) = (vec![1; wide], vec![0; wide]);
            bignum_mul(&mut ours, &secret(&x), &secret(&y));
            low::bignum_mul(&mut theirs, &x, &y);
            prop_assert_eq!(public(&ours), theirs);
        }

        #[test]
        fn modular((m, x, y) in modulus(), extra in words(0, 4)) {
            let k = m.len();
            let (sm, sx, sy) = (secret(&m), secret(&x), secret(&y));
            let (mut ours, mut theirs) = (vec![0; k], vec![0; k]);

            bignum_montifier(&mut ours, &sm, &mut []);
            low::bignum_montifier(&mut theirs, &m, &mut vec![0; k]);
            prop_assert_eq!(public(&ours), theirs.clone());

            // x * y + extra * 2^64k * m stays within 2^64(k + p) * m for p
            // above the extra words.
            let p = k + extra.len();
            let mut wide = vec![0; 2 * k + extra.len() + 1];
            low::bignum_mul(&mut wide, &x, &y);
            let mut em = vec![0; k + extra.len()];
            low::bignum_mul(&mut em, &extra, &m);
            let mut sum = vec![0; wide.len()];
            low::bignum_add(&mut sum, &wide, &[vec![0; k], em].concat());
            bignum_montredc(&mut ours, &secret(&sum), &sm, p as u64);
            low::bignum_montredc(&mut theirs, &sum, &m, p as u64);
            prop_assert_eq!(public(&ours), theirs.clone());

            let mut n0 = [0];
            low::bignum_negmodinv(&mut n0, &m[..1]);
            mont_mul(&mut ours, &sx, &sy, &sm, into_secret(n0[0]));
            low::mont_mul(&mut theirs, &x, &y, &m, n0[0]);
            prop_assert_eq!(public(&ours), theirs.clone());

            mont_sqr(&mut ours, &sx, &sm, into_secret(n0[0]));
            low::mont_mul(&mut theirs, &x, &x, &m, n0[0]);
            prop_assert_eq!(public(&ours), theirs);
        }
    }

    /// The widest values, which the fixed buffers must hold.
    #[test]
    fn widest() {
        let m = [u64::MAX; MAX_WORDS];
        let x = [u64::MAX - 1; MAX_WORDS];
        let (mut product, mut theirs) = ([0; MAX_WORDS * 2], [0; MAX_WORDS * 2]);
        bignum_mul(&mut product, &x, &x);
        low::bignum_mul(&mut theirs, &x, &x);
        assert_eq!(product, theirs);

        let (mut ours, mut theirs) = ([0; MAX_WORDS], [0; MAX_WORDS]);
        bignum_montredc(&mut ours, &product, &m, MAX_WORDS as u64);
        low::bignum_montredc(&mut theirs, &product, &m, MAX_WORDS as u64);
        assert_eq!(ours, theirs);
        bignum_montifier(&mut ours, &m, &mut []);
        low::bignum_montifier(&mut theirs, &m, &mut [0; MAX_WORDS]);
        assert_eq!(ours, theirs);
        // -m^-1 is one for an m of all ones.
        mont_mul(&mut ours, &x, &x, &m, 1);
        low::mont_mul(&mut theirs, &x, &x, &m, 1);
        assert_eq!(ours, theirs);
        mont_sqr(&mut ours, &x, &m, 1);
        assert_eq!(ours, theirs);
    }

    /// The identity in the module docs, at one limb per half: 503 × 207 and
    /// 503² in base 2^b.
    #[test]
    fn karatsuba_identity() {
        let mut product = [0; 4];
        let mut scratch = [0; 8];
        mul_karatsuba(&mut product, &[3, 5], &[7, 2], &mut scratch, 2);
        assert_eq!(product, [21, 41, 10, 0]);
        mul_karatsuba(&mut product, &[2, 5], &[2, 7], &mut scratch, 2);
        assert_eq!(product, [4, 24, 35, 0]);
        sqr_karatsuba(&mut product, &[3, 5], &mut scratch, 2);
        assert_eq!(product, [9, 30, 25, 0]);
    }

    /// Karatsuba at every even length, including below the production
    /// crossover, against the schoolbook product and square.
    #[test]
    fn karatsuba_matches_schoolbook() {
        let mut step = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = || {
            step = step.wrapping_mul(0x6C62_272E_07BB_0142).wrapping_add(1);
            step
        };
        for n in [2usize, 4, 6, 8, 12, 16, 24, 32, 48] {
            let x: Vec<Limb> = (0..n).map(|_| next() as Limb).collect();
            let y: Vec<Limb> = (0..n).map(|_| next() as Limb).collect();
            let mut got = vec![1; 2 * n];
            let mut expect = vec![0; 2 * n];
            let mut scratch = vec![0; 4 * n];
            mul_karatsuba(&mut got, &x, &y, &mut scratch, 2);
            mul_schoolbook(&mut expect, &x, &y);
            assert_eq!(got, expect, "mul {n}");
            sqr_karatsuba(&mut got, &x, &mut scratch, 2);
            sqr_schoolbook(&mut expect, &x);
            assert_eq!(got, expect, "sqr {n}");
            // All-ones halves force a carry out of every limb.
            let ones = vec![Limb::MAX; n];
            mul_karatsuba(&mut got, &ones, &ones, &mut scratch, 2);
            mul_schoolbook(&mut expect, &ones, &ones);
            assert_eq!(got, expect, "mul ones {n}");
            sqr_karatsuba(&mut got, &ones, &mut scratch, 2);
            sqr_schoolbook(&mut expect, &ones);
            assert_eq!(got, expect, "sqr ones {n}");
        }
    }

    /// The production crossover, on both sides, against s2n-bignum. Inputs
    /// are marked secret, so under `admin/ctgrind` this also checks the
    /// Karatsuba path. The words are declassified only to compare.
    #[test]
    fn karatsuba_matches_s2n() {
        // Word counts. On 32-bit limbs each word is two limbs, so a count
        // below the limb crossover still takes the Karatsuba path there.
        // 96 and 128 words are where a 64-bit square takes Karatsuba; on
        // 32-bit limbs that is 192 and 256 limbs, the top of the buffer.
        for k in [1usize, 8, 12, 15, 16, 17, 24, 32, 48, 64, 96, 128] {
            let mut step = 0xD1B5_4A32_D192_ED03u64 ^ k as u64;
            let mut word = || {
                step = step
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .wrapping_add(0x7F4A_7C15);
                step
            };
            let x: Vec<u64> = (0..k).map(|_| word()).collect();
            let y: Vec<u64> = (0..k).map(|_| word()).collect();
            let (sx, sy) = (secret(&x), secret(&y));
            let wide = 2 * k;
            let (mut ours, mut theirs) = (vec![1; wide], vec![0; wide]);
            bignum_mul(&mut ours, &sx, &sy);
            low::bignum_mul(&mut theirs, &x, &y);
            assert_eq!(public(&ours), theirs, "mul {k}");

            // An odd modulus whose top bit is set, and operands with that
            // bit clear, so both sit strictly below it.
            let mut m: Vec<u64> = (0..k).map(|_| word()).collect();
            let mut x = x;
            let mut y = y;
            m[0] |= 1;
            m[k - 1] |= 1 << 63;
            x[k - 1] &= !(1 << 63);
            y[k - 1] &= !(1 << 63);
            let (sm, sx, sy) = (secret(&m), secret(&x), secret(&y));
            let (mut ours, mut theirs) = (vec![0; k], vec![0; k]);
            let mut n0 = [0];
            low::bignum_negmodinv(&mut n0, &m[..1]);
            mont_mul(&mut ours, &sx, &sy, &sm, into_secret(n0[0]));
            low::mont_mul(&mut theirs, &x, &y, &m, n0[0]);
            assert_eq!(public(&ours), theirs, "mont_mul {k}");
            mont_sqr(&mut ours, &sx, &sm, into_secret(n0[0]));
            low::mont_mul(&mut theirs, &x, &x, &m, n0[0]);
            assert_eq!(public(&ours), public(&theirs), "mont_sqr {k}");
        }
    }

    /// `m - 1`, an all-ones value still below `m`, and a value whose halves
    /// match, so the Karatsuba half-difference is zero. Lengths are the
    /// production crossovers, in words.
    fn crossover_edges(seed: u64) -> Vec<(Vec<u64>, Vec<u64>, Vec<u64>)> {
        let mut words = vec![MUL_KARATSUBA / PER_WORD, SQR_KARATSUBA / PER_WORD];
        words.sort_unstable();
        words.dedup();
        let mut out = Vec::new();
        for k in words {
            let m = vec![u64::MAX; k];
            let mut below = m.clone();
            below[0] = below[0].wrapping_sub(1);
            out.push((m.clone(), below.clone(), below));

            let mut ones = vec![u64::MAX; k];
            ones[k - 1] >>= 1;
            out.push((m.clone(), ones.clone(), ones));

            let h = k / 2;
            let mut half = vec![0; h];
            let mut s = seed | 1;
            for w in &mut half {
                s = s.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
                *w = s & !(1 << 63);
            }
            let mut x = half.clone();
            x.extend_from_slice(&half);
            let mut other = half;
            other[0] ^= 0x5a5a_5a5a;
            let mut y = other.clone();
            y.extend_from_slice(&other);
            out.push((m, x, y));
        }
        out
    }

    proptest! {
        #![proptest_config(proptest::test_runner::Config::with_cases(8))]
        #[test]
        fn karatsuba_crossover_edges(seed in proptest::num::u64::ANY) {
            for (m, x, y) in crossover_edges(seed) {
                let (sm, sx, sy) = (secret(&m), secret(&x), secret(&y));
                let (mut ours, mut theirs) = (vec![0; m.len()], vec![0; m.len()]);
                let mut n0 = [0];
                low::bignum_negmodinv(&mut n0, &m[..1]);
                mont_mul(&mut ours, &sx, &sy, &sm, into_secret(n0[0]));
                low::mont_mul(&mut theirs, &x, &y, &m, n0[0]);
                prop_assert_eq!(public(&ours), theirs.clone());
                mont_sqr(&mut ours, &sx, &sm, into_secret(n0[0]));
                low::mont_mul(&mut theirs, &x, &x, &m, n0[0]);
                prop_assert_eq!(public(&ours), theirs);
            }
        }
    }
}
