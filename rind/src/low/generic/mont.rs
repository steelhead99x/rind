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
//! by those, and selects are masks. Arithmetic on values wraps, though the
//! bounds rule out overflow, since a debug build's overflow check would
//! branch on them.
//!
//! The algorithms are the textbook ones, each stated with its bound where
//! it is defined: Montgomery multiplication by Koç, Acar, and Kaliski's CIOS
//! method, and Montgomery reduction (HAC 14.32). A square is the cross
//! products once, doubled, plus the diagonal (HAC 14.16). On 64-bit limbs,
//! a 128-limb square is Karatsuba (Knuth, TAOCP vol. 2) down to an
//! eight-limb square.

use super::super::bignum::{MAX_WORDS, nonzero, select, word};
use super::{Limb, Wide, join, limbs};
use crate::low::ct;

/// Limbs in a 64-bit word.
const PER_WORD: usize = (u64::BITS / Limb::BITS) as usize;

/// `MAX_WORDS` in limbs.
const MAX_LIMBS: usize = MAX_WORDS * PER_WORD;

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
    let n = y.len();
    let mut product = [0; MAX_LIMBS * 2];
    for (i, x) in x.iter().enumerate() {
        product[i + n] = mul_add(&mut product[i..i + n], y, *x) as Limb;
    }
    z.fill(0);
    join(&product, z);
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
    let mut t = [0; MAX_LIMBS + 2];
    // The low limb of `-m^-1 mod 2^64` is `-m^-1` mod a limb.
    mont_mul_limbs(&mut t[..m.len() + 2], x, y, m, n0 as Limb);
    join(&t, z);
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
    let mut t = [0; MAX_LIMBS * 2];
    mont_sqr_limbs(&mut t[..2 * n], x, m, n0 as Limb);
    join(&t[n..2 * n], z);
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
/// takes n^2. A 128-limb square on 64-bit limbs splits instead:
/// `2 a0 a1 = a0^2 + a1^2 - (a0 - a1)^2`, down to eight limbs. Shorter
/// squares, and every square on 32-bit limbs, stay schoolbook: the split
/// was slower or within the noise there.
fn mont_sqr_limbs(t: &mut [Limb], x: &[Limb], m: &[Limb], n0: Limb) {
    let n = x.len();
    let t = &mut t[..2 * n];
    sqr_product(t, x);
    // x^2 is below m^2, so below 2^bn * m.
    redc(t, m, n0);
}

/// `t[..2n] = x^2`. A 128-limb square on 64-bit limbs uses [`sqr_pow2`];
/// every other length uses the schoolbook square.
#[inline]
fn sqr_product(t: &mut [Limb], x: &[Limb]) {
    if split_square_128(x.len()) {
        sqr128(t, x);
    } else {
        sqr_schoolbook(t, x);
    }
}

/// Whether a square of `n` limbs takes the split path.
///
/// 64-bit limbs only, and only at 128. Shorter squares were slower split,
/// and at 32-bit limbs 128 and 256 were within the noise of the schoolbook
/// square. A function, so the 32-bit module's false result is a value rather
/// than a dead branch.
#[inline(always)]
fn split_square_128(n: usize) -> bool {
    Limb::BITS == 64 && n == 128
}

/// 128-limb square in its own frame, so a shorter square does not reserve
/// this scratch.
#[inline(never)]
fn sqr128(t: &mut [Limb], x: &[Limb]) {
    let mut scratch = [0; sqr_scratch(128)];
    sqr_pow2(t, x, &mut scratch);
}

/// Scratch a power-of-two square of `n > 8` limbs needs. Eight limbs need none.
const fn sqr_scratch(n: usize) -> usize {
    if n <= 8 {
        0
    } else {
        // The difference, its square, the middle term, and one half's scratch.
        n / 2 + 2 * n + sqr_scratch(n / 2)
    }
}

/// `r[..2n] = a^2` for a power-of-two `a` of at least 8 limbs.
///
/// `t` has [`sqr_scratch`]`(n)` limbs. Halves of eight limbs are [`sqr8`].
fn sqr_pow2(r: &mut [Limb], a: &[Limb], t: &mut [Limb]) {
    let n = a.len();
    debug_assert!(r.len() >= 2 * n);
    if n == 8 {
        sqr8(&mut r[..16], a);
        return;
    }
    let h = n / 2;
    let (a0, a1) = a.split_at(h);
    sqr_pow2(&mut r[..n], a0, t);
    sqr_pow2(&mut r[n..2 * n], a1, t);

    let (diff, rest) = t.split_at_mut(h);
    abs_diff(diff, &mut rest[..h], a0, a1);
    let (mid, rest) = rest.split_at_mut(n);
    let (term, scratch) = rest.split_at_mut(n);
    sqr_pow2(mid, diff, scratch);
    // `(a0^2 + a1^2) - |a0 - a1|^2 = 2 a0 a1`, added at limb `h`.
    // The difference's top bit is zero or one and lands at limb `h + n`.
    let high = sub_middle(term, &r[..n], &r[n..2 * n], mid);
    add_middle(r, h, term, high);
}

/// One schoolbook row: `r[at + i] += u * b[i]`, carry stored just past them.
macro_rules! cross_row {
    ($r:ident, $at:expr, $u:expr, $($b:expr),+ $(,)?) => {{
        let mut carry = 0;
        let mut i = $at;
        $(
            carry = mac_limb(&mut $r[i], $b, $u, carry);
            i += 1;
        )+
        $r[i] = carry;
    }};
}

/// `*x += u * y + carry`, returning the new carry. It fits a limb.
#[inline(always)]
fn mac_limb(x: &mut Limb, y: Limb, u: Limb, carry: Limb) -> Limb {
    let t = mul_add_limb(u, y, *x, Wide::from(carry));
    *x = t as Limb;
    (t >> Limb::BITS) as Limb
}

/// Eight-limb square. The cross products are straight-line, which is the
/// base the split above bottoms out in.
fn sqr8(r: &mut [Limb], a: &[Limb]) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = [a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]];
    r[..16].fill(0);
    // Row i adds a[i] times the limbs above it, starting at limb 2i + 1.
    cross_row!(r, 1, a0, a1, a2, a3, a4, a5, a6, a7);
    cross_row!(r, 3, a1, a2, a3, a4, a5, a6, a7);
    cross_row!(r, 5, a2, a3, a4, a5, a6, a7);
    cross_row!(r, 7, a3, a4, a5, a6, a7);
    cross_row!(r, 9, a4, a5, a6, a7);
    cross_row!(r, 11, a5, a6, a7);
    cross_row!(r, 13, a6, a7);

    // The products sum to below a^2 / 2, so doubling them cannot overflow.
    let mut bit = 0;
    for limb in &mut r[..16] {
        let next = *limb >> (Limb::BITS - 1);
        *limb = (*limb << 1) | bit;
        bit = next;
    }
    let mut carry = 0;
    for (i, a) in [a0, a1, a2, a3, a4, a5, a6, a7].into_iter().enumerate() {
        let s = mul_add_limb(a, a, r[2 * i], carry);
        r[2 * i] = s as Limb;
        let s = Wide::from(r[2 * i + 1]).wrapping_add(s >> Limb::BITS);
        r[2 * i + 1] = s as Limb;
        carry = s >> Limb::BITS;
    }
}

/// `out = |a - b|`. The sign is a mask, not a branch: `a` is a secret square.
fn abs_diff(out: &mut [Limb], tmp: &mut [Limb], a: &[Limb], b: &[Limb]) {
    let neg = limb_mask(sub_limbs(tmp, a, b));
    sub_limbs(out, b, a);
    for i in 0..a.len() {
        out[i] = tmp[i] ^ ((out[i] ^ tmp[i]) & neg);
    }
}

/// All ones when `bit` is one, else zero.
fn limb_mask(bit: Limb) -> Limb {
    core::hint::black_box(Limb::wrapping_neg(bit))
}

/// `r = a - b`, returning the borrow, which is zero or one.
fn sub_limbs(r: &mut [Limb], a: &[Limb], b: &[Limb]) -> Limb {
    let mut borrow = 0;
    for i in 0..a.len() {
        let (diff, b1) = a[i].overflowing_sub(b[i]);
        let (diff, b2) = diff.overflowing_sub(borrow);
        r[i] = diff;
        borrow = Limb::from(b1 | b2);
    }
    borrow
}

/// `term = (lo + hi) - mid`, returning the limb above `term`. `lo + hi` is
/// `n` limbs plus a bit, and the difference is `2 a0 a1`, so that bit is
/// zero or one and the subtraction does not borrow out.
fn sub_middle(term: &mut [Limb], lo: &[Limb], hi: &[Limb], mid: &[Limb]) -> Limb {
    let mut sum_carry = 0;
    let mut borrow = 0;
    for i in 0..lo.len() {
        let (sum, c1) = lo[i].overflowing_add(hi[i]);
        let (sum, c2) = sum.overflowing_add(sum_carry);
        sum_carry = Limb::from(c1 | c2);
        let (diff, b1) = sum.overflowing_sub(mid[i]);
        let (diff, b2) = diff.overflowing_sub(borrow);
        term[i] = diff;
        borrow = Limb::from(b1 | b2);
    }
    // `2 a0 a1` is non-negative, so this is zero or one and not a borrow.
    sum_carry.wrapping_sub(borrow)
}

/// Adds the `n`-limb `m` into `r` at limb `h`, then `high` at limb `h + n`.
/// `m` with `high` is `2 a0 a1`, and the square fits in `2n` limbs.
fn add_middle(r: &mut [Limb], h: usize, m: &[Limb], high: Limb) {
    let n = m.len();
    let mut carry = 0;
    for i in 0..n {
        let sum = Wide::from(r[h + i])
            .wrapping_add(Wide::from(m[i]))
            .wrapping_add(carry);
        r[h + i] = sum as Limb;
        carry = sum >> Limb::BITS;
    }
    carry = carry.wrapping_add(Wide::from(high));
    for limb in &mut r[h + n..2 * n] {
        let sum = Wide::from(*limb).wrapping_add(carry);
        *limb = sum as Limb;
        carry = sum >> Limb::BITS;
    }
}

/// Writes `x^2` into `t[..2n]`, `n` the length of `x`. `t`'s limbs start at
/// zero.
#[inline]
fn sqr_schoolbook(t: &mut [Limb], x: &[Limb]) {
    let n = x.len();
    for i in 0..n {
        t[i + n] = mul_add(&mut t[2 * i + 1..i + n], &x[i + 1..], x[i]) as Limb;
    }

    // The products sum to below x^2 / 2, so doubling them cannot overflow.
    let mut out = 0;
    for t in &mut t[..2 * n] {
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
}

/// The split square against the schoolbook one, at every width it can take.
#[cfg(test)]
mod sqr_split {
    use super::{Limb, MAX_LIMBS, sqr_product, sqr_schoolbook};

    #[test]
    fn matches_schoolbook() {
        let mut state = 0x1234_5678_9abc_def0u64;
        let mut next = || {
            state = state
                .wrapping_mul(0x5851_f42d_4c95_7f2d)
                .wrapping_add(0x1405_7b7e_f767_814f);
            state as Limb
        };
        let mut ns: Vec<usize> = (1..=128).collect();
        if MAX_LIMBS >= 256 {
            ns.push(256);
        }
        for n in ns {
            for _ in 0..3 {
                let a: Vec<Limb> = (0..n).map(|_| next()).collect();
                let mut got = vec![0; 2 * n];
                let mut want = vec![0; 2 * n];
                sqr_product(&mut got, &a);
                sqr_schoolbook(&mut want, &a);
                assert_eq!(got, want, "n={n}");
            }
            let ones = vec![Limb::MAX; n];
            let mut got = vec![0; 2 * n];
            let mut want = vec![0; 2 * n];
            sqr_product(&mut got, &ones);
            sqr_schoolbook(&mut want, &ones);
            assert_eq!(got, want, "ones n={n}");
        }
    }
}
