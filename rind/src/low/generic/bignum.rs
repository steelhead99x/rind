// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The s2n-bignum routines `low::PosInt` uses that need no multiplication,
//! with their contracts, in portable Rust for armv7 and the portable
//! backend; `mont` has those that multiply, and `safegcd` inversion and
//! coprimality.
//!
//! Each runs in time that depends only on its lengths, never on its values:
//! loops run a count fixed by those, and selects are masks. Arithmetic on
//! values wraps, though the bounds rule out overflow, since a debug build's
//! overflow check would branch on them.

/// The widest value any of these takes: an 8192-bit modulus.
pub(super) const MAX_WORDS: usize = 128;

/// Add, z := x + y
///
/// Inputs x[m], y[n]; outputs function return (carry-out) and z[p]
///
/// Truncates modulo p words, returning the carry out of the p'th place.
pub(crate) fn bignum_add(z: &mut [u64], x: &[u64], y: &[u64]) -> u64 {
    let mut carry = 0;
    for (i, z) in z.iter_mut().enumerate() {
        let (sum, c1) = word(x, i).overflowing_add(word(y, i));
        let (sum, c2) = sum.overflowing_add(carry);
        *z = sum;
        carry = u64::from(c1 | c2);
    }
    carry
}

/// Return size of bignum in bits
///
/// Input x[k]; output function return
///
/// In the case of a zero bignum as input the result is 0
pub(crate) fn bignum_bitsize(x: &[u64]) -> usize {
    let mut bits = 0;
    for (i, w) in x.iter().enumerate() {
        let here = (i as u64 * 64 + 64).wrapping_sub(u64::from(w.leading_zeros()));
        bits = select(nonzero(*w), here, bits);
    }
    bits as usize
}

/// Compare bignums, x < y
///
/// Inputs x[m], y[n]; output function return
pub(crate) fn bignum_cmp_lt(x: &[u64], y: &[u64]) -> u64 {
    let mut borrow = 0;
    for i in 0..x.len().max(y.len()) {
        let (diff, b1) = word(x, i).overflowing_sub(word(y, i));
        let (_, b2) = diff.overflowing_sub(borrow);
        borrow = u64::from(b1 | b2);
    }
    borrow
}

/// Given table: uint64_t[height*width], copy table[idx*width...(idx+1)*width-1]
///
/// into z[0..width-1], reading every row.
pub(crate) fn bignum_copy_row_from_table(
    z: &mut [u64],
    table: &[u64],
    height: u64,
    width: u64,
    index: u64,
) {
    let width = width as usize;
    let z = &mut z[..width];
    z.fill(0);
    // Indexed rather than `chunks_exact`, which divides by `width`, and
    // `admin/ct-vartime` refuses a division here.
    for row in 0..height as usize {
        let entry = &table[row * width..][..width];
        let keep = mask(nonzero(row as u64 ^ index) ^ 1);
        for (z, e) in z.iter_mut().zip(entry) {
            *z |= e & keep;
        }
    }
}

/// Count trailing zero digits (64-bit words)
///
/// Input x[k]; output function return
///
/// In the case of a zero bignum as input the result is 64 * k
pub(crate) fn bignum_ctz(x: &[u64]) -> usize {
    let mut zeros = 64 * x.len() as u64;
    for (i, w) in x.iter().enumerate().rev() {
        let here = (i as u64 * 64).wrapping_add(u64::from(w.trailing_zeros()));
        zeros = select(nonzero(*w), here, zeros);
    }
    zeros as usize
}

/// Return size of bignum in digits (64-bit word)
///
/// Input x[k]; output function return
///
/// In the case of a zero bignum as input the result is 0
pub(crate) fn bignum_digitsize(x: &[u64]) -> usize {
    let mut digits = 0;
    for (i, w) in x.iter().enumerate() {
        digits = select(nonzero(*w), i as u64 + 1, digits);
    }
    digits as usize
}

/// Add modulo m, z := (x + y) mod m, assuming x and y reduced
///
/// Inputs x[k], y[k], m[k]; output z[k]
pub(crate) fn bignum_modadd(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64]) {
    let carry = bignum_add(z, x, y);
    let below = bignum_cmp_lt(z, m);
    sub_masked(z, m, mask(carry | (below ^ 1)));
}

/// Subtract modulo m, z := (x - y) mod m, assuming x and y reduced
///
/// Inputs x[k], y[k], m[k]; output z[k]
pub(crate) fn bignum_modsub(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64]) {
    z.copy_from_slice(x);
    mod_sub_masked(z, y, m, u64::MAX);
}

/// Negated modular inverse, z := (-1/x) mod 2^{64k}
///
/// Input x[k]; output z[k]
///
/// For one word, as `PosInt` takes it, and an odd x.
pub(crate) fn bignum_negmodinv(z: &mut [u64], x: &[u64]) {
    assert!(z.len() == 1 && x.len() == 1);
    // Correct to 5 bits, then Newton's iteration doubles that each time.
    let x = x[0];
    let mut inv = x.wrapping_mul(3) ^ 2;
    for _ in 0..4 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(x.wrapping_mul(inv)));
    }
    z[0] = inv.wrapping_neg();
}

/// Optionally subtract, z := x - y (if p nonzero) or z := x (if p zero)
///
/// Inputs x[k], p, y[k]; output z[k]
pub(crate) fn bignum_optsub(z: &mut [u64], x: &[u64], y: &[u64], p: u64) {
    z.copy_from_slice(x);
    sub_masked(z, y, mask(nonzero(p)));
}

/// `x := x - y mod m` where `keep` is all ones, for `x` and `y` below `m`.
fn mod_sub_masked(x: &mut [u64], y: &[u64], m: &[u64], keep: u64) {
    let borrow = sub_masked(x, y, keep);
    add_masked(x, m, mask(borrow));
}

/// `x := x + y` where `keep` is all ones, returning the carry.
fn add_masked(x: &mut [u64], y: &[u64], keep: u64) -> u64 {
    let mut carry = 0;
    for (x, y) in x.iter_mut().zip(y) {
        let (sum, c1) = x.overflowing_add(y & keep);
        let (sum, c2) = sum.overflowing_add(carry);
        *x = sum;
        carry = u64::from(c1 | c2);
    }
    carry
}

/// `x := x - y` where `keep` is all ones, returning the borrow.
fn sub_masked(x: &mut [u64], y: &[u64], keep: u64) -> u64 {
    let mut borrow = 0;
    for (x, y) in x.iter_mut().zip(y) {
        let (diff, b1) = x.overflowing_sub(y & keep);
        let (diff, b2) = diff.overflowing_sub(borrow);
        *x = diff;
        borrow = u64::from(b1 | b2);
    }
    borrow
}

/// The `i`th word of `x`, or zero beyond its length.
pub(super) fn word(x: &[u64], i: usize) -> u64 {
    x.get(i).copied().unwrap_or(0)
}

/// One if `x` is nonzero, zero if not.
pub(super) fn nonzero(x: u64) -> u64 {
    (x | x.wrapping_neg()) >> 63
}

/// `x` where `bit` is one, `y` where it is zero.
pub(super) fn select(bit: u64, x: u64, y: u64) -> u64 {
    y ^ ((x ^ y) & mask(bit))
}

/// All ones for one and zero for zero, through `black_box` so the compiler
/// cannot turn the select it feeds into a branch.
fn mask(bit: u64) -> u64 {
    core::hint::black_box(0u64.wrapping_sub(bit))
}

/// Checks each routine against s2n-bignum's, word for word.
///
/// The values are marked secret, so under `admin/ctgrind` these also check
/// each routine is constant time in them.
#[cfg(all(test, any(rind_backend = "x86_64", rind_backend = "aarch64")))]
#[cfg_attr(coverage_nightly, coverage(off))]
pub(super) mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::low;
    use crate::low::ct::{into_public, into_secret, public_slice, secret_slice};
    use crate::test::bignum::{below, words};

    /// An odd modulus above one of up to `max` words, with its top word
    /// random, one, zero, or full, and two values below it.
    pub(in super::super) fn modulus(
        max: usize,
    ) -> impl Strategy<Value = (Vec<u64>, Vec<u64>, Vec<u64>)> {
        (1..=max, 0..4u8, any::<u64>()).prop_flat_map(|(k, top, seed)| {
            let m = prop::collection::vec(any::<u64>(), k).prop_map(move |mut m| {
                match top {
                    0 if k > 1 => m[k - 1] = 1,
                    1 if k > 2 => m[k - 1] = 0,
                    2 => m.fill(u64::MAX),
                    _ => {}
                }
                m[0] |= 1;
                if m == [1] {
                    m[0] = seed | 3;
                }
                m
            });
            m.prop_flat_map(|m| (Just(m.clone()), below(64, m.clone()), below(64, m)))
        })
    }

    /// A copy of `x` whose words, but not length, are secret.
    pub(in super::super) fn secret(x: &[u64]) -> Vec<u64> {
        let x = x.to_vec();
        secret_slice(&x);
        x
    }

    /// `x`'s words, made public to compare.
    pub(in super::super) fn public(x: &[u64]) -> Vec<u64> {
        public_slice(x);
        x.to_vec()
    }

    // The reference results are public but marked so anyway: memcheck can
    // count the secret arithmetic's stale flags against a flag a reference
    // routine sets itself, such as the `stc` before `bignum_add_p521`'s
    // `adc` chain on x86_64. See UPSTREAM.md, "Memcheck blames a public
    // flag on a secret carry".
    proptest! {
        #[test]
        fn plain(x in words(0, 8), y in words(0, 8), p in 0..12usize, index in 0..4u64) {
            let (sx, sy) = (secret(&x), secret(&y));
            let (mut ours, mut theirs) = (vec![0; p], vec![0; p]);
            let carry = bignum_add(&mut ours, &sx, &sy);
            prop_assert_eq!(into_public(carry), low::bignum_add(&mut theirs, &x, &y));
            prop_assert_eq!(public(&ours), theirs);

            prop_assert_eq!(into_public(bignum_cmp_lt(&sx, &sy)), low::bignum_cmp_lt(&x, &y));
            prop_assert_eq!(into_public(bignum_bitsize(&sx)), low::bignum_bitsize(&x));
            prop_assert_eq!(into_public(bignum_digitsize(&sx)), low::bignum_digitsize(&x));
            prop_assert_eq!(into_public(bignum_ctz(&sx)), low::bignum_ctz(&x));

            let k = x.len().min(y.len());
            let (mut ours, mut theirs) = (vec![0; k], vec![0; k]);
            bignum_optsub(&mut ours, &sx[..k], &sy[..k], index);
            low::bignum_optsub(&mut theirs, &x[..k], &y[..k], index);
            prop_assert_eq!(public(&ours), theirs);

            let width = x.len().min(y.len());
            if width > 0 {
                let table = [&x[..width], &y[..width], &vec![!0; width]].concat();
                let (mut ours, mut theirs) = (vec![0; width], vec![0; width]);
                bignum_copy_row_from_table(&mut ours, &table, 3, width as u64, into_secret(index));
                low::bignum_copy_row_from_table(&mut theirs, &table, 3, width as u64, index);
                prop_assert_eq!(public(&ours), theirs);
            }
        }

        #[test]
        fn modular((m, x, y) in modulus(20)) {
            let k = m.len();
            let (sm, sx, sy) = (secret(&m), secret(&x), secret(&y));
            let (mut ours, mut theirs) = (vec![0; k], vec![0; k]);

            bignum_modadd(&mut ours, &sx, &sy, &sm);
            low::bignum_modadd(&mut theirs, &x, &y, &m);
            prop_assert_eq!(public(&ours), theirs.clone());

            bignum_modsub(&mut ours, &sx, &sy, &sm);
            low::bignum_modsub(&mut theirs, &x, &y, &m);
            prop_assert_eq!(public(&ours), theirs);

            let (mut ours, mut theirs) = ([0], [0]);
            bignum_negmodinv(&mut ours, &sm[..1]);
            low::bignum_negmodinv(&mut theirs, &m[..1]);
            prop_assert_eq!(into_public(ours), into_public(theirs));
        }
    }

    // Only the top bit set is where an exclusive or of `x` and `-x` would
    // drop it.
    #[test]
    fn nonzero_at_the_top_bit() {
        assert_eq!((nonzero(0), nonzero(1), nonzero(1 << 63)), (0, 1, 1));
    }
}
