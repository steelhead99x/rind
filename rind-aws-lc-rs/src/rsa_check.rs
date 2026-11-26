//! `RSA_check_key` for a two-prime RSA private key of a size rind cannot sign
//! with, so that a PKCS#8 loader can tell a key aws-lc parses (refused as
//! another algorithm, `WrongAlgorithm`) from one it does not
//! (`InvalidEncoding`). aws-lc's `RSA_parse_private_key`
//! (`crypto/rsa_extra/rsa_asn1.c`) ends in `RSA_check_key`
//! (`crypto/fipsmodule/rsa/rsa.c`), which checks the relations below; rind
//! checks the same for the keys it loads (`mid::rsa_priv`), only at 2048 to
//! 8192 bits.
//!
//! Every private component is secret. Each is read at the width of its
//! encoding, which DER makes public anyway, and every operation below runs
//! over those widths with no branch or memory index on a value: products are
//! schoolbook, remainders are bit-serial with a masked subtraction, and
//! comparisons fold into one mask, of which only the final verdict is made
//! public, through rind's constant-time comparison.

use alloc::vec;
use alloc::vec::Vec;

use crate::der::RsaPrivateParts;

/// aws-lc's largest modulus (`kMaxModulusBits`, 16384 bits): a key above it
/// does not parse.
const MAX_MODULUS_BYTES: usize = 16384 / 8;

/// Whether `key` is consistent as `RSA_check_key` requires: the six private
/// INTEGERs minimal and non-negative, p and q odd, n = p q, dp = d mod
/// (p - 1), dq = d mod (q - 1), d e = 1 modulo p - 1 and q - 1 (so modulo
/// their lcm), qinv below p, and q qinv = 1 mod p.
///
/// `d` may be wider than `n`, as rind's own check allows; a `d` more than
/// twice `n`'s width is refused here to keep the cost bounded.
pub(crate) fn consistent(key: &RsaPrivateParts<'_>) -> bool {
    if key.n.len() > MAX_MODULUS_BYTES {
        return false;
    }
    let [d, p, q, dp, dq, qinv] = key.private;
    if d.len() > 2 * key.n.len() + 1
        || [p, q, dp, dq, qinv]
            .iter()
            .any(|v| v.len() > key.n.len() + 1)
    {
        return false;
    }
    let mut ok = u64::MAX;
    for field in key.private {
        ok &= valid_integer(field);
    }
    let n = limbs(key.n);
    let e = limbs(key.e);
    let (d, p, q, dp, dq, qinv) = (
        limbs(d),
        limbs(p),
        limbs(q),
        limbs(dp),
        limbs(dq),
        limbs(qinv),
    );
    ok &= odd(&p) & odd(&q);
    ok &= equal(&mul(&p, &q), &n);
    // p and q are odd, so p - 1 and q - 1 clear only the low bit.
    let p1 = minus_one_odd(&p);
    let q1 = minus_one_odd(&q);
    ok &= equal(&rem(&d, &p1), &dp);
    ok &= equal(&rem(&d, &q1), &dq);
    let de = mul(&d, &e);
    ok &= equal(&rem(&de, &p1), &[1]);
    ok &= equal(&rem(&de, &q1), &[1]);
    ok &= less(&qinv, &p);
    ok &= equal(&rem(&mul(&q, &qinv), &p), &[1]);
    rind::constant_time::verify(&ok.to_le_bytes(), &u64::MAX.to_le_bytes()).is_ok()
}

/// All ones if `contents` is a minimal non-negative INTEGER encoding, as
/// `CBS_is_unsigned_asn1_integer` requires, else zero; read without a branch
/// on its bytes. The DER reader already refused empty contents.
fn valid_integer(contents: &[u8]) -> u64 {
    let first = u64::from(contents.first().copied().unwrap_or(0x80));
    let negative = first >> 7;
    let padded = match contents.get(1) {
        // A leading zero is allowed only before a byte with its top bit set.
        Some(&second) => is_zero(first) & (1 ^ (u64::from(second) >> 7)),
        None => 0,
    };
    ((1 ^ negative) & (1 ^ padded)).wrapping_neg()
}

/// 1 if `x` is zero, else 0, without a branch.
fn is_zero(x: u64) -> u64 {
    1 ^ ((x | x.wrapping_neg()) >> 63)
}

/// A big-endian value as little-endian limbs, as many as its length needs.
fn limbs(bytes: &[u8]) -> Vec<u64> {
    let mut out = vec![0u64; bytes.len().div_ceil(8).max(1)];
    for (i, byte) in bytes.iter().rev().enumerate() {
        out[i / 8] |= u64::from(*byte) << (8 * (i % 8));
    }
    out
}

fn limb(a: &[u64], i: usize) -> u64 {
    a.get(i).copied().unwrap_or(0)
}

/// All ones if `a` is odd, else zero.
fn odd(a: &[u64]) -> u64 {
    (a[0] & 1).wrapping_neg()
}

/// `a - 1` for an odd `a`: the low bit cleared. (For an even `a`, which
/// [`odd`] has already failed, the result is wrong but harmless.)
fn minus_one_odd(a: &[u64]) -> Vec<u64> {
    let mut out = a.to_vec();
    out[0] &= !1;
    out
}

/// All ones if `a` and `b` are equal as numbers, whatever their widths.
fn equal(a: &[u64], b: &[u64]) -> u64 {
    let mut diff = 0;
    for i in 0..a.len().max(b.len()) {
        diff |= limb(a, i) ^ limb(b, i);
    }
    is_zero(diff).wrapping_neg()
}

/// All ones if `a < b`, else zero.
fn less(a: &[u64], b: &[u64]) -> u64 {
    let mut borrow = 0u64;
    for i in 0..a.len().max(b.len()) {
        let (d, b1) = limb(a, i).overflowing_sub(limb(b, i));
        let (_, b2) = d.overflowing_sub(borrow);
        borrow = u64::from(b1 | b2);
    }
    borrow.wrapping_neg()
}

/// `a * b`, schoolbook, `a.len() + b.len()` limbs.
fn mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut out = vec![0u64; a.len() + b.len()];
    for (i, &bi) in b.iter().enumerate() {
        let mut carry = 0u128;
        for (j, &aj) in a.iter().enumerate() {
            let t = u128::from(out[i + j]) + u128::from(aj) * u128::from(bi) + carry;
            out[i + j] = t as u64;
            carry = t >> 64;
        }
        out[i + a.len()] = carry as u64;
    }
    out
}

/// `x mod m`, bit-serial: shift each bit of `x` in from the top, then
/// subtract `m` where the remainder is not below it, selected by mask. Works
/// for an even `m`, which Montgomery reduction would not. For `m` = 0 (p or
/// q of 1) it returns `x` cut to `m`'s width; `d e = 1` then cannot hold,
/// since e is at least 3.
fn rem(x: &[u64], m: &[u64]) -> Vec<u64> {
    // One limb more than m, so the shift cannot overflow.
    let width = m.len() + 1;
    let mut r = vec![0u64; width];
    let mut t = vec![0u64; width];
    for bit in (0..64 * x.len()).rev() {
        let mut carry = (x[bit / 64] >> (bit % 64)) & 1;
        for limb in &mut r {
            let next = *limb >> 63;
            *limb = (*limb << 1) | carry;
            carry = next;
        }
        // t = r - m; keep it where there was no borrow, so r >= m.
        let mut borrow = 0u64;
        for (i, out) in t.iter_mut().enumerate() {
            let (d, b1) = r[i].overflowing_sub(limb(m, i));
            let (d, b2) = d.overflowing_sub(borrow);
            *out = d;
            borrow = u64::from(b1 | b2);
        }
        // `black_box`, so LLVM cannot turn the masked select into a branch
        // on the borrow, as it otherwise does.
        let keep = core::hint::black_box(borrow.wrapping_sub(1));
        for (r, t) in r.iter_mut().zip(&t) {
            *r = (*t & keep) | (*r & !keep);
        }
    }
    r.truncate(m.len());
    r
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(v: u128) -> Vec<u64> {
        vec![v as u64, (v >> 64) as u64]
    }

    #[test]
    fn rem_matches_u128() {
        let values = [
            0u128,
            1,
            2,
            3,
            12,
            255,
            1 << 64,
            (1 << 64) - 1,
            u128::MAX,
            0xdead_beef_cafe_f00d_1234_5678_9abc_def0,
        ];
        let moduli = [1u128, 2, 3, 10, 12, 1 << 63, (1 << 64) + 6, u128::MAX];
        for &x in &values {
            for &m in &moduli {
                assert_eq!(
                    equal(&rem(&n(x), &n(m)), &n(x % m)),
                    u64::MAX,
                    "{x} mod {m}"
                );
            }
        }
        assert_eq!(equal(&rem(&n(5), &n(0)), &[5]), u64::MAX);
    }

    #[test]
    fn mul_and_compare() {
        let (a, b) = (0xffff_ffff_ffff_fffbu128, 0x1_0000_0000_0000_0003u128);
        let product = mul(&n(a), &n(b));
        let expected = {
            // a * b without u256: split b.
            let lo = a * (b & u128::from(u64::MAX));
            let hi = a * (b >> 64);
            let mut out = vec![lo as u64, (lo >> 64) as u64, 0, 0];
            let mut carry = 0u128;
            for (i, part) in [hi as u64, (hi >> 64) as u64].into_iter().enumerate() {
                let t = u128::from(out[i + 1]) + u128::from(part) + carry;
                out[i + 1] = t as u64;
                carry = t >> 64;
            }
            out[3] = out[3].wrapping_add(carry as u64);
            out
        };
        assert_eq!(equal(&product, &expected), u64::MAX);
        assert_eq!(less(&n(3), &n(4)), u64::MAX);
        assert_eq!(less(&n(4), &n(4)), 0);
        assert_eq!(less(&[0, 1], &[5]), 0);
        assert_eq!(equal(&[7, 0, 0], &[7]), u64::MAX);
        assert_eq!(equal(&[7, 1], &[7]), 0);
    }

    #[test]
    fn integer_encodings() {
        assert_eq!(valid_integer(&[0x01]), u64::MAX);
        assert_eq!(valid_integer(&[0x00]), u64::MAX);
        assert_eq!(valid_integer(&[0x00, 0x80]), u64::MAX);
        assert_eq!(valid_integer(&[0x00, 0x7f]), 0);
        assert_eq!(valid_integer(&[0x80]), 0);
        assert_eq!(valid_integer(&[0xff, 0x01]), 0);
    }
}
