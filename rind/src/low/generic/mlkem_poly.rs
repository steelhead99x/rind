// Copyright (c) The mlkem-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

//! ML-KEM's polynomial arithmetic in natural coefficient order, for armv7 and
//! x86_64 CPUs without AVX2: a Rust port of mlkem-native's portable C
//! (`poly.c`, `poly_k.c`, `compress.c`, and `sampling.c`, as aws-lc
//! 5ed12cce0fd4453f2f63300d44325ed14f845d6f vendors it), whose contracts
//! s2n-bignum's routines share. mlkem-native's CBMC proofs of its C do not
//! cover this port; rind's tests check it against s2n-bignum's AVX2 routines.
//!
//! Coefficient arithmetic wraps: the bounds rule out overflow, and a debug
//! build's overflow check would branch on secret values.
const Q: i16 = 3329;

/// mlkem-native's `mlk_zetas`: powers of 17, bit-reversed, in Montgomery form.
const ZETAS: [i16; 128] = [
    -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577, 182, 962, -1202, -1474, 1468,
    573, -1325, 264, 383, -829, 1458, -1602, -130, -681, 1017, 732, 608, -1542, 411, -205, -1571,
    1223, 652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666, -1618, -1162, 126, 1469,
    -853, -90, -271, 830, 107, -1421, -247, -951, -398, 961, -1508, -725, 448, -1065, 677, -1275,
    -1103, 430, 555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235, -291, -460, 1574, 1653, -246,
    778, 1159, -147, -777, 1483, -602, 1119, -1590, 644, -872, 349, 418, 329, -156, -75, 817, 1097,
    603, 610, 1322, -1285, -1465, 384, -1215, -136, 1218, -1335, -874, 220, -1187, -1659, -1185,
    -1530, -1278, 794, -1510, -854, -870, 478, -108, -308, 996, 991, 958, -1460, 1522, 1628,
];

/// `a * 2^-16 mod q`, with `|result| < q` for `|a| < 2^15 * q`.
#[inline(always)]
fn montgomery_reduce(a: i32) -> i16 {
    const QINV: u16 = 62209; // q^-1 mod 2^16
    let t = (a as u16).wrapping_mul(QINV) as i16;
    (a.wrapping_sub((t as i32).wrapping_mul(Q as i32)) >> 16) as i16
}

/// `a * b * 2^-16 mod q`, with `|result| < q` for `|b| <= q / 2`.
#[inline(always)]
fn fqmul(a: i16, b: i16) -> i16 {
    montgomery_reduce((a as i32).wrapping_mul(b as i32))
}

/// `a mod q`, with `|result| <= q / 2`.
#[inline(always)]
fn barrett_reduce(a: i16) -> i16 {
    const MAGIC: i32 = 20159; // round(2^26 / q)
    let t = MAGIC.wrapping_mul(a as i32).wrapping_add(1 << 25) >> 26;
    a.wrapping_sub((t as i16).wrapping_mul(Q))
}

/// Forward number-theoretic transform from ML-KEM, in natural order.
pub(crate) fn mlkem_ntt(r: &mut [i16; 256]) {
    let mut k = 1;
    let mut len = 128;
    while len >= 2 {
        for block in r.chunks_exact_mut(2 * len) {
            let zeta = ZETAS[k];
            k += 1;
            let (lo, hi) = block.split_at_mut(len);
            for (lo, hi) in lo.iter_mut().zip(hi.iter_mut()) {
                let t = fqmul(*hi, zeta);
                *hi = lo.wrapping_sub(t);
                *lo = lo.wrapping_add(t);
            }
        }
        len >>= 1;
    }
}

/// Inverse number-theoretic transform from ML-KEM, in natural order, mapping
/// the result into the Montgomery domain.
pub(crate) fn mlkem_intt(r: &mut [i16; 256]) {
    const F: i16 = 1441; // 2^32 / 128 mod q
    for x in r.iter_mut() {
        *x = fqmul(*x, F);
    }
    let mut k = 127;
    let mut len = 2;
    while len <= 128 {
        for block in r.chunks_exact_mut(2 * len) {
            let zeta = ZETAS[k];
            k -= 1;
            let (lo, hi) = block.split_at_mut(len);
            for (lo, hi) in lo.iter_mut().zip(hi.iter_mut()) {
                let t = *lo;
                *lo = barrett_reduce(t.wrapping_add(*hi));
                *hi = fqmul(hi.wrapping_sub(t), zeta);
            }
        }
        len <<= 1;
    }
}

/// Precompute the mulcache data for a polynomial in the NTT domain.
pub(crate) fn mlkem_mulcache_compute(x: &mut [i16; 128], a: &[i16; 256]) {
    let (x, _) = x.as_chunks_mut::<2>();
    let (a, _) = a.as_chunks::<4>();
    for ((x, a), zeta) in x.iter_mut().zip(a).zip(&ZETAS[64..]) {
        x[0] = fqmul(a[1], *zeta);
        x[1] = fqmul(a[3], -*zeta);
    }
}

/// Scalar product of 2-element polynomial vectors in the NTT domain, with
/// the mulcache `bt` of `b`.
pub(crate) fn mlkem_basemul_k2(
    r: &mut [i16; 256],
    a: &[i16; 512],
    b: &[i16; 512],
    bt: &[i16; 256],
) {
    basemul::<2>(r, a, b, bt);
}

/// Scalar product of 3-element polynomial vectors in the NTT domain, with
/// the mulcache `bt` of `b`.
pub(crate) fn mlkem_basemul_k3(
    r: &mut [i16; 256],
    a: &[i16; 768],
    b: &[i16; 768],
    bt: &[i16; 384],
) {
    basemul::<3>(r, a, b, bt);
}

/// Scalar product of 4-element polynomial vectors in the NTT domain, with
/// the mulcache `bt` of `b`.
pub(crate) fn mlkem_basemul_k4(
    r: &mut [i16; 256],
    a: &[i16; 1024],
    b: &[i16; 1024],
    bt: &[i16; 512],
) {
    basemul::<4>(r, a, b, bt);
}

/// Scalar product of `K`-element polynomial vectors: mlkem-native's
/// `polyvec_basemul_acc_montgomery_cached`.
fn basemul<const K: usize>(r: &mut [i16; 256], a: &[i16], b: &[i16], bt: &[i16]) {
    for i in 0..128 {
        let mut t0 = 0i32;
        let mut t1 = 0i32;
        for k in 0..K {
            let (a0, a1) = (a[256 * k + 2 * i] as i32, a[256 * k + 2 * i + 1] as i32);
            let (b0, b1) = (b[256 * k + 2 * i] as i32, b[256 * k + 2 * i + 1] as i32);
            t0 = t0
                .wrapping_add(a1.wrapping_mul(bt[128 * k + i] as i32))
                .wrapping_add(a0.wrapping_mul(b0));
            t1 = t1
                .wrapping_add(a0.wrapping_mul(b1))
                .wrapping_add(a1.wrapping_mul(b0));
        }
        r[2 * i] = montgomery_reduce(t0);
        r[2 * i + 1] = montgomery_reduce(t1);
    }
}

/// Canonical reduction of polynomial coefficients for ML-KEM, to `0..q`.
pub(crate) fn mlkem_reduce(r: &mut [i16; 256]) {
    for x in r.iter_mut() {
        let t = barrett_reduce(*x);
        *x = t.wrapping_add((t >> 15) & Q);
    }
}

/// Conversion of ML-KEM polynomial coefficients to Montgomery form.
pub(crate) fn mlkem_tomont(r: &mut [i16; 256]) {
    const F: i16 = 1353; // 2^32 mod q
    for x in r.iter_mut() {
        *x = fqmul(*x, F);
    }
}

/// Pack ML-KEM polynomial coefficients as 12-bit numbers.
pub(crate) fn mlkem_tobytes(r: &mut [u8; 384], a: &[i16; 256]) {
    let (r, _) = r.as_chunks_mut::<3>();
    let (a, _) = a.as_chunks::<2>();
    for (r, a) in r.iter_mut().zip(a) {
        let (t0, t1) = (a[0] as u16, a[1] as u16);
        r[0] = t0 as u8;
        r[1] = ((t0 >> 8) | (t1 << 4)) as u8;
        r[2] = (t1 >> 4) as u8;
    }
}

/// Rejection sampling of SHAKE128 bytes `input` into coefficients below q,
/// returning how many of `r` were written. Its time depends on which
/// candidates are rejected, which is public: the bytes expand the public
/// seed `rho`.
pub(crate) fn mlkem_rej_uniform_vartime(r: &mut [i16; 256], input: &[u8]) -> u64 {
    let mut ctr = 0;
    let (chunks, _) = input.as_chunks::<3>();
    for b in chunks {
        if ctr == r.len() {
            break;
        }
        let v0 = (b[0] as i16 | ((b[1] as i16) << 8)) & 0xfff;
        let v1 = ((b[1] >> 4) as i16 | ((b[2] as i16) << 4)) & 0xfff;
        if v0 < Q {
            r[ctr] = v0;
            ctr += 1;
        }
        if ctr < r.len() && v1 < Q {
            r[ctr] = v1;
            ctr += 1;
        }
    }
    ctr as u64
}
