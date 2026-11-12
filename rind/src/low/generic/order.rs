// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! s2n-bignum's routines that are generic over an odd modulus, for armv7:
//! the arithmetic for the group orders it has, n_256, n_384, and n_521,
//! and `bignum`'s for any other modulus, as RSA's are. Montgomery
//! multiplication and its inverse serve only the group orders, and refuse
//! any other modulus.

use super::{bignum, p256, p384, p521};
use crate::low::{bignum_eq, ct};

/// z := x * y / 2^(64k) mod m, for m = n_256, n_384, or n_521 of k words
pub(crate) fn bignum_montmul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64]) {
    match m.len() {
        4 => p256::bignum_montmul(z, x, y, m),
        6 => p384::bignum_montmul(z, x, y, m),
        _ => p521::bignum_montmul(z, x, y, m),
    }
}

/// z := x / 2^(64k) mod m, for m = n_256, n_384, or n_521 of k words
pub(crate) fn bignum_demont(z: &mut [u64], x: &[u64], m: &[u64]) {
    match m.len() {
        4 => p256::bignum_demont(z, x, m),
        6 => p384::bignum_demont(z, x, m),
        _ => p521::bignum_demont(z, x, m),
    }
}

/// z := (x + y) mod m, assuming x and y reduced
pub(crate) fn bignum_modadd(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64]) {
    match order(m) {
        Some(Order::N256) => p256::bignum_modadd(z, x, y, m),
        Some(Order::N384) => p384::bignum_modadd(z, x, y, m),
        Some(Order::N521) => p521::bignum_modadd(z, x, y, m),
        None => bignum::bignum_modadd(z, x, y, m),
    }
}

/// z := a^-1 mod b, for an odd b > 1 coprime to a
pub(crate) fn bignum_modinv(z: &mut [u64], a: &[u64], b: &[u64], t: &mut [u64]) {
    match order(b) {
        Some(Order::N256) => p256::bignum_modinv(z, a, b, t),
        Some(Order::N384) => p384::bignum_modinv(z, a, b, t),
        Some(Order::N521) => p521::bignum_modinv(z, a, b, t),
        None => bignum::bignum_modinv(z, a, b, t),
    }
}

enum Order {
    N256,
    N384,
    N521,
}

/// Which group order `m` is, if any. An RSA modulus may be secret, so it is
/// compared in constant time, revealing only that it is no group order.
fn order(m: &[u64]) -> Option<Order> {
    let is = |n: &[u64]| m.len() == n.len() && ct::into_public(bignum_eq(m, n));
    if is(&p256::N) {
        Some(Order::N256)
    } else if is(&p384::N) {
        Some(Order::N384)
    } else if is(&p521::N) {
        Some(Order::N521)
    } else {
        None
    }
}
