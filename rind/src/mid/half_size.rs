// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Half-size scalars for Ed25519 verification, after ElSheikh, Keskinkurt
//! Paksoy, Cenk, and Hasan, "Accelerating EdDSA Signature Verification with
//! Faster Scalar Size Halving" (TCHES 2025, issue 3).
//!
//! Verification checks `D = [S]B - [k]A - R` is the identity. For any `u`
//! and `v` with `u ≡ v k (mod 8L)`, `[v]D = [v S mod L]B - [v]R - [u]A`,
//! since every point of edwards25519 has order dividing `8L` and `B` order
//! `L`. When `v` is odd and below `L` it is prime to `8L`, so multiplying by
//! it permutes the group, and `[v]D` is the identity exactly when `D` is:
//! the check accepts what the plain one does, whatever torsion `A` and `R`
//! carry. Solving modulo `8L` rather than the paper's `L` is what makes that
//! hold for points outside the prime-order subgroup.
//!
//! [`split`] finds `u` and `v` of about 128 bits each, by the extended
//! Euclidean algorithm on `8L` and `k`, stopped halfway. Its inputs are
//! public, so it runs in variable time.

/// `8L`, for `L` the order of edwards25519's base point.
const ORDER_TIMES_8: [u64; 4] = [
    0xc09318d2e7ae9f68,
    0xa6f7cef517bce6b2,
    0x0000000000000000,
    0x8000000000000000,
];

/// `u` and `v` with `u ≡ v k (mod 8L)`, `v` odd, and `0 < v < 2^128`.
#[derive(Debug)]
pub(crate) struct Split {
    /// `|u|`, below 2^255.
    pub(crate) u: [u64; 4],
    /// Whether `u` is negative.
    pub(crate) u_negative: bool,
    /// `v`.
    pub(crate) v: [u64; 4],
}

/// Splits `k < 2^255` as [`Split`] describes.
pub(crate) fn split(k: &[u64; 4]) -> Split {
    // Each row (r, t) has r ≡ t k (mod 8L): (8L, 0) and (k, 1) to start,
    // and every step subtracts a multiple of one row from the other. The
    // steps keep the rows' matrix unimodular, so the two t are coprime, and
    // keep r0 |t1| + r1 |t0| = 8L with t0 and t1 of opposite signs: the row
    // from 8L keeps t <= 0, the row from k keeps t >= 0, so only magnitudes
    // are stored, with which row is which. k < 2^255 < 8L, so k's row
    // starts as the smaller.
    let mut big = Row {
        r: U256::from(&ORDER_TIMES_8),
        t: 0,
        from_k: false,
    };
    let mut small = Row {
        r: U256::from(k),
        t: 1,
        from_k: true,
    };

    // While small.r >= 2^128, |t| <= 8L / 2^128 < 2^127 + 1 in both rows,
    // so neither magnitude, nor a shift of one below the other's sum,
    // overflows.
    while small.r.hi != 0 {
        // The largest shift with small.r << shift <= big.r, which leaves
        // big.r below half of what it was.
        let mut shift = big.r.bits() - small.r.bits();
        if small.r.shl(shift) > big.r {
            shift -= 1;
        }
        big.r = big.r.sub(&small.r.shl(shift));
        big.t += small.t << shift;
        if big.r < small.r {
            core::mem::swap(&mut big, &mut small);
        }
    }

    // small.r < 2^128 <= big.r, so |small.t| <= 8L / big.r <= 2^127. One t
    // is odd, as the two are coprime. With small.t even, big's row has an
    // odd t, as does their difference, whose t is the sum of magnitudes:
    // take whichever has the shorter longest part.
    let (r, t, from_k) = if small.t & 1 == 1 {
        (small.r, small.t, small.from_k)
    } else {
        let difference = small.t.checked_add(big.t).map(|t| (big.r.sub(&small.r), t));
        match difference {
            Some((r, t)) if r.bits().max(bits(t)) < big.r.bits().max(bits(big.t)) => {
                (r, t, big.from_k)
            }
            _ => (big.r, big.t, big.from_k),
        }
    };

    // The row from k has t >= 0, so v = t and u = r. The other has t <= 0,
    // so negate both: v = |t| and u = -r.
    Split {
        u: r.words(),
        u_negative: !from_k,
        v: [t as u64, (t >> 64) as u64, 0, 0],
    }
}

/// A row of the extended Euclidean algorithm: `r ≡ ±t k (mod 8L)`.
struct Row {
    r: U256,
    /// `|t|`.
    t: u128,
    /// Whether this row began as `(k, 1)`, so its `t` is nonnegative.
    from_k: bool,
}

fn bits(x: u128) -> u32 {
    128 - x.leading_zeros()
}

/// A 256-bit number as two halves.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct U256 {
    hi: u128,
    lo: u128,
}

impl U256 {
    fn from(x: &[u64; 4]) -> Self {
        Self {
            hi: u128::from(x[2]) | u128::from(x[3]) << 64,
            lo: u128::from(x[0]) | u128::from(x[1]) << 64,
        }
    }

    fn words(&self) -> [u64; 4] {
        [
            self.lo as u64,
            (self.lo >> 64) as u64,
            self.hi as u64,
            (self.hi >> 64) as u64,
        ]
    }

    fn bits(&self) -> u32 {
        match self.hi {
            0 => bits(self.lo),
            hi => 128 + bits(hi),
        }
    }

    /// `self << shift`, for `shift < 128` and no bits shifted out: `split`
    /// shifts only a row of at least 2^128 toward one below 2^256.
    fn shl(&self, shift: u32) -> Self {
        match shift {
            0 => *self,
            s => Self {
                hi: self.hi << s | self.lo >> (128 - s),
                lo: self.lo << s,
            },
        }
    }

    /// `self - other`, for `other <= self`.
    fn sub(&self, other: &Self) -> Self {
        let (lo, borrow) = self.lo.overflowing_sub(other.lo);
        Self {
            hi: self.hi - other.hi - u128::from(borrow),
            lo,
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    /// `L`, little-endian.
    const ORDER: [u64; 4] = [
        0x5812631a5cf5d3ed,
        0x14def9dea2f79cd6,
        0x0000000000000000,
        0x1000000000000000,
    ];

    /// `x * y` for `y < 2^128`, as eight words.
    fn mul(x: &[u64; 4], y: &[u64; 4]) -> [u64; 8] {
        let mut z = [0u64; 8];
        for (i, &xi) in x.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &yj) in y.iter().enumerate() {
                let t = u128::from(xi) * u128::from(yj) + u128::from(z[i + j]) + carry;
                z[i + j] = t as u64;
                carry = t >> 64;
            }
            z[i + 4] = carry as u64;
        }
        z
    }

    /// `x + y` or, for `x >= y`, `x - y`, over eight words.
    fn add_or_sub(x: &[u64; 8], y: &[u64; 4], sub: bool) -> [u64; 8] {
        let mut z = [0u64; 8];
        let mut carry = 0i128;
        for i in 0..8 {
            let yi = i128::from(*y.get(i).unwrap_or(&0));
            let t = i128::from(x[i]) + carry + if sub { -yi } else { yi };
            z[i] = t as u64;
            carry = t >> 64;
        }
        assert_eq!(carry, 0);
        z
    }

    /// `x mod 8L`, by long division.
    fn reduce(x: &[u64; 8]) -> U256 {
        let n = U256::from(&ORDER_TIMES_8);
        // Below 2 * 8L < 2^257, so the top bit is kept apart.
        let mut rem = U256 { hi: 0, lo: 0 };
        for i in (0..512).rev() {
            let top = rem.hi >> 127;
            rem = rem.shl(1);
            rem.lo |= u128::from(x[i / 64] >> (i % 64) & 1);
            if top == 1 || rem >= n {
                // Wrapping: with the top bit set, rem + 2^256 - 8L fits.
                let (lo, borrow) = rem.lo.overflowing_sub(n.lo);
                rem.hi = rem.hi.wrapping_sub(n.hi).wrapping_sub(u128::from(borrow));
                rem.lo = lo;
            }
        }
        rem
    }

    fn check(k: &[u64; 4]) -> u32 {
        let mut n = ORDER.map(u128::from);
        let mut carry = 0;
        for limb in &mut n {
            *limb = *limb * 8 + carry;
            carry = *limb >> 64;
            *limb &= u128::from(u64::MAX);
        }
        assert_eq!(n.map(|l| l as u64), ORDER_TIMES_8);

        let s = split(k);
        let vk = mul(k, &s.v);
        // v k - u ≡ 0 (mod 8L): v k + |u| for negative u; otherwise
        // whichever of v k - u and u - v k is nonnegative.
        let difference = match s.u_negative {
            true => add_or_sub(&vk, &s.u, false),
            false => match vk[4..] == [0; 4]
                && U256::from(vk[..4].try_into().unwrap()) < U256::from(&s.u)
            {
                true => {
                    let mut u = [0; 8];
                    u[..4].copy_from_slice(&s.u);
                    add_or_sub(&u, vk[..4].try_into().unwrap(), true)
                }
                false => add_or_sub(&vk, &s.u, true),
            },
        };
        assert!(
            reduce(&difference) == U256 { hi: 0, lo: 0 },
            "{k:x?}: {s:x?}"
        );
        assert!(s.v[0] & 1 == 1, "{k:x?}: {s:x?}");
        assert_eq!(s.v[2..], [0, 0], "{k:x?}: {s:x?}");
        assert!(s.u[3] >> 63 == 0, "{k:x?}: {s:x?}");
        U256::from(&s.u).bits().max(U256::from(&s.v).bits())
    }

    #[test]
    fn edges() {
        let mut l_minus_1 = ORDER;
        l_minus_1[0] -= 1;
        for k in [
            [0, 0, 0, 0],
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            [u64::MAX, u64::MAX, 0, 0],
            [0, 0, 1, 0],
            [0, 0, 2, 0],
            l_minus_1,
            ORDER,
            // 2^255 - 1, above every reduced k.
            [u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1],
        ] {
            check(&k);
        }
    }

    #[test]
    fn random_scalars_split_in_half() {
        let mut x = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        // Each split's longest part sets how many doublings verification
        // runs, so on average it should cost under one past 128.
        let rounds = 100_000;
        let mut total = 0;
        for _ in 0..rounds {
            let k = [next(), next(), next(), next() >> 4];
            total += check(&k).max(128);
        }
        assert!(
            total < 129 * rounds,
            "{}",
            f64::from(total) / f64::from(rounds)
        );
    }
}
