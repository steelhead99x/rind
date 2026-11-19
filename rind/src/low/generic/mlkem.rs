// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// Unpack ML-KEM polynomial coefficients as 12-bit numbers
///
/// Input a[384] (bytes); output r[256] (signed 16-bit words)
///
/// This accepts an array of 384 bytes and unpacks them into 256 16-bit numbers
/// in the range 0 <= a[i] < 2^12 (typically they will be < 3329, the ML-KEM prime).
pub(crate) fn mlkem_frombytes(r: &mut [i16; 256], a: &[u8; 384]) {
    // Counted, not zipped: the proof is about Aeneas's translation, which
    // takes no iterator adapter.
    for i in 0..128 {
        let (a0, a1, a2) = (a[3 * i], a[3 * i + 1], a[3 * i + 2]);
        r[2 * i] = (a0 as i16) | (((a1 & 0x0f) as i16) << 8);
        r[2 * i + 1] = ((a1 >> 4) as i16) | ((a2 as i16) << 4);
    }
}

/// Reorder ML-KEM polynomial coefficients for the current implementation
///
/// Input/output a[256] (signed 16-bit words)
///
/// This reorders coefficients from their natural order into the order
/// used by the rest of the implementation.  The x86_64 AVX2 version of this
/// function produces the layout required by the AVX2 NTT; this
/// implementation (and the functions it works alongside, like
/// [`mlkem_frombytes`]) uses the natural order, so there is nothing to do.
pub(crate) fn mlkem_unpack(_a: &mut [i16; 256]) {}

/// Compress ML-KEM polynomial coefficients to 4 bits each, and pack them
///
/// Input a[256] (signed 16-bit words, each in `[0, Q)`); output r[128] (bytes)
pub(crate) fn mlkem_compress_d4(r: &mut [u8; 128], a: &[i16; 256]) {
    compress::<4, 128>(r, a);
}

/// Compress ML-KEM polynomial coefficients to 5 bits each, and pack them
///
/// Input a[256] (signed 16-bit words, each in `[0, Q)`); output r[160] (bytes)
pub(crate) fn mlkem_compress_d5(r: &mut [u8; 160], a: &[i16; 256]) {
    compress::<5, 160>(r, a);
}

/// Compress ML-KEM polynomial coefficients to 10 bits each, and pack them
///
/// Input a[256] (signed 16-bit words, each in `[0, Q)`); output r[320] (bytes)
pub(crate) fn mlkem_compress_d10(r: &mut [u8; 320], a: &[i16; 256]) {
    compress::<10, 320>(r, a);
}

/// Compress ML-KEM polynomial coefficients to 11 bits each, and pack them
///
/// Input a[256] (signed 16-bit words, each in `[0, Q)`); output r[352] (bytes)
pub(crate) fn mlkem_compress_d11(r: &mut [u8; 352], a: &[i16; 256]) {
    compress::<11, 352>(r, a);
}

/// FIPS 203's `ByteEncode_D(Compress_D(a))` into the `L = 32 * D` bytes of
/// `r`: each eight coefficients become `D` bytes, little-endian bit order per
/// `BitsToBytes`.
fn compress<const D: usize, const L: usize>(r: &mut [u8; L], a: &[i16; 256]) {
    debug_assert_eq!(L, 32 * D);
    for i in 0..32 {
        let mut bits = 0u128;
        for j in 0..8 {
            bits |= (compress_one::<D>(a[8 * i + j]) as u128) << (D * j);
        }
        r[D * i..D * i + D].copy_from_slice(&bits.to_le_bytes()[..D]);
    }
}

const Q: i16 = 3329;
const Q_HALF: i16 = (Q + 1) / 2;

/// `Compress_D(x) = round((2^D / q) * x) mod 2^D`, for x in [0, Q)
///
/// Division-free so no variable-time division instruction is emitted
/// (cf. KyberSlash): `(x * 2^D + q / 2) * M >> S` is `floor` of the quotient
/// by `q` for each `D`'s `M` and `S`, which `compress_is_exact` checks over
/// the whole input range.
#[expect(
    clippy::manual_range_contains,
    reason = "Aeneas's library has no `Range::contains`"
)]
fn compress_one<const D: usize>(x: i16) -> u16 {
    let public = crate::low::ct::into_public(x);
    debug_assert!(0 <= public && public < Q);
    let (m, s) = match D {
        4 | 5 => (80635, 28),
        10 => (1290167, 32),
        11 => (5160669, 34),
        _ => unreachable!(),
    };
    let c = x as u64;
    let c = c << D;
    let c = c.wrapping_add(Q_HALF as u64);
    let c = c.wrapping_mul(m);
    let c = c >> s;
    (c & ((1 << D) - 1)) as u16
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn unpacks_known_values() {
        let mut a = [0u8; 384];
        // first pair of coefficients: 0xabc and 0xdef, packed little-endian
        // per FIPS 203 ByteEncode_12
        a[0] = 0xbc;
        a[1] = 0xfa;
        a[2] = 0xde;

        let mut r = [0i16; 256];
        mlkem_frombytes(&mut r, &a);
        assert_eq!(r[0], 0xabc);
        assert_eq!(r[1], 0xdef);
        assert_eq!(&r[2..], &[0i16; 254]);
    }

    // Every input against FIPS 203's rounding, done with division.
    #[test]
    fn compress_is_exact() {
        fn check<const D: usize>() {
            for x in 0..Q {
                let want = ((((x as u32) << (D + 1)) + Q as u32) / (2 * Q as u32)) % (1 << D);
                assert_eq!(compress_one::<D>(x) as u32, want, "d{D}, {x}");
            }
        }
        check::<4>();
        check::<5>();
        check::<10>();
        check::<11>();
    }

    #[test]
    fn output_is_at_most_12_bits() {
        let a = [0xffu8; 384];
        let mut r = [0i16; 256];
        mlkem_frombytes(&mut r, &a);
        assert_eq!(r, [0xfff; 256]);
    }
}
