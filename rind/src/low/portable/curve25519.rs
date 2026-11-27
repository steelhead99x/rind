// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! X25519 on curve25519-dalek's serial backend, which clamps the scalar and
//! masks the point's top bit as RFC7748 requires. dalek's precomputed Edwards
//! table serves the fixed base.

use curve25519_dalek::montgomery::MontgomeryPoint;

/// res := X25519(scalar, point), in little-endian words.
pub(crate) fn curve25519_x25519(res: &mut [u64; 4], scalar: &[u64; 4], point: &[u64; 4]) {
    *res = from_bytes(
        &MontgomeryPoint(to_bytes(point))
            .mul_clamped(to_bytes(scalar))
            .0,
    );
}

/// res := X25519(scalar, 9), in little-endian words.
pub(crate) fn curve25519_x25519base(res: &mut [u64; 4], scalar: &[u64; 4]) {
    *res = from_bytes(&MontgomeryPoint::mul_base_clamped(to_bytes(scalar)).0);
}

// These are `mid::util`'s `u64x4_to_little_endian` and
// `little_endian_to_u64x4`, which `low` cannot call, character for
// character, so that `proofs/Rind/Armv7/Curve25519.lean` proves them the same
// functions and reuses those functions' proofs: the zip of a mutable iterator
// they replace, Aeneas translates through backward functions no proof here
// reasons about.
pub(crate) fn to_bytes(v: &[u64; 4]) -> [u8; 32] {
    let mut r = [0u8; 4 * 8];
    for (i, word) in v.iter().enumerate() {
        r[i * 8..(i + 1) * 8].copy_from_slice(&word.to_le_bytes());
    }
    r
}

// `as_chunks` here would no longer be `mid::util`'s code.
#[allow(clippy::chunks_exact_to_as_chunks)]
pub(crate) fn from_bytes(b: &[u8; 32]) -> [u64; 4] {
    let mut r = [0; 4];
    for (ir, b) in (0..4).zip(b.chunks_exact(8)) {
        r[ir] = u64::from_le_bytes(b.try_into().unwrap());
    }
    r
}
