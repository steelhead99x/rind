// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The narrow and `_alt` schedules compute the same values.
//!
//! Each routine is called on zero, one, an all-ones limb, and a mixed
//! pattern, and the curve routines also on a generator. The points are the
//! ones the scalar-multiplication proofs state: Montgomery Jacobian with
//! z = 1 for P-256 and P-384, and Jacobian with z = 1 for P-521. Field
//! elements at `p - 1`, `p`, and `p + k`, scalars at and above each group
//! order, and a point at infinity are included too.
//! `matches_portable` checks the narrow schedules against oracles other than
//! the wide schedule: a schoolbook reduction, curve25519-dalek, and the
//! generic backend. `random` repeats both checks on seeded pseudo-random
//! inputs. These tests compile only for aarch64, so they run on aarch64
//! hosts and in the aarch64 qemu CI job.

/// Both schedules agree, for every routine `wide_mux` dispatches.
pub(crate) fn agree() {
    let limbs = [
        [0; 4],
        [1, 0, 0, 0],
        [u64::MAX; 4],
        [
            0x0123_4567_89ab_cdef,
            0xfedc_ba98_7654_3210,
            0x0f0e_0d0c_0b0a_0908,
            0x0706_0504_0302_0100,
        ],
        [9, 0, 0, 0],
    ];
    for (i, x) in limbs.iter().enumerate() {
        let (mut w, mut n) = ([0; 4], [0; 4]);
        let rw = super::bignum_invsqrt_p25519::bignum_invsqrt_p25519(&mut w, x);
        let rn = super::bignum_invsqrt_p25519_narrow::bignum_invsqrt_p25519(&mut n, x);
        assert_eq!((rw, w), (rn, n), "invsqrt {i}");
        super::bignum_sqr_p25519::bignum_sqr_p25519(&mut w, x);
        super::bignum_sqr_p25519_narrow::bignum_sqr_p25519(&mut n, x);
        assert_eq!(w, n, "sqr {i}");
        for (j, y) in limbs.iter().enumerate() {
            super::bignum_mul_p25519::bignum_mul_p25519(&mut w, x, y);
            super::bignum_mul_p25519_narrow::bignum_mul_p25519(&mut n, x, y);
            assert_eq!(w, n, "mul {i},{j}");
            let carry = &limbs[j % limbs.len()];
            super::bignum_madd_n25519::bignum_madd_n25519(&mut w, x, y, carry);
            super::bignum_madd_n25519_narrow::bignum_madd_n25519(&mut n, x, y, carry);
            assert_eq!(w, n, "madd {i},{j}");
            super::curve25519_x25519::curve25519_x25519(&mut w, x, y);
            super::curve25519_x25519_narrow::curve25519_x25519(&mut n, x, y);
            assert_eq!(w, n, "x25519 {i},{j}");
        }
        let (mut w, mut n) = ([0; 4], [0; 4]);
        super::curve25519_x25519base::curve25519_x25519base(&mut w, x);
        super::curve25519_x25519base_narrow::curve25519_x25519base(&mut n, x);
        assert_eq!(w, n, "x25519base {i}");

        let (mut w, mut n) = ([0; 8], [0; 8]);
        super::edwards25519_scalarmulbase::edwards25519_scalarmulbase(&mut w, x);
        super::edwards25519_scalarmulbase_narrow::edwards25519_scalarmulbase(&mut n, x);
        assert_eq!(w, n, "ed25519 base {i}");
        let point = w;
        let (mut w, mut n) = ([0; 8], [0; 8]);
        super::edwards25519_scalarmuldouble::edwards25519_scalarmuldouble(
            &mut w, x, &point, &limbs[1],
        );
        super::edwards25519_scalarmuldouble_narrow::edwards25519_scalarmuldouble(
            &mut n, x, &point, &limbs[1],
        );
        assert_eq!(w, n, "ed25519 double {i}");
    }

    for (i, bytes) in [[0u8; 32], [0xff; 32], {
        let mut b = [0u8; 32];
        b[0] = 0x58;
        b[31] = 0x66;
        b
    }]
    .iter()
    .enumerate()
    {
        let (mut w, mut n) = ([0; 8], [0; 8]);
        let rw = super::edwards25519_decode::edwards25519_decode(&mut w, bytes);
        let rn = super::edwards25519_decode_narrow::edwards25519_decode(&mut n, bytes);
        assert_eq!((rw, w), (rn, n), "decode {i}");
    }

    // Extended points, including the zero point and a point copied out of
    // the base multiplication above.
    let mut extended = [[0u64; 16]; 2];
    extended[1][..4].copy_from_slice(&limbs[3]);
    let mut projective = [[0u64; 12]; 2];
    projective[1][..4].copy_from_slice(&limbs[3]);
    projective[1][8] = 1;
    for (i, p1) in extended.iter().enumerate() {
        for p2 in &extended {
            let (mut w, mut n) = ([0; 16], [0; 16]);
            super::edwards25519_epadd::edwards25519_epadd(&mut w, p1, p2);
            super::edwards25519_epadd_narrow::edwards25519_epadd(&mut n, p1, p2);
            assert_eq!(w, n, "epadd {i}");
        }
    }
    for (i, p) in projective.iter().enumerate() {
        let (mut w, mut n) = ([0; 16], [0; 16]);
        super::edwards25519_epdouble::edwards25519_epdouble(&mut w, p);
        super::edwards25519_epdouble_narrow::edwards25519_epdouble(&mut n, p);
        assert_eq!(w, n, "epdouble {i}");
        let (mut w, mut n) = ([0; 12], [0; 12]);
        super::edwards25519_pdouble::edwards25519_pdouble(&mut w, p);
        super::edwards25519_pdouble_narrow::edwards25519_pdouble(&mut n, p);
        assert_eq!(w, n, "pdouble {i}");
    }

    // P-256's generator, affine little-endian limbs, as `p256_scalarmul` takes it.
    let g_affine = [
        0xf4a1_3945_d898_c296,
        0x7703_7d81_2deb_33a0,
        0xf8bc_e6e5_63a4_40f2,
        0x6b17_d1f2_e12c_4247,
        0xcbb6_4068_37bf_51f5,
        0x2bce_3357_6b31_5ece,
        0x8ee7_eb4a_7c0f_9e16,
        0x4fe3_42e2_fe1a_7f9b,
    ];
    // G in Montgomery Jacobian, z = 1.
    let g256 = [
        0x79e7_30d4_18a9_143c,
        0x75ba_95fc_5fed_b601,
        0x79fb_732b_7762_2510,
        0x1890_5f76_a537_55c6,
        0xddf2_5357_ce95_560a,
        0x8b4a_b8e4_ba19_e45c,
        0xd2e8_8688_dd21_f325,
        0x8571_ff18_2588_5d85,
        0x0000_0000_0000_0001,
        0xffff_ffff_0000_0000,
        0xffff_ffff_ffff_ffff,
        0x0000_0000_ffff_fffe,
    ];
    let g384 = [
        0x3dd0_7566_49c0_b528,
        0x20e3_78e2_a0d6_ce38,
        0x879c_3afc_541b_4d6e,
        0x6454_8684_59a3_0eff,
        0x812f_f723_614e_de2b,
        0x4d3a_adc2_299e_1513,
        0x2304_3dad_4b03_a4fe,
        0xa1bf_a8bf_7bb4_a9ac,
        0x8bad_e756_2e83_b050,
        0xc6c3_5219_68f4_ffd9,
        0xdd80_0226_3969_a840,
        0x2b78_abc2_5a15_c5e9,
        0xffff_ffff_0000_0001,
        0x0000_0000_ffff_ffff,
        0x0000_0000_0000_0001,
        0,
        0,
        0,
    ];
    let g521 = [
        0xf97e_7e31_c2e5_bd66,
        0x3348_b3c1_856a_429b,
        0xfe1d_c127_a2ff_a8de,
        0xa14b_5e77_efe7_5928,
        0xf828_af60_6b4d_3dba,
        0x9c64_8139_053f_b521,
        0x9e3e_cb66_2395_b442,
        0x858e_06b7_0404_e9cd,
        0x0000_0000_0000_00c6,
        0x88be_9476_9fd1_6650,
        0x353c_7086_a272_c240,
        0xc550_b901_3fad_0761,
        0x97ee_7299_5ef4_2640,
        0x17af_bd17_273e_662c,
        0x98f5_4449_579b_4468,
        0x5c8a_5fb4_2c7d_1bd9,
        0x3929_6a78_9a3b_c004,
        0x0000_0000_0000_0118,
        1,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];

    for (i, scalar) in limbs.iter().enumerate() {
        let (mut w, mut n) = ([0; 8], [0; 8]);
        super::p256_scalarmul::p256_scalarmul(&mut w, scalar, &g_affine);
        super::p256_scalarmul_narrow::p256_scalarmul(&mut n, scalar, &g_affine);
        assert_eq!(w, n, "p256 scalarmul {i}");
    }
    let (mut wide, mut narrow) = ([0; 12], [0; 12]);
    let affine = g256[..8].try_into().unwrap();
    super::p256_montjmixadd::p256_montjmixadd(&mut wide, &g256, &affine);
    super::p256_montjmixadd_narrow::p256_montjmixadd(&mut narrow, &g256, &affine);
    assert_eq!(wide, narrow, "p256 mixadd");
    let mut zero_jac = [0; 12];
    zero_jac[8] = 1;
    super::p256_montjmixadd::p256_montjmixadd(&mut wide, &zero_jac, &affine);
    super::p256_montjmixadd_narrow::p256_montjmixadd(&mut narrow, &zero_jac, &affine);
    assert_eq!(wide, narrow, "p256 mixadd z");

    // A zero table and one with a single nonzero window. `vec` keeps the
    // 43 blocks off this frame.
    let mut tables: Vec<Box<[[u64; 256]; 43]>> = Vec::new();
    let zero_rows: Vec<[u64; 256]> = vec![[0; 256]; 43];
    tables.push(zero_rows.try_into().unwrap());
    let mut rows: Vec<[u64; 256]> = vec![[0; 256]; 43];
    rows[1][..8].copy_from_slice(&g_affine);
    tables.push(rows.try_into().unwrap());
    for (i, table) in tables.iter().enumerate() {
        for (j, scalar) in limbs.iter().enumerate().take(3) {
            let (mut w, mut n) = ([0; 8], [0; 8]);
            super::p256_scalarmulbase::p256_scalarmulbase(&mut w, scalar, table);
            super::p256_scalarmulbase_narrow::p256_scalarmulbase(&mut n, scalar, table);
            assert_eq!(w, n, "p256 base {i},{j}");
        }
    }

    let scalars6 = [
        [0; 6],
        [1, 0, 0, 0, 0, 0],
        [u64::MAX; 6],
        [limbs[3][0], limbs[3][1], limbs[3][2], limbs[3][3], 0, 0],
    ];
    for (i, scalar) in scalars6.iter().enumerate() {
        let (mut w, mut n) = ([0; 18], [0; 18]);
        super::p384_montjscalarmul::p384_montjscalarmul(&mut w, scalar, &g384);
        super::p384_montjscalarmul_narrow::p384_montjscalarmul(&mut n, scalar, &g384);
        assert_eq!(w, n, "p384 scalarmul {i}");
    }
    let affine384: [u64; 12] = g384[..12].try_into().unwrap();
    let (mut w, mut n) = ([0; 18], [0; 18]);
    super::p384_montjmixadd::p384_montjmixadd(&mut w, &g384, &affine384);
    super::p384_montjmixadd_narrow::p384_montjmixadd(&mut n, &g384, &affine384);
    assert_eq!(w, n, "p384 mixadd");

    let (mut doubled_w, mut doubled_n) = ([0; 27], [0; 27]);
    super::p521_jdouble::p521_jdouble(&mut doubled_w, &g521);
    super::p521_jdouble_narrow::p521_jdouble(&mut doubled_n, &g521);
    assert_eq!(doubled_w, doubled_n, "p521 double");
    let mut zero521 = [0; 27];
    zero521[18] = 1;
    super::p521_jdouble::p521_jdouble(&mut doubled_w, &zero521);
    super::p521_jdouble_narrow::p521_jdouble(&mut doubled_n, &zero521);
    assert_eq!(doubled_w, doubled_n, "p521 double z");
    let (mut w, mut n) = ([0; 27], [0; 27]);
    super::p521_jadd::p521_jadd(&mut w, &g521, &doubled_n);
    super::p521_jadd_narrow::p521_jadd(&mut n, &g521, &doubled_n);
    assert_eq!(w, n, "p521 add");
    let affine521: [u64; 18] = g521[..18].try_into().unwrap();
    super::p521_jmixadd::p521_jmixadd(&mut w, &g521, &affine521);
    super::p521_jmixadd_narrow::p521_jmixadd(&mut n, &g521, &affine521);
    assert_eq!(w, n, "p521 mixadd");
    let scalars9 = [
        [0; 9],
        [1, 0, 0, 0, 0, 0, 0, 0, 0],
        {
            let mut s = [0; 9];
            s[..4].copy_from_slice(&limbs[3]);
            s
        },
        [u64::MAX; 9],
    ];
    for (i, scalar) in scalars9.iter().enumerate() {
        let (mut w, mut n) = ([0; 27], [0; 27]);
        super::p521_jscalarmul::p521_jscalarmul(&mut w, scalar, &g521);
        super::p521_jscalarmul_narrow::p521_jscalarmul(&mut n, scalar, &g521);
        assert_eq!(w, n, "p521 scalarmul {i}");
    }

    // p = 2^255 - 19, then p - 1 and p + k. These are the reduction edges.
    let p25519 = [
        0xffff_ffff_ffff_ffed,
        u64::MAX,
        u64::MAX,
        0x7fff_ffff_ffff_ffff,
    ];
    let mut p25519_minus = p25519;
    p25519_minus[0] -= 1;
    let mut p25519_plus = p25519;
    p25519_plus[0] += 2;
    // 2^255, which is p + 19 and sets only the sign bit of a 32-byte encoding.
    let two_255 = [0, 0, 0, 0x8000_0000_0000_0000];
    for (i, x) in [p25519_minus, p25519, p25519_plus, two_255]
        .iter()
        .enumerate()
    {
        let (mut w, mut n) = ([0; 4], [0; 4]);
        let rw = super::bignum_invsqrt_p25519::bignum_invsqrt_p25519(&mut w, x);
        let rn = super::bignum_invsqrt_p25519_narrow::bignum_invsqrt_p25519(&mut n, x);
        assert_eq!((rw, w), (rn, n), "invsqrt edge {i}");
        super::bignum_sqr_p25519::bignum_sqr_p25519(&mut w, x);
        super::bignum_sqr_p25519_narrow::bignum_sqr_p25519(&mut n, x);
        assert_eq!(w, n, "sqr edge {i}");
        super::bignum_mul_p25519::bignum_mul_p25519(&mut w, x, &p25519);
        super::bignum_mul_p25519_narrow::bignum_mul_p25519(&mut n, x, &p25519);
        assert_eq!(w, n, "mul edge {i}");
        super::curve25519_x25519::curve25519_x25519(&mut w, x, &p25519_minus);
        super::curve25519_x25519_narrow::curve25519_x25519(&mut n, x, &p25519_minus);
        assert_eq!(w, n, "x25519 edge {i}");
        super::curve25519_x25519base::curve25519_x25519base(&mut w, x);
        super::curve25519_x25519base_narrow::curve25519_x25519base(&mut n, x);
        assert_eq!(w, n, "x25519base edge {i}");
    }

    // Ed25519's group order L, then L - 1 and L + 1.
    let order25519 = [
        0x5812_631a_5cf5_d3ed,
        0x14de_f9de_a2f7_9cd6,
        0,
        0x1000_0000_0000_0000,
    ];
    let mut below25519 = order25519;
    below25519[0] -= 1;
    let mut above25519 = order25519;
    above25519[0] += 1;
    for (i, scalar) in [below25519, order25519, above25519].iter().enumerate() {
        let (mut w, mut n) = ([0; 8], [0; 8]);
        super::edwards25519_scalarmulbase::edwards25519_scalarmulbase(&mut w, scalar);
        super::edwards25519_scalarmulbase_narrow::edwards25519_scalarmulbase(&mut n, scalar);
        assert_eq!(w, n, "ed25519 order {i}");
    }

    // Decode at p - 1, p, p + 1, and with the sign bit set on each.
    let mut decode_edges = Vec::new();
    for mut limbs in [p25519_minus, p25519, p25519_plus] {
        decode_edges.push(limbs_to_bytes(limbs));
        limbs[3] |= 0x8000_0000_0000_0000;
        decode_edges.push(limbs_to_bytes(limbs));
    }
    for (i, bytes) in decode_edges.iter().enumerate() {
        let (mut w, mut n) = ([0; 8], [0; 8]);
        let rw = super::edwards25519_decode::edwards25519_decode(&mut w, bytes);
        let rn = super::edwards25519_decode_narrow::edwards25519_decode(&mut n, bytes);
        assert_eq!((rw, w), (rn, n), "decode edge {i}");
    }

    // n, n - 1, and n + 1 for each NIST scalar. u64::MAX is above the order
    // and is already in the loops above; these are the boundary.
    let n256 = [
        0xf3b9_cac2_fc63_2551,
        0xbce6_faad_a717_9e84,
        u64::MAX,
        0xffff_ffff_0000_0000,
    ];
    let mut below256 = n256;
    below256[0] -= 1;
    let mut above256 = n256;
    above256[0] += 1;
    for (i, scalar) in [below256, n256, above256].iter().enumerate() {
        let (mut w, mut n) = ([0; 8], [0; 8]);
        super::p256_scalarmul::p256_scalarmul(&mut w, scalar, &g_affine);
        super::p256_scalarmul_narrow::p256_scalarmul(&mut n, scalar, &g_affine);
        assert_eq!(w, n, "p256 order {i}");
    }

    let n384 = [
        0xecec_196a_ccc5_2973,
        0x581a_0db2_48b0_a77a,
        0xc763_4d81_f437_2ddf,
        u64::MAX,
        u64::MAX,
        u64::MAX,
    ];
    let mut below384 = n384;
    below384[0] -= 1;
    let mut above384 = n384;
    above384[0] += 1;
    for (i, scalar) in [below384, n384, above384].iter().enumerate() {
        let (mut w, mut n) = ([0; 18], [0; 18]);
        super::p384_montjscalarmul::p384_montjscalarmul(&mut w, scalar, &g384);
        super::p384_montjscalarmul_narrow::p384_montjscalarmul(&mut n, scalar, &g384);
        assert_eq!(w, n, "p384 order {i}");
    }

    let n521 = [
        0xbb6f_b71e_9138_6409,
        0x3bb5_c9b8_899c_47ae,
        0x7fcc_0148_f709_a5d0,
        0x5186_8783_bf2f_966b,
        0xffff_ffff_ffff_fffa,
        u64::MAX,
        u64::MAX,
        u64::MAX,
        0x0000_0000_0000_01ff,
    ];
    let mut below521 = n521;
    below521[0] -= 1;
    let mut above521 = n521;
    above521[0] += 1;
    for (i, scalar) in [below521, n521, above521].iter().enumerate() {
        let (mut w, mut n) = ([0; 27], [0; 27]);
        super::p521_jscalarmul::p521_jscalarmul(&mut w, scalar, &g521);
        super::p521_jscalarmul_narrow::p521_jscalarmul(&mut n, scalar, &g521);
        assert_eq!(w, n, "p521 order {i}");
    }

    // Point at infinity (Z = 0) and an unreduced affine X, for the mixed adds.
    let mut inf384 = g384;
    inf384[12..].fill(0);
    let mut unreduced384 = affine384;
    unreduced384[..6].fill(u64::MAX);
    for (i, (point, affine)) in [(inf384, affine384), (g384, unreduced384)]
        .iter()
        .enumerate()
    {
        let (mut w, mut n) = ([0; 18], [0; 18]);
        super::p384_montjmixadd::p384_montjmixadd(&mut w, point, affine);
        super::p384_montjmixadd_narrow::p384_montjmixadd(&mut n, point, affine);
        assert_eq!(w, n, "p384 mixadd edge {i}");
    }
    let mut inf521 = g521;
    inf521[18..].fill(0);
    let mut unreduced521 = affine521;
    unreduced521[..9].fill(u64::MAX);
    for (i, (point, affine)) in [(inf521, affine521), (g521, unreduced521)]
        .iter()
        .enumerate()
    {
        let (mut w, mut n) = ([0; 27], [0; 27]);
        super::p521_jmixadd::p521_jmixadd(&mut w, point, affine);
        super::p521_jmixadd_narrow::p521_jmixadd(&mut n, point, affine);
        assert_eq!(w, n, "p521 mixadd edge {i}");
    }

    matches_portable(&g_affine, &g256, &g384, &g521);
    random(&g_affine, &g256, &g384, &g521);
}

/// Seeded inputs per routine in [`random`] and in `mont`'s Karatsuba test.
pub(super) const RANDOM_CASES: usize = 256;

/// splitmix64, so a failure reproduces from its seed.
pub(super) struct Rng(pub(super) u64);

impl Rng {
    pub(super) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub(super) fn words<const N: usize>(&mut self) -> [u64; N] {
        core::array::from_fn(|_| self.next())
    }
}

/// Both schedules on [`RANDOM_CASES`] seeded inputs each, and against the
/// oracles `matches_portable` uses: the schoolbook reduction for the field
/// products and multiply-add, the generic backend for the NIST point
/// operations, and, on the first `DALEK_CASES`, curve25519-dalek for X25519
/// and Ed25519, and on the first `EULER_CASES` Euler's criterion for the
/// inverse square root. The points are multiples of each generator by
/// random full-width scalars. P-256's base multiplication, whose table
/// `p256_base` builds, stays on the fixed scalars.
fn random(g_affine: &[u64; 8], g256: &[u64; 12], g384: &[u64; 18], g521: &[u64; 27]) {
    use curve25519_dalek::edwards::EdwardsPoint;
    use curve25519_dalek::montgomery::MontgomeryPoint;
    use curve25519_dalek::scalar::Scalar;

    use crate::low::generic::limb64::{p256, p384, p521};

    // dalek and the schoolbook exponentiation run unoptimised in the test
    // build, and slower still in qemu.
    const DALEK_CASES: usize = 16;
    const EULER_CASES: usize = 4;
    let p = [
        0xffff_ffff_ffff_ffed,
        u64::MAX,
        u64::MAX,
        0x7fff_ffff_ffff_ffff,
    ];
    let n = [
        0x5812_631a_5cf5_d3ed,
        0x14de_f9de_a2f7_9cd6,
        0,
        0x1000_0000_0000_0000,
    ];
    let mont256 = |x: &[u64]| {
        let mut out = [0; 4];
        p256::bignum_tomont_p256(&mut out, &limbs_at(x));
        out
    };
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let mut invsqrt_samples = Vec::new();
    // The previous case's points, so each addition has two random operands.
    let mut prev256 = *g_affine;
    let mut prev384 = *g384;
    let mut prev521 = *g521;
    for i in 0..RANDOM_CASES {
        let [x, y, c]: [[u64; 4]; 3] = core::array::from_fn(|_| rng.words());
        let dalek = i < DALEK_CASES;

        let (mut w, mut nr) = ([0; 4], [0; 4]);
        super::bignum_mul_p25519::bignum_mul_p25519(&mut w, &x, &y);
        super::bignum_mul_p25519_narrow::bignum_mul_p25519(&mut nr, &x, &y);
        assert_eq!(w, nr, "random mul {i}");
        assert_eq!(nr, reduce(&mul256(x, y), &p), "random portable mul {i}");
        super::bignum_sqr_p25519::bignum_sqr_p25519(&mut w, &x);
        super::bignum_sqr_p25519_narrow::bignum_sqr_p25519(&mut nr, &x);
        assert_eq!(w, nr, "random sqr {i}");
        assert_eq!(nr, reduce(&mul256(x, x), &p), "random portable sqr {i}");
        super::bignum_madd_n25519::bignum_madd_n25519(&mut w, &x, &y, &c);
        super::bignum_madd_n25519_narrow::bignum_madd_n25519(&mut nr, &x, &y, &c);
        assert_eq!(w, nr, "random madd {i}");
        assert_eq!(nr, madd_n(x, y, c, n), "random portable madd {i}");
        let rw = super::bignum_invsqrt_p25519::bignum_invsqrt_p25519(&mut w, &x);
        let rn = super::bignum_invsqrt_p25519_narrow::bignum_invsqrt_p25519(&mut nr, &x);
        assert_eq!((rw, w), (rn, nr), "random invsqrt {i}");
        if i < EULER_CASES {
            invsqrt_samples.push(x);
        }

        super::curve25519_x25519::curve25519_x25519(&mut w, &x, &y);
        super::curve25519_x25519_narrow::curve25519_x25519(&mut nr, &x, &y);
        assert_eq!(w, nr, "random x25519 {i}");
        if dalek {
            let want = MontgomeryPoint(words_to_bytes(&y))
                .mul_clamped(words_to_bytes(&x))
                .0;
            assert_eq!(words_to_bytes(&nr), want, "random dalek x25519 {i}");
        }
        super::curve25519_x25519base::curve25519_x25519base(&mut w, &x);
        super::curve25519_x25519base_narrow::curve25519_x25519base(&mut nr, &x);
        assert_eq!(w, nr, "random x25519base {i}");
        if dalek {
            let want = MontgomeryPoint::mul_base_clamped(words_to_bytes(&x)).0;
            assert_eq!(words_to_bytes(&nr), want, "random dalek x25519base {i}");
        }

        let (mut w, mut nr) = ([0; 8], [0; 8]);
        super::edwards25519_scalarmulbase::edwards25519_scalarmulbase(&mut w, &x);
        super::edwards25519_scalarmulbase_narrow::edwards25519_scalarmulbase(&mut nr, &x);
        assert_eq!(w, nr, "random ed25519 base {i}");
        if dalek {
            let want = EdwardsPoint::mul_base(&Scalar::from_bytes_mod_order(words_to_bytes(&x)))
                .compress()
                .0;
            assert_eq!(compress_edwards(&nr), want, "random dalek ed25519 base {i}");
        }
        let point = nr;
        super::edwards25519_scalarmuldouble::edwards25519_scalarmuldouble(&mut w, &y, &point, &c);
        super::edwards25519_scalarmuldouble_narrow::edwards25519_scalarmuldouble(
            &mut nr, &y, &point, &c,
        );
        assert_eq!(w, nr, "random ed25519 double {i}");
        // A valid encoding, and 32 random bytes, which mostly are not.
        for (j, bytes) in [compress_edwards(&point), words_to_bytes(&c)]
            .iter()
            .enumerate()
        {
            let (mut w, mut nr) = ([0; 8], [0; 8]);
            let rw = super::edwards25519_decode::edwards25519_decode(&mut w, bytes);
            let rn = super::edwards25519_decode_narrow::edwards25519_decode(&mut nr, bytes);
            assert_eq!((rw, w), (rn, nr), "random decode {i},{j}");
        }
        // `point` and `nr` (y·B) in extended (x, y, 1, xy) and projective
        // (x, y, 1) coordinates.
        let extended = |affine: &[u64; 8]| {
            let mut out = [0; 16];
            out[..8].copy_from_slice(affine);
            out[8] = 1;
            let mut t = [0; 4];
            let (xy, _) = affine.as_chunks::<4>();
            super::bignum_mul_p25519::bignum_mul_p25519(&mut t, &xy[0], &xy[1]);
            out[12..].copy_from_slice(&t);
            out
        };
        super::edwards25519_scalarmulbase::edwards25519_scalarmulbase(&mut nr, &y);
        let (p1, p2) = (extended(&point), extended(&nr));
        let (mut w16, mut n16) = ([0; 16], [0; 16]);
        super::edwards25519_epadd::edwards25519_epadd(&mut w16, &p1, &p2);
        super::edwards25519_epadd_narrow::edwards25519_epadd(&mut n16, &p1, &p2);
        assert_eq!(w16, n16, "random epadd {i}");
        let projective: [u64; 12] = p1[..12].try_into().unwrap();
        super::edwards25519_epdouble::edwards25519_epdouble(&mut w16, &projective);
        super::edwards25519_epdouble_narrow::edwards25519_epdouble(&mut n16, &projective);
        assert_eq!(w16, n16, "random epdouble {i}");
        let (mut w12, mut n12) = ([0; 12], [0; 12]);
        super::edwards25519_pdouble::edwards25519_pdouble(&mut w12, &projective);
        super::edwards25519_pdouble_narrow::edwards25519_pdouble(&mut n12, &projective);
        assert_eq!(w12, n12, "random pdouble {i}");

        // P-256: k·G, then k·G in Montgomery Jacobian (z = 1) plus the
        // previous case's point in Montgomery affine.
        let (mut w8, mut n8) = ([0; 8], [0; 8]);
        super::p256_scalarmul::p256_scalarmul(&mut w8, &x, g_affine);
        super::p256_scalarmul_narrow::p256_scalarmul(&mut n8, &x, g_affine);
        assert_eq!(w8, n8, "random p256 scalarmul {i}");
        let mut jacobian = [0; 12];
        jacobian[..4].copy_from_slice(&mont256(&n8[..4]));
        jacobian[4..8].copy_from_slice(&mont256(&n8[4..]));
        jacobian[8..].copy_from_slice(&g256[8..]);
        let mut affine = [0; 8];
        affine[..4].copy_from_slice(&mont256(&prev256[..4]));
        affine[4..].copy_from_slice(&mont256(&prev256[4..]));
        prev256 = n8;
        let (mut w12, mut n12, mut g12) = ([0; 12], [0; 12], [0; 12]);
        super::p256_montjmixadd::p256_montjmixadd(&mut w12, &jacobian, &affine);
        super::p256_montjmixadd_narrow::p256_montjmixadd(&mut n12, &jacobian, &affine);
        p256::p256_montjmixadd(&mut g12, &jacobian, &affine);
        assert_eq!((w12, n12), (g12, g12), "random p256 mixadd {i}");

        let k6: [u64; 6] = rng.words();
        let (mut w18, mut n18) = ([0; 18], [0; 18]);
        super::p384_montjscalarmul::p384_montjscalarmul(&mut w18, &k6, g384);
        super::p384_montjscalarmul_narrow::p384_montjscalarmul(&mut n18, &k6, g384);
        assert_eq!(w18, n18, "random p384 scalarmul {i}");
        let (px, py) = p384_affine(&prev384).expect("a random multiple is finite");
        let mut affine384 = [0; 12];
        affine384[..6].copy_from_slice(&px);
        affine384[6..].copy_from_slice(&py);
        let jacobian384 = n18;
        prev384 = n18;
        let mut g18 = [0; 18];
        super::p384_montjmixadd::p384_montjmixadd(&mut w18, &jacobian384, &affine384);
        super::p384_montjmixadd_narrow::p384_montjmixadd(&mut n18, &jacobian384, &affine384);
        p384::p384_montjmixadd(&mut g18, &jacobian384, &affine384);
        assert_eq!((w18, n18), (g18, g18), "random p384 mixadd {i}");

        let k9: [u64; 9] = rng.words();
        let (mut w27, mut n27, mut g27) = ([0; 27], [0; 27], [0; 27]);
        super::p521_jscalarmul::p521_jscalarmul(&mut w27, &k9, g521);
        super::p521_jscalarmul_narrow::p521_jscalarmul(&mut n27, &k9, g521);
        assert_eq!(w27, n27, "random p521 scalarmul {i}");
        let point521 = n27;
        super::p521_jdouble::p521_jdouble(&mut w27, &point521);
        super::p521_jdouble_narrow::p521_jdouble(&mut n27, &point521);
        p521::p521_jdouble(&mut g27, &point521);
        assert_eq!((w27, n27), (g27, g27), "random p521 double {i}");
        super::p521_jadd::p521_jadd(&mut w27, &point521, &prev521);
        super::p521_jadd_narrow::p521_jadd(&mut n27, &point521, &prev521);
        p521::p521_jadd(&mut g27, &point521, &prev521);
        assert_eq!((w27, n27), (g27, g27), "random p521 add {i}");
        let (px, py) = p521_affine(&prev521).expect("a random multiple is finite");
        let mut affine521 = [0; 18];
        affine521[..9].copy_from_slice(&px);
        affine521[9..].copy_from_slice(&py);
        super::p521_jmixadd::p521_jmixadd(&mut w27, &point521, &affine521);
        super::p521_jmixadd_narrow::p521_jmixadd(&mut n27, &point521, &affine521);
        p521::p521_jmixadd(&mut g27, &point521, &affine521);
        assert_eq!((w27, n27), (g27, g27), "random p521 mixadd {i}");
        prev521 = point521;
    }
    invsqrt_oracle(&p, &invsqrt_samples);
}

/// Narrow schedules against oracles other than the wide schedule.
///
/// Field products and `n_25519` multiply-add are reduced by a binary
/// schoolbook, whose `(p - 1)^2 = 1` and `n * 1 = 0` checks run first.
/// X25519, including a zero u-coordinate, `u = p`, and the low-order
/// points, and Ed25519 base multiplication, decoding, and double-scalar
/// multiplication are curve25519-dalek, as is the RFC 7748 base-point
/// vector. `bignum_invsqrt_p25519` is checked against Euler's criterion.
/// P-256 scalar multiplication is checked at `0`, `1`, `n - 1`, `n`, and
/// `n + 1`. Base multiplication uses the signing table and the generic
/// backend, at `0`, `1`, `n - 1`, `n`, and a full-width scalar. P-256 and
/// P-384 mixed addition, including `P = Q` and `P = -Q`, use the generic
/// backend. P-384 has no variable-base scalar multiplication there, so its
/// order edges are checked against the affine generator. P-521 doubling,
/// `P + P`, `P + (-P)`, mixed addition of distinct points, and the sum of
/// two points at infinity use the generic backend. One point at infinity
/// is the other point, with `z = 1` for mixed addition: the assembly
/// selects it, and the generic formula does not. P-521 scalar multiplication is
/// compared to `p521_jscalarmul` as affine points, because that routine
/// matches s2n-bignum in the point rather than its words, and checked at
/// the same order edges.
fn matches_portable(g_affine: &[u64; 8], g256: &[u64; 12], g384: &[u64; 18], g521: &[u64; 27]) {
    use curve25519_dalek::edwards::EdwardsPoint;
    use curve25519_dalek::montgomery::MontgomeryPoint;
    use curve25519_dalek::scalar::Scalar;

    let p = [
        0xffff_ffff_ffff_ffed,
        u64::MAX,
        u64::MAX,
        0x7fff_ffff_ffff_ffff,
    ];
    let extra: u128 = 27_742_317_777_372_353_535_851_937_790_883_648_493;
    let n25519 = [extra as u64, (extra >> 64) as u64, 0, 1u64 << 60];
    assert_eq!(
        n25519,
        [
            0x5812_631a_5cf5_d3ed,
            0x14de_f9de_a2f7_9cd6,
            0,
            0x1000_0000_0000_0000,
        ]
    );
    let one = [1, 0, 0, 0];
    let mut pm1 = p;
    sub_into(&mut pm1, &one);
    let mut nm1 = n25519;
    sub_into(&mut nm1, &one);
    assert_eq!(reduce(&mul256(pm1, pm1), &p), one, "oracle (p-1)^2");
    assert_eq!(reduce(&mul256(p, one), &p), [0; 4], "oracle p");
    assert_eq!(
        reduce(&mul256([2, 0, 0, 0], [2, 0, 0, 0]), &p),
        [4, 0, 0, 0],
        "oracle 4"
    );
    assert_eq!(madd_n(n25519, one, [0; 4], n25519), [0; 4], "oracle n");
    assert_eq!(madd_n(nm1, nm1, [0; 4], n25519), one, "oracle (n-1)^2");

    let two255 = [u64::MAX, u64::MAX, u64::MAX, 0x7fff_ffff_ffff_ffff];
    let field = [
        [0; 4],
        one,
        pm1,
        p,
        succ(p),
        two255,
        [u64::MAX; 4],
        [
            0x0123_4567_89ab_cdef,
            0xfedc_ba98_7654_3210,
            0x0f0e_0d0c_0b0a_0908,
            0x0706_0504_0302_0100,
        ],
    ];
    for (i, x) in field.iter().enumerate() {
        let mut got = [0; 4];
        super::bignum_sqr_p25519_narrow::bignum_sqr_p25519(&mut got, x);
        assert_eq!(got, reduce(&mul256(*x, *x), &p), "portable sqr {i}");
        for (j, y) in field.iter().enumerate() {
            super::bignum_mul_p25519_narrow::bignum_mul_p25519(&mut got, x, y);
            assert_eq!(got, reduce(&mul256(*x, *y), &p), "portable mul {i},{j}");
            let carry = field[(i + j) % field.len()];
            super::bignum_madd_n25519_narrow::bignum_madd_n25519(&mut got, x, y, &carry);
            assert_eq!(got, madd_n(*x, *y, carry, n25519), "portable madd {i},{j}");
        }
    }

    let alice = hex32("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a");
    let alice_public = hex32("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a");
    let mut base = [0; 4];
    super::curve25519_x25519base_narrow::curve25519_x25519base(&mut base, &bytes_to_words(&alice));
    assert_eq!(words_to_bytes(&base), alice_public, "rfc7748 base");
    assert_eq!(
        MontgomeryPoint::mul_base_clamped(alice).0,
        alice_public,
        "dalek rfc7748"
    );

    let alice_words = bytes_to_words(&alice);
    // Wycheproof's low-order u-coordinates, and the same values with the
    // high bit set, which X25519 ignores.
    let torsion_a = bytes_to_words(&hex32(
        "e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800",
    ));
    let torsion_b = bytes_to_words(&hex32(
        "5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157",
    ));
    let mut torsion_a_hi = torsion_a;
    torsion_a_hi[3] |= 1 << 63;
    let mut torsion_b_hi = torsion_b;
    torsion_b_hi[3] |= 1 << 63;
    let points = [
        [0; 4],
        one,
        [9, 0, 0, 0],
        pm1,
        p,
        succ(p),
        [0, 0, 0, 1 << 63],
        [9, 0, 0, 1 << 63],
        torsion_a,
        torsion_b,
        torsion_a_hi,
        torsion_b_hi,
        [u64::MAX; 4],
        alice_words,
    ];
    for (i, scalar) in [one, [u64::MAX; 4], alice_words].iter().enumerate() {
        let mut got = [0; 4];
        super::curve25519_x25519base_narrow::curve25519_x25519base(&mut got, scalar);
        let want = MontgomeryPoint::mul_base_clamped(words_to_bytes(scalar)).0;
        assert_eq!(words_to_bytes(&got), want, "portable x25519 base {i}");
        for (j, point) in points.iter().enumerate() {
            super::curve25519_x25519_narrow::curve25519_x25519(&mut got, scalar, point);
            let want = MontgomeryPoint(words_to_bytes(point))
                .mul_clamped(words_to_bytes(scalar))
                .0;
            assert_eq!(words_to_bytes(&got), want, "portable x25519 {i},{j}");
        }
    }

    let identity = {
        let mut bytes = [0u8; 32];
        bytes[0] = 1;
        bytes
    };
    let base_ed = hex32("5866666666666666666666666666666666666666666666666666666666666666");
    for (label, scalar, expect) in [("0", [0; 4], identity), ("1", one, base_ed)] {
        let mut point = [0; 8];
        super::edwards25519_scalarmulbase_narrow::edwards25519_scalarmulbase(&mut point, &scalar);
        assert_eq!(compress_edwards(&point), expect, "ed25519 {label}");
        let want = EdwardsPoint::mul_base(&Scalar::from_bytes_mod_order(words_to_bytes(&scalar)))
            .compress()
            .0;
        assert_eq!(compress_edwards(&point), want, "portable ed25519 {label}");
    }
    for (i, scalar) in [[u64::MAX; 4], alice_words, nm1, n25519, succ(n25519)]
        .iter()
        .enumerate()
    {
        let mut point = [0; 8];
        super::edwards25519_scalarmulbase_narrow::edwards25519_scalarmulbase(&mut point, scalar);
        let want = EdwardsPoint::mul_base(&Scalar::from_bytes_mod_order(words_to_bytes(scalar)))
            .compress()
            .0;
        assert_eq!(compress_edwards(&point), want, "portable ed25519 {i}");
    }

    ed25519_decode();
    ed25519_double(&[[0; 4], one, nm1, alice_words]);
    let mut invsqrt_in = field.to_vec();
    invsqrt_in.push([2, 0, 0, 0]);
    invsqrt_oracle(&p, &invsqrt_in);
    p256_base(g256, g_affine);
    p256_edges(g_affine);
    mixadd_p256(g256);
    mixadd_p384(g384);
    p384_order(g384);
    p521_points(g521);
    p521_order(g521);
}

fn p256_edges(g_affine: &[u64; 8]) {
    use crate::low::generic::limb64::p256;

    let n = p256::N;
    let expect_neg = neg_p256(g_affine);
    for (label, scalar, expect) in [
        ("0", [0; 4], [0; 8]),
        ("1", [1, 0, 0, 0], *g_affine),
        ("n-1", pred(n), expect_neg),
        ("n", n, [0; 8]),
        ("n+1", succ(n), *g_affine),
    ] {
        let mut narrow = [0; 8];
        let mut wide = [0; 8];
        super::p256_scalarmul_narrow::p256_scalarmul(&mut narrow, &scalar, g_affine);
        super::p256_scalarmul::p256_scalarmul(&mut wide, &scalar, g_affine);
        assert_eq!(narrow, wide, "p256 order {label}");
        assert_eq!(narrow, expect, "p256 affine {label}");
    }
}

fn mixadd_p256(g256: &[u64; 12]) {
    use crate::low::generic::limb64::p256;

    let mont = |w: u64| {
        let mut raw = [0; 4];
        raw[0] = w;
        let mut out = [0; 4];
        p256::bignum_tomont_p256(&mut out, &raw);
        out
    };
    let one = mont(1);
    let mut z_one = [0u64; 4];
    z_one.copy_from_slice(&g256[8..]);
    assert_eq!(one, z_one, "p256 mont one");
    let mut affine = [0; 8];
    affine[..4].copy_from_slice(&mont(2));
    affine[4..].copy_from_slice(&mont(3));
    let mut got = [0; 12];
    let mut want = [0; 12];
    super::p256_montjmixadd_narrow::p256_montjmixadd(&mut got, g256, &affine);
    p256::p256_montjmixadd(&mut want, g256, &affine);
    assert_eq!(got, want, "portable p256 mixadd");
    let infinity = [0; 12];
    super::p256_montjmixadd_narrow::p256_montjmixadd(&mut got, &infinity, &affine);
    p256::p256_montjmixadd(&mut want, &infinity, &affine);
    assert_eq!(got, want, "portable p256 mixadd infinity");
    // G + G and G + (-G). The addition formula is unspecified as a sum
    // there; both backends still have to agree.
    let g_aff: [u64; 8] = g256[..8].try_into().unwrap();
    super::p256_montjmixadd_narrow::p256_montjmixadd(&mut got, g256, &g_aff);
    p256::p256_montjmixadd(&mut want, g256, &g_aff);
    assert_eq!(got, want, "portable p256 mixadd double");
    let neg = neg_mont_y(&g_aff, p256::bignum_neg_p256);
    super::p256_montjmixadd_narrow::p256_montjmixadd(&mut got, g256, &neg);
    p256::p256_montjmixadd(&mut want, g256, &neg);
    assert_eq!(got, want, "portable p256 mixadd inverse");
}

fn mixadd_p384(g384: &[u64; 18]) {
    use crate::low::generic::limb64::p384;

    let mont = |w: u64| {
        let mut raw = [0; 6];
        raw[0] = w;
        let mut out = [0; 6];
        p384::bignum_tomont_p384(&mut out, &raw);
        out
    };
    assert_eq!(mont(1).as_slice(), &g384[12..], "p384 mont one");
    let mut affine = [0; 12];
    affine[..6].copy_from_slice(&mont(2));
    affine[6..].copy_from_slice(&mont(3));
    let mut got = [0; 18];
    let mut want = [0; 18];
    super::p384_montjmixadd_narrow::p384_montjmixadd(&mut got, g384, &affine);
    p384::p384_montjmixadd(&mut want, g384, &affine);
    assert_eq!(got, want, "portable p384 mixadd");
    let infinity = [0; 18];
    super::p384_montjmixadd_narrow::p384_montjmixadd(&mut got, &infinity, &affine);
    p384::p384_montjmixadd(&mut want, &infinity, &affine);
    assert_eq!(got, want, "portable p384 mixadd infinity");
    let g_aff: [u64; 12] = g384[..12].try_into().unwrap();
    super::p384_montjmixadd_narrow::p384_montjmixadd(&mut got, g384, &g_aff);
    p384::p384_montjmixadd(&mut want, g384, &g_aff);
    assert_eq!(got, want, "portable p384 mixadd double");
    let neg = neg_mont_y(&g_aff, p384::bignum_neg_p384);
    super::p384_montjmixadd_narrow::p384_montjmixadd(&mut got, g384, &neg);
    p384::p384_montjmixadd(&mut want, g384, &neg);
    assert_eq!(got, want, "portable p384 mixadd inverse");
}

fn p384_order(g384: &[u64; 18]) {
    use crate::low::generic::limb64::p384;

    // The generic backend has no variable-base P-384 scalar multiplication.
    // These edges have an affine value that does not depend on either schedule.
    let g = p384_affine(g384).expect("P-384 generator");
    assert_eq!(g.0.as_slice(), &g384[..6], "p384 generator x");
    assert_eq!(g.1.as_slice(), &g384[6..12], "p384 generator y");
    let mut neg_y = [0; 6];
    p384::bignum_neg_p384(&mut neg_y, &g.1);
    let neg = (g.0, neg_y);
    let n = p384::N;
    for (label, scalar) in [
        ("0", [0; 6]),
        ("1", [1, 0, 0, 0, 0, 0]),
        ("n-1", pred(n)),
        ("n", n),
        ("n+1", succ(n)),
        ("ones", [u64::MAX; 6]),
    ] {
        let mut narrow = [0; 18];
        let mut wide = [0; 18];
        super::p384_montjscalarmul_narrow::p384_montjscalarmul(&mut narrow, &scalar, g384);
        super::p384_montjscalarmul::p384_montjscalarmul(&mut wide, &scalar, g384);
        assert_eq!(narrow, wide, "p384 order {label}");
        let affine = p384_affine(&narrow);
        match label {
            "0" | "n" => assert_eq!(affine, None, "p384 infinity {label}"),
            "1" | "n+1" => assert_eq!(affine, Some(g), "p384 generator {label}"),
            "n-1" => assert_eq!(affine, Some(neg), "p384 negation {label}"),
            "ones" => {}
            _ => unreachable!("{label}"),
        }
    }
}

fn p521_points(g521: &[u64; 27]) {
    use crate::low::generic::limb64::p521;

    let mut other = [0; 27];
    other[0] = 1;
    other[9] = 2;
    other[18] = 1;
    let mut affine = [0; 18];
    affine[0] = 3;
    affine[9] = 4;
    let mut got = [0; 27];
    let mut want = [0; 27];
    super::p521_jdouble_narrow::p521_jdouble(&mut got, g521);
    p521::p521_jdouble(&mut want, g521);
    assert_eq!(got, want, "portable p521 double");
    super::p521_jdouble_narrow::p521_jdouble(&mut got, &other);
    p521::p521_jdouble(&mut want, &other);
    assert_eq!(got, want, "portable p521 double other");
    super::p521_jadd_narrow::p521_jadd(&mut got, g521, &other);
    p521::p521_jadd(&mut want, g521, &other);
    assert_eq!(got, want, "portable p521 add");
    super::p521_jmixadd_narrow::p521_jmixadd(&mut got, g521, &affine);
    p521::p521_jmixadd(&mut want, g521, &affine);
    assert_eq!(got, want, "portable p521 mixadd");
    super::p521_jmixadd_narrow::p521_jmixadd(&mut got, &other, &affine);
    p521::p521_jmixadd(&mut want, &other, &affine);
    assert_eq!(got, want, "portable p521 mixadd other");

    let infinity = [0; 27];
    super::p521_jdouble_narrow::p521_jdouble(&mut got, &infinity);
    p521::p521_jdouble(&mut want, &infinity);
    assert_eq!(got, want, "portable p521 double infinity");
    super::p521_jadd_narrow::p521_jadd(&mut got, g521, g521);
    p521::p521_jadd(&mut want, g521, g521);
    assert_eq!(got, want, "portable p521 add double");
    super::p521_jadd_narrow::p521_jadd(&mut got, &other, &other);
    p521::p521_jadd(&mut want, &other, &other);
    assert_eq!(got, want, "portable p521 add other double");
    let neg = p521_neg(g521);
    super::p521_jadd_narrow::p521_jadd(&mut got, g521, &neg);
    p521::p521_jadd(&mut want, g521, &neg);
    assert_eq!(got, want, "portable p521 add inverse");
    // One zero z is outside the formula. The assembly then copies the other
    // point; the generic backend has no such select.
    for (label, p1, p2) in [("left", &infinity, g521), ("right", g521, &infinity)] {
        let mut wide = [0; 27];
        super::p521_jadd_narrow::p521_jadd(&mut got, p1, p2);
        super::p521_jadd::p521_jadd(&mut wide, p1, p2);
        assert_eq!(got, *g521, "p521 add infinity {label}");
        assert_eq!(wide, *g521, "p521 add infinity wide {label}");
    }
    super::p521_jadd_narrow::p521_jadd(&mut got, &infinity, &infinity);
    p521::p521_jadd(&mut want, &infinity, &infinity);
    assert_eq!(got, want, "portable p521 add infinities");

    let g_aff: [u64; 18] = g521[..18].try_into().unwrap();
    let neg_aff = p521_neg_affine(&g_aff);
    let other_aff: [u64; 18] = other[..18].try_into().unwrap();
    for (label, point, affine) in [
        ("double", g521, g_aff),
        ("inverse", g521, neg_aff),
        ("other", &other, other_aff),
    ] {
        super::p521_jmixadd_narrow::p521_jmixadd(&mut got, point, &affine);
        p521::p521_jmixadd(&mut want, point, &affine);
        assert_eq!(got, want, "portable p521 mixadd {label}");
    }
    // A zero z is outside the formula. The assembly returns the affine
    // point with z = 1; the generic backend has no such select.
    let mut wide = [0; 27];
    super::p521_jmixadd_narrow::p521_jmixadd(&mut got, &infinity, &g_aff);
    super::p521_jmixadd::p521_jmixadd(&mut wide, &infinity, &g_aff);
    assert_eq!(got, *g521, "p521 mixadd infinity");
    assert_eq!(wide, *g521, "p521 mixadd infinity wide");
}

fn p521_order(g521: &[u64; 27]) {
    use crate::low::generic::limb64::p521;

    let g = p521_affine(g521).expect("P-521 generator");
    let mut neg_y = [0; 9];
    p521::bignum_neg_p521(&mut neg_y, &g.1);
    let neg = (g.0, neg_y);
    let n = p521::N;
    for (label, scalar) in [
        ("0", [0; 9]),
        ("1", [1, 0, 0, 0, 0, 0, 0, 0, 0]),
        ("n-1", pred(n)),
        ("n", n),
        ("n+1", succ(n)),
        ("ones", [u64::MAX; 9]),
    ] {
        let mut narrow = [0; 27];
        let mut wide = [0; 27];
        let mut generic = [0; 27];
        super::p521_jscalarmul_narrow::p521_jscalarmul(&mut narrow, &scalar, g521);
        super::p521_jscalarmul::p521_jscalarmul(&mut wide, &scalar, g521);
        p521::p521_jscalarmul(&mut generic, &scalar, g521);
        assert_eq!(narrow, wide, "p521 order {label}");
        let affine = p521_affine(&narrow);
        assert_eq!(affine, p521_affine(&generic), "p521 generic {label}");
        match label {
            "0" | "n" => assert_eq!(affine, None, "p521 infinity {label}"),
            "1" | "n+1" => assert_eq!(affine, Some(g), "p521 generator {label}"),
            "n-1" => assert_eq!(affine, Some(neg), "p521 negation {label}"),
            "ones" => {}
            _ => unreachable!("{label}"),
        }
    }
}

fn ed25519_decode() {
    let mut cases = Vec::new();
    let mut identity = [0u8; 32];
    identity[0] = 1;
    cases.push(identity);
    let mut identity_sign = identity;
    identity_sign[31] = 0x80;
    cases.push(identity_sign);
    let base = hex32("5866666666666666666666666666666666666666666666666666666666666666");
    cases.push(base);
    let mut base_neg = base;
    base_neg[31] ^= 0x80;
    cases.push(base_neg);
    // y = p and y = p + 1, with the sign bit clear and set. Each is y >= p.
    for (low, high) in [(0xed, 0x7f), (0xee, 0x7f), (0xed, 0xff), (0xee, 0xff)] {
        let mut y = [0xffu8; 32];
        y[0] = low;
        y[31] = high;
        cases.push(y);
    }
    cases.push([0xff; 32]);
    cases.push([0; 32]);
    let mut two = [0u8; 32];
    two[0] = 2;
    cases.push(two);
    // y = p - 1 with the sign bit set: x = 0, which is not canonical.
    let mut neg_one_sign = [0xffu8; 32];
    neg_one_sign[0] = 0xec;
    cases.push(neg_one_sign);

    for (i, bytes) in cases.iter().enumerate() {
        let mut point = [0; 8];
        let ok = super::edwards25519_decode_narrow::edwards25519_decode(&mut point, bytes);
        let want = canonical_edwards(bytes);
        assert_eq!(ok, want.is_some(), "ed25519 decode {i}");
        if let Some(expected) = want {
            assert_eq!(
                compress_edwards(&point),
                expected,
                "ed25519 decode point {i}"
            );
        }
    }
}

/// dalek after the canonical checks of `mid::portable::edwards25519`: `y`
/// below `p`, and no sign bit when `x = 0`. dalek itself reduces `y` and
/// accepts that sign bit.
fn canonical_edwards(bytes: &[u8; 32]) -> Option<[u8; 32]> {
    use curve25519_dalek::edwards::CompressedEdwardsY;

    let mut y = *bytes;
    y[31] &= 0x7f;
    let mut one = [0u8; 32];
    one[0] = 1;
    let mut pm1 = [0xffu8; 32];
    pm1[0] = 0xec;
    pm1[31] = 0x7f;
    let sign = bytes[31] >> 7 == 1;
    if y.iter().rev().cmp(pm1.iter().rev()).is_gt() || (sign && (y == one || y == pm1)) {
        return None;
    }
    CompressedEdwardsY(*bytes)
        .decompress()
        .map(|point| point.compress().0)
}

fn ed25519_double(scalars: &[[u64; 4]]) {
    use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
    use curve25519_dalek::scalar::Scalar;

    let mut points = Vec::new();
    for scalar in scalars {
        let mut point = [0; 8];
        super::edwards25519_scalarmulbase_narrow::edwards25519_scalarmulbase(&mut point, scalar);
        points.push(point);
    }
    for (i, point) in points.iter().enumerate() {
        let dalek = CompressedEdwardsY(compress_edwards(point))
            .decompress()
            .expect("base multiple decodes");
        for (j, n) in scalars.iter().enumerate() {
            for (k, m) in scalars.iter().enumerate() {
                let mut got = [0; 8];
                super::edwards25519_scalarmuldouble_narrow::edwards25519_scalarmuldouble(
                    &mut got, n, point, m,
                );
                let want = EdwardsPoint::vartime_double_scalar_mul_basepoint(
                    &Scalar::from_bytes_mod_order(words_to_bytes(n)),
                    &dalek,
                    &Scalar::from_bytes_mod_order(words_to_bytes(m)),
                )
                .compress()
                .0;
                assert_eq!(compress_edwards(&got), want, "ed25519 double {i},{j},{k}");
            }
        }
    }
}

/// Legendre symbol by Euler's criterion, then `x * z^2 = 1` for a square,
/// with the even root.
fn invsqrt_oracle(p: &[u64; 4], samples: &[[u64; 4]]) {
    let mut pm1 = *p;
    sub_into(&mut pm1, &[1, 0, 0, 0]);
    let mut exp = pm1;
    let mut carry = 0u64;
    for limb in exp.iter_mut().rev() {
        let low = *limb & 1;
        *limb = (*limb >> 1) | (carry << 63);
        carry = low;
    }
    assert_eq!(carry, 0, "p - 1 is odd");
    for (i, x) in samples.iter().enumerate() {
        let reduced = reduce(x, p);
        let symbol = euler(&reduced, p, &exp, &pm1);
        let mut z = [0; 4];
        let got = super::bignum_invsqrt_p25519_narrow::bignum_invsqrt_p25519(&mut z, x);
        let got = match got {
            0 => 0,
            1 => 1,
            u64::MAX => -1,
            other => panic!("invsqrt symbol {other:#x} at {i}"),
        };
        assert_eq!(got, symbol, "invsqrt euler {i}");
        if symbol == 1 {
            assert_eq!(z[0] & 1, 0, "invsqrt even {i}");
            let square = reduce(&mul256(z, z), p);
            assert_eq!(
                reduce(&mul256(reduced, square), p),
                [1, 0, 0, 0],
                "invsqrt equation {i}"
            );
        }
    }
}

fn euler(x: &[u64; 4], p: &[u64; 4], exp: &[u64; 4], pm1: &[u64; 4]) -> i64 {
    if *x == [0; 4] {
        return 0;
    }
    let mut result = [1, 0, 0, 0];
    for bit in (0..256).rev() {
        result = reduce(&mul256(result, result), p);
        if (exp[bit / 64] >> (bit % 64)) & 1 == 1 {
            result = reduce(&mul256(result, *x), p);
        }
    }
    if result == [1, 0, 0, 0] {
        1
    } else if result == *pm1 {
        -1
    } else {
        panic!("euler {result:?}")
    }
}

fn p256_base(g256: &[u64; 12], g_affine: &[u64; 8]) {
    use crate::low::generic::limb64::p256;

    // The generator table `p256_scalarmulbase` reads: row i is
    // `2^(6i) * j * G` for j from 1 to 32, Montgomery affine. Scalars 0 and
    // 1 only select the first entry.
    let table = p256_generator_table(g256);
    assert_eq!(&table[0][..8], &g256[..8], "row 0 digit 1 is G");
    assert!(
        table[42].iter().any(|limb| *limb != 0),
        "a late row is nonzero"
    );

    let n = p256::N;
    let below = pred(n);
    let full = [u64::MAX; 4];
    assert!(
        exercises_base_table(&below),
        "n - 1 must hit a later window and a digit above 32"
    );
    assert!(
        exercises_base_table(&full),
        "a full-width scalar must hit a later window and a digit above 32"
    );
    let neg_g = neg_p256(g_affine);
    for (label, scalar, expect) in [
        ("0", [0; 4], Some([0; 8])),
        ("1", [1, 0, 0, 0], Some(*g_affine)),
        ("n-1", below, Some(neg_g)),
        ("n", n, Some([0; 8])),
        ("full", full, None),
    ] {
        let mut narrow = [0; 8];
        let mut generic = [0; 8];
        super::p256_scalarmulbase_narrow::p256_scalarmulbase(&mut narrow, &scalar, &table);
        p256::p256_scalarmulbase(&mut generic, &scalar, &table);
        assert_eq!(narrow, generic, "p256 base generic {label}");
        if let Some(expect) = expect {
            assert_eq!(narrow, expect, "p256 base affine {label}");
        }
    }
}

/// Row i holds `2^(6i) * j * G` for j from 1 to 32, in Montgomery affine form.
fn p256_generator_table(g: &[u64; 12]) -> Box<[[u64; 256]; 43]> {
    let mut rows = vec![[0u64; 256]; 43];
    let mut base = *g;
    for row in &mut rows {
        let mut multiple = base;
        for (j, entry) in (1..).zip(row.as_chunks_mut::<8>().0) {
            *entry = mont_affine_p256(&multiple);
            let kept = multiple;
            if j == 1 {
                super::p256_montjdouble::p256_montjdouble(&mut multiple, &kept);
            } else {
                super::p256_montjadd::p256_montjadd(&mut multiple, &kept, &base);
            }
        }
        for _ in 0..6 {
            let kept = base;
            super::p256_montjdouble::p256_montjdouble(&mut base, &kept);
        }
    }
    rows.try_into().unwrap()
}

/// `(x / z^2, y / z^3)` in Montgomery form.
fn mont_affine_p256(point: &[u64; 12]) -> [u64; 8] {
    let z: [u64; 4] = limbs_at(&point[8..]);
    assert_ne!(z, [0; 4], "affine of a zero z");
    let mut plain = [0; 4];
    super::bignum_demont_p256::bignum_demont_p256(&mut plain, &z);
    let mut inv = [0; 4];
    super::bignum_inv_p256::bignum_inv_p256(&mut inv, &plain);
    let mut inv_m = [0; 4];
    super::bignum_tomont_p256::bignum_tomont_p256(&mut inv_m, &inv);
    let mut z2 = [0; 4];
    super::bignum_montsqr_p256::bignum_montsqr_p256(&mut z2, &inv_m);
    let mut z3 = [0; 4];
    super::bignum_montmul_p256::bignum_montmul_p256(&mut z3, &z2, &inv_m);
    let mut xy = [0; 8];
    let (out, _) = xy.as_chunks_mut::<4>();
    super::bignum_montmul_p256::bignum_montmul_p256(&mut out[0], &limbs_at(&point[..4]), &z2);
    super::bignum_montmul_p256::bignum_montmul_p256(&mut out[1], &limbs_at(&point[4..8]), &z3);
    xy
}

/// The scalar's raw 6-bit windows include one after the first and one above
/// 32, which scalars 0 and 1 never select.
fn exercises_base_table(scalar: &[u64; 4]) -> bool {
    let mut late = false;
    let mut wide_digit = false;
    for i in 0..43 {
        let bit = 6 * i;
        let (word, shift) = (bit / 64, bit % 64);
        let mut window = scalar[word] >> shift;
        if shift > 58 && word < 3 {
            window |= scalar[word + 1] << (64 - shift);
        }
        let digit = (window & 0x3f) as u8;
        late |= i > 0 && digit != 0;
        wide_digit |= digit > 32;
    }
    late && wide_digit
}

/// Negate the Montgomery y coordinate of an affine point, x then y.
fn neg_mont_y<const N: usize, const Y: usize>(
    affine: &[u64; N],
    mut neg: impl FnMut(&mut [u64; Y], &[u64; Y]),
) -> [u64; N] {
    assert_eq!(N, 2 * Y);
    let mut y = [0; Y];
    y.copy_from_slice(&affine[Y..]);
    let mut negated = [0; Y];
    neg(&mut negated, &y);
    let mut out = *affine;
    out[Y..].copy_from_slice(&negated);
    out
}

fn limbs_at<const N: usize>(src: &[u64]) -> [u64; N] {
    src.try_into().unwrap()
}

/// Affine Montgomery `(x, y)`, or `None` when `z` is zero.
fn p384_affine(point: &[u64; 18]) -> Option<([u64; 6], [u64; 6])> {
    use crate::low::generic::limb64::p384;

    let z: [u64; 6] = limbs_at(&point[12..]);
    if z == [0; 6] {
        return None;
    }
    let mut z_norm = [0; 6];
    p384::bignum_demont_p384(&mut z_norm, &z);
    let mut z_inv = [0; 6];
    p384::bignum_inv_p384(&mut z_inv, &z_norm);
    let mut z_inv_m = [0; 6];
    p384::bignum_tomont_p384(&mut z_inv_m, &z_inv);
    let mut z_inv2 = [0; 6];
    p384::bignum_montsqr_p384(&mut z_inv2, &z_inv_m);
    let mut z_inv3 = [0; 6];
    p384::bignum_montmul_p384(&mut z_inv3, &z_inv2, &z_inv_m);
    let mut x = [0; 6];
    let mut y = [0; 6];
    p384::bignum_montmul_p384(&mut x, &limbs_at(&point[..6]), &z_inv2);
    p384::bignum_montmul_p384(&mut y, &limbs_at(&point[6..12]), &z_inv3);
    Some((x, y))
}

/// Affine `(x, y)`, or `None` when `z` is zero.
fn p521_affine(point: &[u64; 27]) -> Option<([u64; 9], [u64; 9])> {
    use crate::low::generic::limb64::p521;

    let z: [u64; 9] = limbs_at(&point[18..]);
    if z == [0; 9] {
        return None;
    }
    let mut z_inv = [0; 9];
    p521::bignum_inv_p521(&mut z_inv, &z);
    let mut z_inv2 = [0; 9];
    p521::bignum_sqr_p521(&mut z_inv2, &z_inv);
    let mut z_inv3 = [0; 9];
    p521::bignum_mul_p521(&mut z_inv3, &z_inv2, &z_inv);
    let mut x = [0; 9];
    let mut y = [0; 9];
    p521::bignum_mul_p521(&mut x, &limbs_at(&point[..9]), &z_inv2);
    p521::bignum_mul_p521(&mut y, &limbs_at(&point[9..18]), &z_inv3);
    Some((x, y))
}

fn p521_neg(point: &[u64; 27]) -> [u64; 27] {
    use crate::low::generic::limb64::p521;

    let mut out = *point;
    let mut y = [0; 9];
    p521::bignum_neg_p521(&mut y, &limbs_at(&point[9..18]));
    out[9..18].copy_from_slice(&y);
    out
}

fn p521_neg_affine(point: &[u64; 18]) -> [u64; 18] {
    use crate::low::generic::limb64::p521;

    let mut out = *point;
    let mut y = [0; 9];
    p521::bignum_neg_p521(&mut y, &limbs_at(&point[9..]));
    out[9..].copy_from_slice(&y);
    out
}

fn neg_p256(g: &[u64; 8]) -> [u64; 8] {
    // p_256 = 2^256 - 2^224 + 2^192 + 2^96 - 1.
    let p = [
        0xffff_ffff_ffff_ffff,
        0x0000_0000_ffff_ffff,
        0,
        0xffff_ffff_0000_0001,
    ];
    let mut y = [0; 4];
    y.copy_from_slice(&g[4..]);
    let mut ny = p;
    sub_into(&mut ny, &y);
    let mut out = *g;
    out[4..].copy_from_slice(&ny);
    out
}

fn madd_n(x: [u64; 4], y: [u64; 4], c: [u64; 4], n: [u64; 4]) -> [u64; 4] {
    let mut wide = [0; 9];
    wide[..8].copy_from_slice(&mul256(x, y));
    let mut carry = 0u64;
    for i in 0..4 {
        let (sum, c1) = wide[i].overflowing_add(c[i]);
        let (sum, c2) = sum.overflowing_add(carry);
        wide[i] = sum;
        carry = u64::from(c1 || c2);
    }
    for limb in wide.iter_mut().take(8).skip(4) {
        let (sum, c1) = limb.overflowing_add(carry);
        *limb = sum;
        carry = u64::from(c1);
    }
    wide[8] = carry;
    reduce(&wide, &n)
}

fn mul256(x: [u64; 4], y: [u64; 4]) -> [u64; 8] {
    let mut acc = [0u128; 8];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 {
            let t = acc[i + j] + u128::from(x[i]) * u128::from(y[j]) + carry;
            acc[i + j] = t & u128::from(u64::MAX);
            carry = t >> 64;
        }
        acc[i + 4] += carry;
    }
    let mut out = [0; 8];
    for (out, acc) in out.iter_mut().zip(acc) {
        assert!(acc <= u128::from(u64::MAX), "product limb overflowed");
        *out = acc as u64;
    }
    out
}

/// `prod` mod `modulus`, `prod` little-endian and shorter than twice the
/// modulus width in bits. `modulus` is nonzero and below `2^(64N - 1)`.
fn reduce<const N: usize, const W: usize>(prod: &[u64; W], modulus: &[u64; N]) -> [u64; N] {
    let mut r = [0u64; N];
    for bit in (0..W * 64).rev() {
        let mut carry = 0u64;
        for limb in &mut r {
            let next = *limb >> 63;
            *limb = (*limb << 1) | carry;
            carry = next;
        }
        assert_eq!(carry, 0, "residue doubled past its width");
        let bit_set = (prod[bit / 64] >> (bit % 64)) & 1;
        let mut add = bit_set;
        for limb in &mut r {
            let (sum, c) = limb.overflowing_add(add);
            *limb = sum;
            add = u64::from(c);
        }
        assert_eq!(add, 0, "residue addition carried out");
        if ge(&r, modulus) {
            sub_into(&mut r, modulus);
        }
        assert!(!ge(&r, modulus), "residue not reduced");
    }
    r
}

fn ge<const N: usize>(a: &[u64; N], b: &[u64; N]) -> bool {
    for i in (0..N).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

fn sub_into<const N: usize>(a: &mut [u64; N], b: &[u64; N]) {
    let mut borrow = 0u64;
    for i in 0..N {
        let (diff, b1) = a[i].overflowing_sub(b[i]);
        let (diff, b2) = diff.overflowing_sub(borrow);
        a[i] = diff;
        borrow = u64::from(b1 || b2);
    }
    assert_eq!(borrow, 0, "subtraction borrowed");
}

fn succ<const N: usize>(mut a: [u64; N]) -> [u64; N] {
    let mut carry = 1u64;
    for limb in &mut a {
        let (sum, c) = limb.overflowing_add(carry);
        *limb = sum;
        carry = u64::from(c);
    }
    a
}

fn pred<const N: usize>(mut a: [u64; N]) -> [u64; N] {
    let mut borrow = 1u64;
    for limb in &mut a {
        let (diff, b) = limb.overflowing_sub(borrow);
        *limb = diff;
        borrow = u64::from(b);
    }
    a
}

fn hex32(s: &str) -> [u8; 32] {
    hex::decode(s).unwrap().try_into().unwrap()
}

fn words_to_bytes(words: &[u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (chunk, word) in out.as_chunks_mut::<8>().0.iter_mut().zip(words) {
        *chunk = word.to_le_bytes();
    }
    out
}

fn bytes_to_words(bytes: &[u8; 32]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for (word, chunk) in out.iter_mut().zip(bytes.as_chunks::<8>().0) {
        *word = u64::from_le_bytes(*chunk);
    }
    out
}

fn compress_edwards(p: &[u64; 8]) -> [u8; 32] {
    let y3 = (p[7] & 0x7fff_ffff_ffff_ffff) | (p[0] << 63);
    let mut out = [0u8; 32];
    for (i, word) in [p[4], p[5], p[6], y3].into_iter().enumerate() {
        out[8 * i..8 * i + 8].copy_from_slice(&word.to_le_bytes());
    }
    out
}

fn limbs_to_bytes(limbs: [u64; 4]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (i, limb) in limbs.iter().enumerate() {
        bytes[i * 8..][..8].copy_from_slice(&limb.to_le_bytes());
    }
    bytes
}

// The override is process-wide, so each schedule is a child. Disable wins
// over force, and the mux calls the schedule the flag names.
#[cfg(all(any(debug_assertions, rind_cpu_disable), not(rind_fips)))]
#[test]
fn mux_follows_the_override() {
    const CHILD: &str = "RIND_TEST_MUX_SCHEDULE";
    if let Some(mode) = std::env::var_os(CHILD) {
        let wide = mode == "wide";
        assert_eq!(super::cpu::wide_multiplier(), wide);
        let scalar = [1u64, 0, 0, 0];
        let point = [9u64, 0, 0, 0];
        let mut via_mux = [0; 4];
        let mut direct = [0; 4];
        super::wide_mux::curve25519_x25519(&mut via_mux, &scalar, &point);
        if wide {
            super::curve25519_x25519::curve25519_x25519(&mut direct, &scalar, &point);
        } else {
            super::curve25519_x25519_narrow::curve25519_x25519(&mut direct, &scalar, &point);
        }
        assert_eq!(via_mux, direct);
        // A second product must still be the schedule this flag names. The
        // mux calls that schedule directly.
        let (x, y) = ([1u64, 0, 0, 0], [9u64, 0, 0, 0]);
        let (mut via_mul, mut direct_mul) = ([0; 4], [0; 4]);
        super::wide_mux::bignum_mul_p25519(&mut via_mul, &x, &y);
        super::wide_mux::bignum_mul_p25519(&mut via_mux, &x, &y);
        if wide {
            super::bignum_mul_p25519::bignum_mul_p25519(&mut direct_mul, &x, &y);
        } else {
            super::bignum_mul_p25519_narrow::bignum_mul_p25519(&mut direct_mul, &x, &y);
        }
        assert_eq!(via_mul, direct_mul);
        assert_eq!(via_mux, direct_mul);
        let (mut via_sqr, mut direct_sqr) = ([0; 4], [0; 4]);
        super::wide_mux::bignum_sqr_p25519(&mut via_sqr, &x);
        if wide {
            super::bignum_sqr_p25519::bignum_sqr_p25519(&mut direct_sqr, &x);
        } else {
            super::bignum_sqr_p25519_narrow::bignum_sqr_p25519(&mut direct_sqr, &x);
        }
        assert_eq!(via_sqr, direct_sqr);
        println!("{CHILD} done");
        return;
    }
    for (mode, disable, force) in [
        ("narrow", true, true),
        ("wide", false, true),
        ("narrow", true, false),
    ] {
        let mut cmd = super::cpu::reexec();
        // `--exact` matches the harness name, not the function's last
        // component. `module_path!` includes the crate, which libtest drops.
        let test = concat!(module_path!(), "::mux_follows_the_override");
        let test = test.split_once("::").unwrap().1;
        cmd.args([test, "--exact", "--nocapture"])
            .env(CHILD, mode)
            .env_remove("RIND_CPU_DISABLE_wide_mul")
            .env_remove("RIND_CPU_FORCE_wide_mul");
        if disable {
            cmd.env("RIND_CPU_DISABLE_wide_mul", "1");
        }
        if force {
            cmd.env("RIND_CPU_FORCE_wide_mul", "1");
        }
        let output = cmd.output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        // Detection is silent, so the marker proves the child ran, and the
        // child's own assertion that the multiplier is `mode` proves which
        // override won: disable over force.
        assert!(
            output.status.success() && stdout.contains(&format!("{CHILD} done")),
            "{mode} (disable {disable}, force {force}):\n{stdout}{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

fn qemu_seed(n: usize) -> Vec<u8> {
    let seed = super::ct_qemu::seed().to_le_bytes();
    seed.iter().cycle().take(n).copied().collect()
}

fn trace_ecdh(algorithm: &'static crate::agreement::Algorithm, len: usize) {
    use crate::agreement::PrivateKey;

    let mut peer_scalar = vec![1u8; len];
    peer_scalar[len - 1] = 2;
    let peer = PrivateKey::from_scalar(algorithm, &peer_scalar).unwrap();
    let peer = peer.public_key().as_ref().to_vec();
    // Every byte comes from the seed except the leading one, which stays
    // zero. A big-endian NIST scalar is then below 2^(8*(len-1)), which is
    // below the order, and the high windows differ between the two seeds.
    let mut scalar = qemu_seed(len);
    scalar[0] = 0;
    if scalar.iter().all(|&byte| byte == 0) {
        scalar[len - 1] = 1;
    }
    super::ct_qemu::traced(|| {
        let key = PrivateKey::from_scalar(algorithm, &scalar).unwrap();
        key.agree(&peer).is_ok()
    });
}

// Valgrind on the arm64 runner sees the schedule that runner's core selects,
// which is wide. `admin/ct-qemu` builds with `--cfg rind_cpu_disable` and
// traces each of these again with `RIND_CPU_DISABLE_wide_mul=1`, so the
// narrow schedules are in a trace too.

#[test]
#[ignore = "admin/ct-qemu runs it under qemu"]
fn ct_qemu_x25519() {
    trace_ecdh(&crate::agreement::X25519, 32);
}

#[test]
#[ignore = "admin/ct-qemu runs it under qemu"]
fn ct_qemu_ecdh_p256() {
    trace_ecdh(&crate::agreement::ECDH_P256, 32);
}

#[test]
#[ignore = "admin/ct-qemu runs it under qemu"]
fn ct_qemu_ecdh_p384() {
    trace_ecdh(&crate::agreement::ECDH_P384, 48);
}

#[test]
#[ignore = "admin/ct-qemu runs it under qemu"]
fn ct_qemu_ecdh_p521() {
    trace_ecdh(&crate::agreement::ECDH_P521, 66);
}

#[test]
#[ignore = "admin/ct-qemu runs it under qemu"]
fn ct_qemu_ed25519() {
    use crate::ed25519::KeyPair as Ed25519KeyPair;

    let seed = qemu_seed(32);
    let message = qemu_seed(40);
    super::ct_qemu::traced(|| {
        let key = Ed25519KeyPair::from_seed(&seed).unwrap();
        key.sign(&message)
    });
}

/// A 16-word Montgomery product. On a narrow multiplier that is
/// `bignum_kmul_16_32`, `bignum_ksqr_16_32`, and `bignum_emontredc_8n` at
/// k = 16, which is every RSA-2048 CRT exponentiation. The inputs differ
/// between the two seeds; the low limb of the modulus does not.
#[test]
#[ignore = "admin/ct-qemu runs it under qemu"]
fn ct_qemu_mont16() {
    let seed = qemu_seed(16 * 8 * 3);
    let mut modulus = [0u64; 16];
    let mut x = [0u64; 16];
    let mut y = [0u64; 16];
    words_into(&seed[..128], &mut modulus);
    words_into(&seed[128..256], &mut x);
    words_into(&seed[256..], &mut y);
    modulus[0] = 1;
    modulus[15] |= 1 << 63;
    x[15] &= !(1 << 63);
    y[15] &= !(1 << 63);
    let mut n0 = [0u64];
    super::bignum_negmodinv::bignum_negmodinv(&mut n0, &modulus[..1]);
    super::ct_qemu::traced(|| {
        let mut z = [0u64; 16];
        super::mont::mont_mul(&mut z, &x, &y, &modulus, n0[0]);
        super::mont::mont_sqr(&mut z, &x, &modulus, n0[0]);
        z
    });
}

fn words_into(bytes: &[u8], out: &mut [u64]) {
    let (chunks, _) = bytes.as_chunks::<8>();
    for (limb, chunk) in out.iter_mut().zip(chunks) {
        *limb = u64::from_le_bytes(*chunk);
    }
}
