// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The narrow and `_alt` schedules compute the same values.
//!
//! Each routine is called on zero, one, an all-ones limb, and a mixed
//! pattern, and the curve routines also on a generator. The points are the
//! ones the scalar-multiplication proofs state: Montgomery Jacobian with
//! z = 1 for P-256 and P-384, and Jacobian with z = 1 for P-521.

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
}

// The override is process-wide, so each schedule is a child. Disable wins
// over force, and the mux calls the schedule the flag names.
#[cfg(any(debug_assertions, rind_cpu_disable))]
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
        return;
    }
    for (mode, disable, force) in [
        ("narrow", true, true),
        ("wide", false, true),
        ("narrow", true, false),
    ] {
        let mut cmd = std::process::Command::new(std::env::current_exe().unwrap());
        cmd.args(["--exact", "mux_follows_the_override", "--nocapture"])
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
        assert!(
            output.status.success(),
            "{mode}: {}{}",
            String::from_utf8_lossy(&output.stdout),
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
    // The low bytes carry the seed. The rest stay zero, so the scalar is
    // below every curve order `from_scalar` accepts.
    let mut scalar = vec![0u8; len];
    let seed = qemu_seed(8);
    scalar[..seed.len()].copy_from_slice(&seed);
    super::ct_qemu::traced(|| {
        let key = PrivateKey::from_scalar(algorithm, &scalar).unwrap();
        key.agree(&peer).is_ok()
    });
}

// Valgrind on the arm64 runner sees the schedule that runner's core selects,
// which is wide. `admin/ct-qemu` traces these with the narrow schedules
// forced, so the NEON field arithmetic is in the trace.

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
    use crate::signature::Ed25519KeyPair;

    let seed = qemu_seed(32);
    let message = qemu_seed(40);
    super::ct_qemu::traced(|| {
        let key = Ed25519KeyPair::from_seed(&seed).unwrap();
        key.sign(&message)
    });
}

#[test]
#[ignore = "admin/ct-qemu runs it under qemu"]
fn ct_qemu_rsa() {
    use crate::signature::RsaKeyPair;
    use crate::signature::sign::RSA_PKCS1_SHA256;

    let key = RsaKeyPair::from_pkcs8(include_bytes!("../../high/rsa/rsa2048.pkcs8.der")).unwrap();
    let message = qemu_seed(32);
    super::ct_qemu::traced(|| key.sign(&RSA_PKCS1_SHA256, &message).unwrap());
}
