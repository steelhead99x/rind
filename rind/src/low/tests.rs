// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

fn bignum_mux_equiv(p: u64, x_if_p: &[u64], y_if_not_p: &[u64]) {
    let mut model_z = vec![0; x_if_p.len()];
    let mut real_z = vec![0; x_if_p.len()];
    model::bignum_mux(p, &mut model_z, x_if_p, y_if_not_p);
    super::bignum_mux(p, &mut real_z, x_if_p, y_if_not_p);
    assert_eq!(model_z, real_z);
}

#[test]
fn bignum_mux() {
    bignum_mux_equiv(0, &[0u64; 4], &[1u64; 4]);
    bignum_mux_equiv(1, &[1u64; 4], &[0xff; 4]);
    bignum_mux_equiv(u64::MAX, &[1; 1], &[0; 1]);
}

// ld64 splits a Mach-O object into atoms at each CFI frame, and can
// dead-strip one that is reached only by branches with no relocation, such as
// a routine joined into another's naked function.
#[test]
fn apple_routines_open_one_cfi_frame() {
    fn visit(dir: &std::path::Path, files: &mut usize) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                visit(&path, files);
            } else if path.to_str().unwrap().ends_with(".apple.s") {
                let text = std::fs::read_to_string(&path).unwrap();
                let frames = text
                    .lines()
                    .filter(|line| line.trim() == ".cfi_startproc")
                    .count();
                assert!(frames <= 1, "{}: {frames} CFI frames", path.display());
                *files += 1;
            }
        }
    }

    let mut files = 0;
    visit(
        concat!(env!("CARGO_MANIFEST_DIR"), "/src/low").as_ref(),
        &mut files,
    );
    assert_ne!(files, 0);
}

mod model {
    pub(super) fn bignum_mux(p: u64, z: &mut [u64], x_if_p: &[u64], y_if_not_p: &[u64]) {
        if p > 0 {
            z.copy_from_slice(x_if_p);
        } else {
            z.copy_from_slice(y_if_not_p);
        }
    }
}

#[test]
fn test_edwards25519_decode() {
    use hex::FromHex;

    // valid pubkey from RFC 8032
    let pk_hex = "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a";
    let pk = <[u8; 32]>::from_hex(pk_hex).unwrap();
    let mut point = [0u64; 8];
    assert!(super::edwards25519_decode(&mut point, &pk));

    // invalid pubkey
    assert!(!super::edwards25519_decode(&mut point, &[0xffu8; 32]));
}

// A source with `unsafe` checks its preconditions in every build, so a
// release binary's soundness never rests on its callers.
#[test]
fn no_debug_assert_beside_unsafe() {
    fn visit(dir: &std::path::Path, found: &mut Vec<String>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                visit(&path, found);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let text = std::fs::read_to_string(&path).unwrap();
                // Spelled apart, so this file does not match itself.
                let debug = ["debug", "_assert"].concat();
                let asserts = ["!", "_eq!", "_ne!"]
                    .iter()
                    .any(|bang| text.contains(&format!("{debug}{bang}")));
                let unsafe_ = [
                    "unsafe {",
                    "unsafe fn",
                    "unsafe extern",
                    "unsafe(",
                    "unsafe impl",
                ]
                .iter()
                .any(|word| text.contains(word));
                if asserts && unsafe_ {
                    found.push(path.display().to_string());
                }
            }
        }
    }

    let mut found = Vec::new();
    visit(
        concat!(env!("CARGO_MANIFEST_DIR"), "/src/low").as_ref(),
        &mut found,
    );
    assert!(
        found.is_empty(),
        "debug assertions beside `unsafe`: {found:?}"
    );
}

/// Each wrapper that takes slices refuses mismatched ones, by panicking
/// before its assembly runs. CI runs this in release builds too, where a
/// debug assertion would not fire.
#[test]
fn wrappers_refuse_mismatched_slices() {
    #[repr(align(32))]
    struct Aligned<const N: usize>([i16; N]);

    // 2 bytes past a 32-byte boundary.
    fn misaligned<const N: usize>(buf: &mut Aligned<1024>) -> &mut [i16; N] {
        (&mut buf.0[1..1 + N]).try_into().unwrap()
    }

    let mut cases: Vec<(&str, fn())> = vec![
        ("mont_mul", || {
            super::mont_mul(&mut [0; 4], &[0; 4], &[0; 3], &[1; 4], 1)
        }),
        ("mont_sqr", || {
            super::mont_sqr(&mut [0; 3], &[0; 4], &[1; 4], 1)
        }),
        ("mont_mul, 1 word", || {
            super::mont_mul(&mut [0; 1], &[0; 1], &[], &[1; 1], 1)
        }),
        ("sha1", || {
            super::sha1_compress_blocks(&mut [0; 5], &[0; 63])
        }),
        ("sha256", || {
            super::sha256_compress_blocks(&mut [0; 8], &[0; 65])
        }),
        ("sha512", || {
            super::sha512_compress_blocks(&mut [0; 8], &[0; 127])
        }),
    ];

    #[cfg(rind_backend = "x86_64")]
    {
        use super::x86_64::*;
        cases.extend::<[(&str, fn()); _]>([
            ("mux", || {
                bignum_mux::bignum_mux(1, &mut [0; 4], &[0; 4], &[0; 3])
            }),
            ("copy_row", || {
                bignum_copy_row_from_table::bignum_copy_row_from_table(
                    &mut [0; 4],
                    &[0; 15],
                    4,
                    4,
                    0,
                )
            }),
            ("modadd", || {
                bignum_modadd::bignum_modadd(&mut [0; 4], &[0; 4], &[0; 4], &[1; 3])
            }),
            ("modsub", || {
                bignum_modsub::bignum_modsub(&mut [0; 4], &[0; 3], &[0; 4], &[1; 4])
            }),
            ("modinv", || {
                bignum_modinv::bignum_modinv(&mut [0; 4], &[0; 4], &[1; 4], &mut [0; 11])
            }),
            ("montmul", || {
                bignum_montmul::bignum_montmul(&mut [0; 4], &[0; 4], &[0; 3], &[1; 4])
            }),
            ("demont", || {
                bignum_demont::bignum_demont(&mut [0; 4], &[0; 3], &[1; 4])
            }),
            ("montifier", || {
                bignum_montifier::bignum_montifier(&mut [0; 4], &[1; 4], &mut [0; 3])
            }),
            ("montredc", || {
                bignum_montredc::bignum_montredc(&mut [0; 4], &[0; 8], &[1; 3], 1)
            }),
            ("mul", || {
                bignum_mul::bignum_mul(&mut [0; 7], &[0; 4], &[0; 4])
            }),
            ("emontredc_8n", || {
                bignum_emontredc_8n::bignum_emontredc_8n(&mut [0; 8], &[1; 4], 1);
            }),
            ("optsub", || {
                bignum_optsub::bignum_optsub(&mut [0; 4], &[0; 4], &[0; 3], 1)
            }),
            ("negmodinv", || {
                bignum_negmodinv::bignum_negmodinv(&mut [0; 4], &[1; 3])
            }),
            ("coprime", || {
                bignum_coprime::bignum_coprime(&[1; 4], &[1; 4], &mut [0; 7]);
            }),
            ("kmul_16_32", || {
                bignum_kmul_16_32::bignum_kmul_16_32(&mut [0; 32], &[0; 16], &[0; 15], &mut [0; 32])
            }),
            ("kmul_32_64", || {
                bignum_kmul_32_64::bignum_kmul_32_64(&mut [0; 63], &[0; 32], &[0; 32], &mut [0; 96])
            }),
            ("ksqr_16_32", || {
                bignum_ksqr_16_32::bignum_ksqr_16_32(&mut [0; 32], &[0; 15], &mut [0; 24])
            }),
            ("ksqr_32_64", || {
                bignum_ksqr_32_64::bignum_ksqr_32_64(&mut [0; 64], &[0; 31], &mut [0; 72])
            }),
            ("mont_exp", || {
                mont_exp::mont_exp(&mut [0; 4], &[0; 4], &[0; 3], &[1], &[1; 4], 1)
            }),
            ("rej_uniform", || {
                mlkem_rej_uniform_vartime::mlkem_rej_uniform_vartime(
                    &mut [0; 256],
                    &[0; 13],
                    &[0; 4096],
                );
            }),
            ("ntt", || {
                mlkem_ntt::mlkem_ntt(misaligned(&mut Aligned([0; 1024])), &[0; 624])
            }),
            ("intt", || {
                mlkem_intt::mlkem_intt(misaligned(&mut Aligned([0; 1024])), &[0; 624])
            }),
            ("tobytes", || {
                mlkem_tobytes::mlkem_tobytes(&mut [0; 384], misaligned(&mut Aligned([0; 1024])))
            }),
            ("frombytes", || {
                mlkem_frombytes::mlkem_frombytes(misaligned(&mut Aligned([0; 1024])), &[0; 384])
            }),
            ("tomont", || {
                mlkem_tomont::mlkem_tomont(misaligned(&mut Aligned([0; 1024])))
            }),
            ("unpack", || {
                mlkem_unpack::mlkem_unpack(misaligned(&mut Aligned([0; 1024])))
            }),
            ("reduce", || {
                mlkem_reduce::mlkem_reduce(misaligned(&mut Aligned([0; 1024])))
            }),
            ("mulcache", || {
                let (a, q) = (Aligned([0; 256]), Aligned([0; 624]));
                mlkem_mulcache_compute::mlkem_mulcache_compute(
                    misaligned(&mut Aligned([0; 1024])),
                    &a.0,
                    &q.0,
                )
            }),
            ("basemul", || {
                let (mut r, b, bt) = (Aligned([0; 256]), Aligned([0; 768]), Aligned([0; 384]));
                let mut buf = Aligned([0; 1024]);
                let a = misaligned(&mut buf);
                mlkem_basemul_k3::mlkem_basemul_k3(&mut r.0, a, &b.0, &bt.0)
            }),
        ]);
    }

    #[cfg(rind_backend = "aarch64")]
    {
        use super::aarch64::*;
        cases.extend::<[(&str, fn()); _]>([
            ("mux", || {
                bignum_mux::bignum_mux(1, &mut [0; 4], &[0; 4], &[0; 3])
            }),
            ("copy_row", || {
                bignum_copy_row_from_table::bignum_copy_row_from_table(
                    &mut [0; 4],
                    &[0; 15],
                    4,
                    4,
                    0,
                )
            }),
            ("copy_row_8n", || {
                bignum_copy_row_from_table_8n::bignum_copy_row_from_table_8n(
                    &mut [0; 8],
                    &[0; 31],
                    4,
                    8,
                    0,
                )
            }),
            ("copy_row_16", || {
                bignum_copy_row_from_table_16::bignum_copy_row_from_table_16(
                    &mut [0; 16],
                    &[0; 63],
                    4,
                    0,
                )
            }),
            ("copy_row_32", || {
                bignum_copy_row_from_table_32::bignum_copy_row_from_table_32(
                    &mut [0; 32],
                    &[0; 127],
                    4,
                    0,
                )
            }),
            ("modadd", || {
                bignum_modadd::bignum_modadd(&mut [0; 4], &[0; 4], &[0; 4], &[1; 3])
            }),
            ("modsub", || {
                bignum_modsub::bignum_modsub(&mut [0; 4], &[0; 3], &[0; 4], &[1; 4])
            }),
            ("modinv", || {
                bignum_modinv::bignum_modinv(&mut [0; 4], &[0; 4], &[1; 4], &mut [0; 11])
            }),
            ("montmul", || {
                bignum_montmul::bignum_montmul(&mut [0; 4], &[0; 4], &[0; 3], &[1; 4])
            }),
            ("montsqr", || {
                bignum_montsqr::bignum_montsqr(&mut [0; 4], &[0; 3], &[1; 4])
            }),
            ("demont", || {
                bignum_demont::bignum_demont(&mut [0; 4], &[0; 3], &[1; 4])
            }),
            ("montifier", || {
                bignum_montifier::bignum_montifier(&mut [0; 4], &[1; 4], &mut [0; 3])
            }),
            ("montredc", || {
                bignum_montredc::bignum_montredc(&mut [0; 4], &[0; 8], &[1; 3], 1)
            }),
            ("mul", || {
                bignum_mul::bignum_mul(&mut [0; 7], &[0; 4], &[0; 4])
            }),
            ("optsub", || {
                bignum_optsub::bignum_optsub(&mut [0; 4], &[0; 4], &[0; 3], 1)
            }),
            ("negmodinv", || {
                bignum_negmodinv::bignum_negmodinv(&mut [0; 4], &[1; 3])
            }),
            ("coprime", || {
                bignum_coprime::bignum_coprime(&[1; 4], &[1; 4], &mut [0; 7]);
            }),
            ("ntt", || {
                let (z, z56) = (Aligned([0; 80]), Aligned([0; 384]));
                mlkem_ntt::mlkem_ntt(misaligned(&mut Aligned([0; 1024])), &z.0, &z56.0)
            }),
            ("intt", || {
                let (z, z56) = (Aligned([0; 80]), Aligned([0; 384]));
                mlkem_intt::mlkem_intt(misaligned(&mut Aligned([0; 1024])), &z.0, &z56.0)
            }),
            ("tobytes", || {
                mlkem_tobytes::mlkem_tobytes(&mut [0; 384], misaligned(&mut Aligned([0; 1024])))
            }),
        ]);
    }

    let accepted: Vec<_> = cases
        .iter()
        .filter(|(_, call)| std::panic::catch_unwind(call).is_ok())
        .map(|(name, _)| *name)
        .collect();
    assert!(
        accepted.is_empty(),
        "ran with mismatched arguments: {accepted:?}"
    );
}
