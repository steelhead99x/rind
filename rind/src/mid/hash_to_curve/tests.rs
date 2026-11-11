// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::{ExpandError, expand_sha256, expand_sha384, expand_sha512, reduce_be};
use crate::low::ct::{into_public, secret_slice};
use crate::mid::{p256, p384, p521};

#[derive(serde::Deserialize)]
struct ExpandFile {
    #[serde(rename = "DST")]
    dst: String,
    tests: Vec<ExpandCase>,
}

#[derive(serde::Deserialize)]
struct ExpandCase {
    msg: String,
    len_in_bytes: String,
    uniform_bytes: String,
}

#[derive(serde::Deserialize)]
struct SuiteFile {
    dst: String,
    vectors: Vec<SuiteCase>,
}

#[derive(serde::Deserialize)]
struct SuiteCase {
    msg: String,
    u: [String; 2],
    #[serde(rename = "Q0")]
    q0: Xy,
    #[serde(rename = "Q1")]
    q1: Xy,
    #[serde(rename = "P")]
    p: Xy,
}

#[derive(serde::Deserialize)]
struct Xy {
    x: String,
    y: String,
}

fn hex_bytes(text: &str) -> Vec<u8> {
    let text = text.strip_prefix("0x").unwrap_or(text);
    let padded = if text.len().is_multiple_of(2) {
        text.to_string()
    } else {
        format!("0{text}")
    };
    hex::decode(padded).unwrap()
}

fn fit(bytes: &[u8], width: usize) -> Vec<u8> {
    assert!(bytes.len() <= width);
    let mut out = vec![0u8; width];
    out[width - bytes.len()..].copy_from_slice(bytes);
    out
}

type ExpandFn = fn(&[u8], &[u8], &mut [u8]) -> Result<(), ExpandError>;
type ElementsFn<const N: usize> = fn(&[u8], &[u8]) -> ([u8; N], [u8; N]);
type MapFn<const N: usize> = fn(&[u8]) -> ([u8; N], [u8; N]);

fn expand_cases(file: &str, expand: ExpandFn) {
    let parsed: ExpandFile = serde_json::from_str(file).unwrap();
    for case in parsed.tests {
        let len = usize::from_str_radix(case.len_in_bytes.trim_start_matches("0x"), 16).unwrap();
        let mut out = vec![0u8; len];
        expand(case.msg.as_bytes(), parsed.dst.as_bytes(), &mut out).unwrap();
        assert_eq!(out, hex_bytes(&case.uniform_bytes), "{}", case.msg);
    }
}

#[test]
fn expand_message_xmd_sha256() {
    expand_cases(
        include_str!("../testdata/expand_message_xmd_SHA256_38.json"),
        expand_sha256,
    );
}

#[test]
fn expand_message_xmd_sha256_long_dst() {
    // Appendix K.2: a tag longer than 255 bytes is hashed, as section 5.3.3
    // requires, rather than truncated or refused.
    expand_cases(
        include_str!("../testdata/expand_message_xmd_SHA256_256.json"),
        expand_sha256,
    );
}

#[test]
fn expand_message_xmd_sha512() {
    expand_cases(
        include_str!("../testdata/expand_message_xmd_SHA512_38.json"),
        expand_sha512,
    );
}

#[test]
fn expand_message_refuses_hostile_lengths() {
    let dst = b"dst-not-empty!!";
    assert_eq!(
        expand_sha256(b"", b"", &mut [0; 32]),
        Err(ExpandError::EmptyDst)
    );
    assert_eq!(
        expand_sha384(b"abc", b"", &mut [0; 48]),
        Err(ExpandError::EmptyDst)
    );
    assert_eq!(
        expand_sha512(b"abc", b"", &mut [0; 64]),
        Err(ExpandError::EmptyDst)
    );

    let mut too_wide = vec![0u8; 65536];
    assert_eq!(
        expand_sha256(b"m", dst, &mut too_wide),
        Err(ExpandError::OutputLength)
    );
    // 255 blocks are the last legal length. One more byte needs a 256th block.
    let mut last = vec![0u8; 255 * 32];
    assert!(expand_sha256(b"m", dst, &mut last).is_ok());
    let mut over_blocks = vec![0u8; 255 * 32 + 1];
    assert_eq!(
        expand_sha256(b"m", dst, &mut over_blocks),
        Err(ExpandError::OutputLength)
    );
    let mut sha512_over = vec![0u8; 255 * 64 + 1];
    assert_eq!(
        expand_sha512(b"m", dst, &mut sha512_over),
        Err(ExpandError::OutputLength)
    );

    // A zero length is the empty prefix of the RFC's output.
    assert!(expand_sha256(b"", dst, &mut []).is_ok());
    // An empty message is a real input. Appendix K starts with one.
    assert!(expand_sha384(b"", dst, &mut [0; 48]).is_ok());

    // A tag of 255 bytes is used as written. One more byte is hashed first.
    let mut at_limit = [0u8; 32];
    let mut over = [0u8; 32];
    let dst_255 = vec![b'Z'; 255];
    let dst_256 = vec![b'Z'; 256];
    expand_sha256(b"", &dst_255, &mut at_limit).unwrap();
    expand_sha256(b"", &dst_256, &mut over).unwrap();
    assert_ne!(at_limit, over);
    expand_sha384(b"abc", &dst_255, &mut [0; 48]).unwrap();
    expand_sha512(b"abc", &dst_256, &mut [0; 64]).unwrap();

    // `L` outside a suite is refused before any allocation.
    assert_eq!(
        super::expand_two::<0>(b"m", dst, expand_sha256),
        Err(ExpandError::OutputLength)
    );
    assert_eq!(
        super::expand_two::<129>(b"m", dst, expand_sha512),
        Err(ExpandError::OutputLength)
    );
}

#[test]
fn reduce_be_matches_schoolbook() {
    // 2^128 ≡ 1 (mod 5), so the one-limb montifier is 1. The input stays
    // below 2^64 * 5, which Montgomery reduction requires.
    assert_eq!(reduce_be(&[7], &[5u64], &[1]), [2]);
    assert_eq!(reduce_be(&[5], &[5], &[1]), [0]);
    assert_eq!(reduce_be(&[4], &[5], &[1]), [4]);
    assert_eq!(reduce_be(&[1, 0], &[5], &[1]), [1]);

    let p256 = [
        0xffff_ffff_ffff_ffff,
        0x0000_0000_ffff_ffff,
        0x0000_0000_0000_0000,
        0xffff_ffff_0000_0001,
    ];
    let r2 = [
        0x0000_0000_0000_0003,
        0xffff_fffb_ffff_ffff,
        0xffff_ffff_ffff_fffe,
        0x0000_0004_ffff_fffd,
    ];
    let be = |words: &[u64; 4]| -> Vec<u8> {
        let mut out = vec![0u8; 32];
        for (i, word) in words.iter().enumerate() {
            let at = out.len() - (i + 1) * 8;
            out[at..at + 8].copy_from_slice(&word.to_be_bytes());
        }
        out
    };
    assert_eq!(reduce_be(&be(&p256), &p256, &r2), [0; 4]);
    assert_eq!(reduce_be(&[1], &p256, &r2), [1, 0, 0, 0]);

    let wide = [0x5au8; 48];
    assert_eq!(reduce_be(&wide, &p256, &r2), school(&wide, &p256));

    // The modulus, one below it, one past it, and an all-ones input of length L.
    let modulus = be(&p256);
    assert_eq!(reduce_be(&modulus, &p256, &r2), [0; 4]);
    let mut below = modulus.clone();
    *below.last_mut().unwrap() -= 1;
    assert_ne!(reduce_be(&below, &p256, &r2), [0; 4]);
    assert_eq!(reduce_be(&below, &p256, &r2), school(&below, &p256));
    let mut past = vec![0x01];
    past.extend_from_slice(&modulus);
    assert_eq!(reduce_be(&past, &p256, &r2), school(&past, &p256));
    let ones = [0xffu8; 48];
    assert_eq!(reduce_be(&ones, &p256, &r2), school(&ones, &p256));
    check_modulus(&p256, &r2);
    check_modulus(
        &[
            0xf3b9_cac2_fc63_2551,
            0xbce6_faad_a717_9e84,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_0000_0000,
        ],
        &[
            0x8324_4c95_be79_eea2,
            0x4699_799c_49bd_6fa6,
            0x2845_b239_2b6b_ec59,
            0x66e1_2d94_f3d9_5620,
        ],
    );

    // P-384 and P-521, at the modulus, one below, and one past. The order is
    // the scalar modulus `hash_to_scalar` reduces by.
    check_modulus(
        &[
            0x0000_0000_ffff_ffff,
            0xffff_ffff_0000_0000,
            0xffff_ffff_ffff_fffe,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
        ],
        &[
            0xffff_fffe_0000_0001,
            0x0000_0002_0000_0000,
            0xffff_fffe_0000_0000,
            0x0000_0002_0000_0000,
            0x0000_0000_0000_0001,
            0x0000_0000_0000_0000,
        ],
    );
    check_modulus(
        &[
            0xecec_196a_ccc5_2973,
            0x581a_0db2_48b0_a77a,
            0xc763_4d81_f437_2ddf,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
        ],
        &[
            0x2d31_9b24_19b4_09a9,
            0xff3d_81e5_df1a_a419,
            0xbc3e_483a_fcb8_2947,
            0xd40d_4917_4aab_1cc5,
            0x3fb0_5b7a_2826_6895,
            0x0c84_ee01_2b39_bf21,
        ],
    );
    check_modulus(
        &[
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0x0000_0000_0000_01ff,
        ],
        &[
            0x0000_0000_0000_0000,
            0x0000_4000_0000_0000,
            0x0000_0000_0000_0000,
            0x0000_0000_0000_0000,
            0x0000_0000_0000_0000,
            0x0000_0000_0000_0000,
            0x0000_0000_0000_0000,
            0x0000_0000_0000_0000,
            0x0000_0000_0000_0000,
        ],
    );
    check_modulus(
        &[
            0xbb6f_b71e_9138_6409,
            0x3bb5_c9b8_899c_47ae,
            0x7fcc_0148_f709_a5d0,
            0x5186_8783_bf2f_966b,
            0xffff_ffff_ffff_fffa,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0x0000_0000_0000_01ff,
        ],
        &[
            0x137c_d04d_cf15_dd04,
            0xf707_badc_e554_7ea3,
            0x12a7_8d38_7945_73ff,
            0xd372_1ef5_57f7_5e06,
            0xdd6e_23d8_2e49_c7db,
            0xcff3_d142_b775_6e3e,
            0x5bcc_6d61_a8e5_67bc,
            0x2d8e_03d1_492d_0d45,
            0x0000_0000_0000_003d,
        ],
    );
}

/// `modulus`, one below it, and one past it, against schoolbook reduction.
fn check_modulus<const N: usize>(modulus: &[u64; N], r2: &[u64; N]) {
    let be = |words: &[u64; N]| -> Vec<u8> {
        let mut out = vec![0u8; N * 8];
        for (i, word) in words.iter().enumerate() {
            let at = out.len() - (i + 1) * 8;
            out[at..at + 8].copy_from_slice(&word.to_be_bytes());
        }
        out
    };
    let encoded = be(modulus);
    assert_eq!(reduce_be(&encoded, modulus, r2), [0; N]);
    let mut below = encoded.clone();
    decrement(&mut below);
    assert_eq!(reduce_be(&below, modulus, r2), school(&below, modulus));
    let mut past = encoded.clone();
    increment(&mut past);
    assert_eq!(reduce_be(&past, modulus, r2), school(&past, modulus));
    let mut one = [0u64; N];
    one[0] = 1;
    assert_eq!(reduce_be(&past, modulus, r2), one);
}

fn increment(bytes: &mut [u8]) {
    for byte in bytes.iter_mut().rev() {
        let (sum, carry) = byte.overflowing_add(1);
        *byte = sum;
        if !carry {
            return;
        }
    }
}

fn decrement(bytes: &mut [u8]) {
    for byte in bytes.iter_mut().rev() {
        let (diff, borrow) = byte.overflowing_sub(1);
        *byte = diff;
        if !borrow {
            return;
        }
    }
}

/// `bytes` reduced mod `modulus`, one bit at a time.
///
/// The accumulator keeps one extra limb: doubling a residue below the modulus
/// can set the bit just above it.
fn school<const N: usize>(bytes: &[u8], modulus: &[u64; N]) -> [u64; N] {
    fn double(x: &mut [u64]) {
        let mut carry = 0u64;
        for limb in x.iter_mut() {
            let next = *limb >> 63;
            *limb = (*limb << 1) | carry;
            carry = next;
        }
        assert_eq!(carry, 0);
    }
    fn add_bit(x: &mut [u64], bit: u64) {
        let mut carry = bit;
        for limb in x.iter_mut() {
            let (sum, c) = limb.overflowing_add(carry);
            *limb = sum;
            carry = u64::from(c);
        }
        assert_eq!(carry, 0);
    }
    fn ge(x: &[u64], y: &[u64]) -> bool {
        for (x, y) in x.iter().zip(y).rev() {
            if x != y {
                return x > y;
            }
        }
        true
    }
    fn sub(x: &mut [u64], y: &[u64]) {
        let mut borrow = false;
        for (x, y) in x.iter_mut().zip(y) {
            let (diff, b1) = x.overflowing_sub(*y);
            let (diff, b2) = diff.overflowing_sub(u64::from(borrow));
            *x = diff;
            borrow = b1 || b2;
        }
        assert!(!borrow);
    }

    let mut acc = vec![0u64; N + 1];
    let mut wide = vec![0u64; N + 1];
    wide[..N].copy_from_slice(modulus);
    for &byte in bytes {
        for bit in (0..8).rev() {
            double(&mut acc);
            add_bit(&mut acc, u64::from((byte >> bit) & 1));
            if ge(&acc, &wide) {
                sub(&mut acc, &wide);
            }
        }
    }
    acc[..N].try_into().unwrap()
}

fn suite<const N: usize>(
    file: &str,
    hash_elements: ElementsFn<N>,
    map: MapFn<N>,
    hash_point: fn(&[u8], &[u8]) -> Result<super::HashedPoint<N>, ExpandError>,
) {
    let parsed: SuiteFile = serde_json::from_str(file).unwrap();
    let dst = parsed.dst.as_bytes();
    for case in parsed.vectors {
        let msg = case.msg.as_bytes();
        let (u0, u1) = hash_elements(msg, dst);
        assert_eq!(u0, fit(&hex_bytes(&case.u[0]), N).as_slice(), "u0");
        assert_eq!(u1, fit(&hex_bytes(&case.u[1]), N).as_slice(), "u1");
        let (x, y) = map(&u0);
        assert_eq!(x, fit(&hex_bytes(&case.q0.x), N).as_slice(), "Q0.x");
        assert_eq!(y, fit(&hex_bytes(&case.q0.y), N).as_slice(), "Q0.y");
        let (x, y) = map(&u1);
        assert_eq!(x, fit(&hex_bytes(&case.q1.x), N).as_slice(), "Q1.x");
        assert_eq!(y, fit(&hex_bytes(&case.q1.y), N).as_slice(), "Q1.y");
        let point = hash_point(msg, dst).unwrap();
        assert_eq!(point.infinity, 0);
        assert_eq!(point.x, fit(&hex_bytes(&case.p.x), N).as_slice(), "P.x");
        assert_eq!(point.y, fit(&hex_bytes(&case.p.y), N).as_slice(), "P.y");
    }
}

#[test]
fn p256_suite_vectors() {
    suite(
        include_str!("../testdata/P256_XMD:SHA-256_SSWU_RO_.json"),
        p256::hash_elements,
        p256::map_field_element,
        p256::hash_to_curve,
    );
}

#[test]
fn p384_suite_vectors() {
    suite(
        include_str!("../testdata/P384_XMD:SHA-384_SSWU_RO_.json"),
        p384::hash_elements,
        p384::map_field_element,
        p384::hash_to_curve,
    );
}

#[test]
fn p521_suite_vectors() {
    suite(
        include_str!("../testdata/P521_XMD:SHA-512_SSWU_RO_.json"),
        p521::hash_elements,
        p521::map_field_element,
        p521::hash_to_curve,
    );
}

#[test]
fn hashed_point_debug_redacts_coordinates() {
    let point = p256::hash_to_curve(b"abc", b"dst-not-empty!!").unwrap();
    let text = format!("{point:?}");
    assert_eq!(text, "HashedPoint { .. }");
    assert!(!text.contains(&hex::encode(point.x)));
}

#[test]
fn hash_to_field_is_one_element_and_scalar_differs() {
    let dst = b"rind-hash-to-field-v1";
    let msg = b"";
    let field = p256::hash_to_field(msg, dst).unwrap();
    let scalar = p256::hash_to_scalar(msg, dst).unwrap().as_bytes();
    // count 1 is the first half of count 2 only when the lengths differ, so
    // these two reductions of different expand outputs are not the same bytes.
    assert_ne!(field, scalar);
    assert_eq!(p384::hash_to_field(msg, dst).unwrap().len(), 48);
    assert_eq!(p521::hash_to_field(msg, dst).unwrap().len(), 66);
    assert_eq!(p384::hash_to_scalar(msg, dst).unwrap().as_bytes().len(), 48);
    assert_eq!(p521::hash_to_scalar(msg, dst).unwrap().as_bytes().len(), 66);
}

fn ct_point<const N: usize>(hash: fn(&[u8], &[u8]) -> Result<super::HashedPoint<N>, ExpandError>) {
    let msg = [0x5au8; 80];
    secret_slice(&msg);
    let dst = b"rind-hash-to-curve-ct-v1";
    let first = into_public(hash(&msg, dst).unwrap());
    let second = into_public(hash(&msg, dst).unwrap());
    assert_eq!(first, second);
}

fn ct_scalar_bytes<const N: usize>(bytes: impl Fn(&[u8], &[u8]) -> [u8; N]) {
    let msg = [0xa5u8; 96];
    secret_slice(&msg);
    let dst = b"rind-hash-to-scalar-ct-v1";
    let first = into_public(bytes(&msg, dst));
    let second = into_public(bytes(&msg, dst));
    assert_eq!(first, second);
}

#[test]
fn ctgrind_maps_and_scalars() {
    ct_point(p256::hash_to_curve);
    ct_point(p384::hash_to_curve);
    ct_point(p521::hash_to_curve);
    ct_scalar_bytes(|msg, dst| p256::hash_to_field(msg, dst).unwrap());
    ct_scalar_bytes(|msg, dst| p384::hash_to_field(msg, dst).unwrap());
    ct_scalar_bytes(|msg, dst| p521::hash_to_field(msg, dst).unwrap());
    ct_scalar_bytes(|msg, dst| p256::hash_to_scalar(msg, dst).unwrap().as_bytes());
    ct_scalar_bytes(|msg, dst| p384::hash_to_scalar(msg, dst).unwrap().as_bytes());
    ct_scalar_bytes(|msg, dst| p521::hash_to_scalar(msg, dst).unwrap().as_bytes());
}

#[cfg(not(miri))]
#[allow(unsafe_code)]
mod differential {
    use elliptic_curve::sec1::ToSec1Point;
    use hash2curve::GroupDigest;

    use super::fit;
    use crate::mid::{p256, p384, p521};

    fn aws_point(
        nid: i32,
        hash: unsafe extern "C" fn(
            *const aws_lc_sys::EC_GROUP,
            *mut aws_lc_sys::EC_POINT,
            *const u8,
            usize,
            *const u8,
            usize,
        ) -> i32,
        msg: &[u8],
        dst: &[u8],
        out: &mut [u8],
    ) -> bool {
        // SAFETY: the group and point are freed here, the output buffer is
        // `out`, and a zero-length input is not read.
        unsafe {
            let group = aws_lc_sys::EC_GROUP_new_by_curve_name(nid);
            assert!(!group.is_null());
            let point = aws_lc_sys::EC_POINT_new(group);
            assert!(!point.is_null());
            let ok = hash(
                group,
                point,
                dst.as_ptr(),
                dst.len(),
                msg.as_ptr(),
                msg.len(),
            );
            if ok == 1 {
                let written = aws_lc_sys::EC_POINT_point2oct(
                    group,
                    point,
                    aws_lc_sys::point_conversion_form_t::POINT_CONVERSION_UNCOMPRESSED,
                    out.as_mut_ptr(),
                    out.len(),
                    core::ptr::null_mut(),
                );
                assert_eq!(written, out.len());
            }
            aws_lc_sys::EC_POINT_free(point);
            aws_lc_sys::EC_GROUP_free(group);
            ok == 1
        }
    }

    #[test]
    fn p256_and_p384_match_aws_lc() {
        let msgs: &[&[u8]] = &[
            b"",
            b"abc",
            b"password",
            &[0],
            &[0xff; 40],
            b"a longer message than one hash block, for the compression loop",
        ];
        let long_dst = vec![b'Z'; 300];
        let dsts: &[&[u8]] = &[b"QUUX-V01-CS02-with-P256_XMD:SHA-256_SSWU_RO_", &long_dst];
        for msg in msgs {
            for dst in dsts {
                let ours = p256::hash_to_curve(msg, dst).unwrap();
                let mut theirs = [0u8; 65];
                assert!(aws_point(
                    aws_lc_sys::NID_X9_62_prime256v1,
                    aws_lc_sys::EC_hash_to_curve_p256_xmd_sha256_sswu,
                    msg,
                    dst,
                    &mut theirs,
                ));
                assert_eq!(theirs[0], 0x04);
                assert_eq!(ours.infinity, 0);
                assert_eq!(ours.x, theirs[1..33]);
                assert_eq!(ours.y, theirs[33..65]);

                let ours = p384::hash_to_curve(msg, dst).unwrap();
                let mut theirs = [0u8; 97];
                assert!(aws_point(
                    aws_lc_sys::NID_secp384r1,
                    aws_lc_sys::EC_hash_to_curve_p384_xmd_sha384_sswu,
                    msg,
                    dst,
                    &mut theirs,
                ));
                assert_eq!(theirs[0], 0x04);
                assert_eq!(ours.infinity, 0);
                assert_eq!(ours.x, theirs[1..49]);
                assert_eq!(ours.y, theirs[49..97]);
            }
        }
        assert!(p256::hash_to_curve(b"m", b"").is_err());
        let mut ignored = [0u8; 65];
        assert!(!aws_point(
            aws_lc_sys::NID_X9_62_prime256v1,
            aws_lc_sys::EC_hash_to_curve_p256_xmd_sha256_sswu,
            b"m",
            b"",
            &mut ignored,
        ));
    }

    #[test]
    fn rustcrypto_p521() {
        use elliptic_curve::sec1::{Coordinates, ToSec1Point};
        use hash2curve::GroupDigest;

        let msgs: &[&[u8]] = &[b"", b"abc", b"password", &[0xff; 70]];
        let dsts: &[&[u8]] = &[
            b"QUUX-V01-CS02-with-P521_XMD:SHA-512_SSWU_RO_",
            b"another-domain-separation-tag",
        ];
        for msg in msgs {
            for dst in dsts {
                let ours = p521::hash_to_curve(msg, dst).unwrap();
                let theirs = ::p521::NistP521::hash_from_bytes(&[*msg], &[*dst]).unwrap();
                let encoded = theirs.to_affine().to_sec1_point(false);
                let Coordinates::Uncompressed { x, y } = encoded.coordinates() else {
                    panic!("uncompressed");
                };
                assert_eq!(ours.infinity, 0);
                assert_eq!(ours.x, fit(x, 66).as_slice());
                assert_eq!(ours.y, fit(y, 66).as_slice());
            }
        }
    }

    fn field_and_scalar(msg: &[u8], dst: &[u8]) {
        use hash2curve::{ExpandMsgXmd, MapToCurve};
        use sha2::{Sha256, Sha384, Sha512};

        let [fe] = hash2curve::hash_to_field::<
            1,
            ExpandMsgXmd<Sha256>,
            <::p256::NistP256 as MapToCurve>::SecurityLevel,
            <::p256::NistP256 as MapToCurve>::FieldElement,
            <::p256::NistP256 as MapToCurve>::Length,
        >(&[msg], &[dst])
        .unwrap();
        assert_eq!(
            p256::hash_to_field(msg, dst).unwrap().as_slice(),
            fe.to_bytes().as_slice()
        );
        let scalar = hash2curve::hash_to_scalar::<
            ::p256::NistP256,
            ExpandMsgXmd<Sha256>,
            <::p256::NistP256 as MapToCurve>::Length,
        >(&[msg], &[dst])
        .unwrap();
        assert_eq!(
            p256::hash_to_scalar(msg, dst)
                .unwrap()
                .as_bytes()
                .as_slice(),
            scalar.to_bytes().as_slice()
        );

        let [fe] = hash2curve::hash_to_field::<
            1,
            ExpandMsgXmd<Sha384>,
            <::p384::NistP384 as MapToCurve>::SecurityLevel,
            <::p384::NistP384 as MapToCurve>::FieldElement,
            <::p384::NistP384 as MapToCurve>::Length,
        >(&[msg], &[dst])
        .unwrap();
        assert_eq!(
            p384::hash_to_field(msg, dst).unwrap().as_slice(),
            fe.to_bytes().as_slice()
        );
        let scalar = hash2curve::hash_to_scalar::<
            ::p384::NistP384,
            ExpandMsgXmd<Sha384>,
            <::p384::NistP384 as MapToCurve>::Length,
        >(&[msg], &[dst])
        .unwrap();
        assert_eq!(
            p384::hash_to_scalar(msg, dst)
                .unwrap()
                .as_bytes()
                .as_slice(),
            scalar.to_bytes().as_slice()
        );

        let [fe] = hash2curve::hash_to_field::<
            1,
            ExpandMsgXmd<Sha512>,
            <::p521::NistP521 as MapToCurve>::SecurityLevel,
            <::p521::NistP521 as MapToCurve>::FieldElement,
            <::p521::NistP521 as MapToCurve>::Length,
        >(&[msg], &[dst])
        .unwrap();
        assert_eq!(
            p521::hash_to_field(msg, dst).unwrap().as_slice(),
            fe.to_bytes().as_slice()
        );
        let scalar = hash2curve::hash_to_scalar::<
            ::p521::NistP521,
            ExpandMsgXmd<Sha512>,
            <::p521::NistP521 as MapToCurve>::Length,
        >(&[msg], &[dst])
        .unwrap();
        assert_eq!(
            p521::hash_to_scalar(msg, dst)
                .unwrap()
                .as_bytes()
                .as_slice(),
            scalar.to_bytes().as_slice()
        );
    }

    /// RFC 9380 appendix K has no `expand_message_xmd` file for SHA-384.
    /// This compares the function with RustCrypto's SHA-384 expander, which is
    /// that algorithm. The P-384 suite vectors also run it.
    fn expand_sha384_matches(msg: &[u8], dst: &[u8], len: u16) {
        use core::num::NonZero;

        use hash2curve::{ExpandMsg, Expander, MapToCurve};

        let mut ours = vec![0u8; usize::from(len)];
        super::expand_sha384(msg, dst, &mut ours).unwrap();
        let msgs = [msg];
        let dsts = [dst];
        let mut expander = <hash2curve::ExpandMsgXmd<sha2::Sha384> as ExpandMsg<
            <::p384::NistP384 as MapToCurve>::SecurityLevel,
        >>::expand_message(&msgs, &dsts, NonZero::new(len).unwrap())
        .unwrap();
        let mut theirs = vec![0u8; usize::from(len)];
        expander.fill_bytes(&mut theirs).unwrap();
        assert_eq!(ours, theirs);
    }

    #[test]
    fn field_scalar_and_sha384_match_hash2curve() {
        let dst_255 = vec![b'D'; 255];
        let dst_256 = vec![b'D'; 256];
        for msg in [b"".as_slice(), b"abc", b"password", &[0xff; 40]] {
            for dst in [
                b"QUUX-V01-CS02".as_slice(),
                b"another-domain-separation-tag",
                dst_255.as_slice(),
                dst_256.as_slice(),
            ] {
                field_and_scalar(msg, dst);
                // One byte, one hash output, and one byte past it.
                expand_sha384_matches(msg, dst, 1);
                expand_sha384_matches(msg, dst, 48);
                expand_sha384_matches(msg, dst, 49);
            }
        }
    }

    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(8))]
        #[test]
        fn random_messages_match_hash2curve(
            msg in proptest::collection::vec(proptest::prelude::any::<u8>(), 0..80),
            dst in proptest::collection::vec(proptest::prelude::any::<u8>(), 1..48),
        ) {
            field_and_scalar(&msg, &dst);
            expand_sha384_matches(&msg, &dst, 48);
            let ours = p256::hash_to_curve(&msg, &dst).unwrap();
            let theirs = ::p256::NistP256::hash_from_bytes(&[&msg], &[&dst]).unwrap();
            let encoded = theirs.to_affine().to_sec1_point(false);
            let elliptic_curve::sec1::Coordinates::Uncompressed { x, y } = encoded.coordinates() else {
                panic!("uncompressed");
            };
            assert_eq!(ours.infinity, 0);
            assert_eq!(ours.x.as_slice(), x.as_slice());
            assert_eq!(ours.y.as_slice(), y.as_slice());
        }
    }
}
