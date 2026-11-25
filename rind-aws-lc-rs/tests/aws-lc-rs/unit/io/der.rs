// Copyright 2015 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::error;
use aws_lc_rs::io::Positive;
use aws_lc_rs::io::der::*;
use untrusted::Input;

fn with_good_i<F, R>(value: &[u8], f: F)
where
    F: FnOnce(&mut untrusted::Reader) -> Result<R, error::Unspecified>,
{
    let r = Input::from(value).read_all(error::Unspecified, f);
    assert!(r.is_ok());
}

fn with_bad_i<F, R>(value: &[u8], f: F)
where
    F: FnOnce(&mut untrusted::Reader) -> Result<R, error::Unspecified>,
{
    let r = Input::from(value).read_all(error::Unspecified, f);
    assert!(r.is_err());
}

static ZERO_INTEGER: &[u8] = &[0x02, 0x01, 0x00];

static GOOD_POSITIVE_INTEGERS: &[(&[u8], u8)] = &[
    (&[0x02, 0x01, 0x01], 0x01),
    (&[0x02, 0x01, 0x02], 0x02),
    (&[0x02, 0x01, 0x7e], 0x7e),
    (&[0x02, 0x01, 0x7f], 0x7f),
    // Values that need to have an 0x00 prefix to disambiguate them from
    // them from negative values.
    (&[0x02, 0x02, 0x00, 0x80], 0x80),
    (&[0x02, 0x02, 0x00, 0x81], 0x81),
    (&[0x02, 0x02, 0x00, 0xfe], 0xfe),
    (&[0x02, 0x02, 0x00, 0xff], 0xff),
];

#[allow(clippy::type_complexity)]
static GOOD_BIG_POSITIVE_INTEGERS: &[((&[u8], &[u8]), (&[u8], &[u8]))] = &[
    ((&[0x02, 0x81, 129u8, 1], &[0; 128]), (&[1], &[0; 128])),
    ((&[0x02, 0x82, 0x01, 0x00, 1], &[0; 255]), (&[1], &[0; 255])),
];

static BAD_NONNEGATIVE_INTEGERS: &[&[u8]] = &[
    &[],           // At end of input
    &[0x02],       // Tag only
    &[0x02, 0x00], // Empty value
    // Length mismatch
    &[0x02, 0x00, 0x01],
    &[0x02, 0x01],
    &[0x02, 0x01, 0x00, 0x01],
    &[0x02, 0x01, 0x01, 0x00], // Would be valid if last byte is ignored.
    &[0x02, 0x02, 0x01],
    // Negative values
    &[0x02, 0x01, 0x80],
    &[0x02, 0x01, 0xfe],
    &[0x02, 0x01, 0xff],
    // Values that have an unnecessary leading 0x00
    &[0x02, 0x02, 0x00, 0x00],
    &[0x02, 0x02, 0x00, 0x01],
    &[0x02, 0x02, 0x00, 0x02],
    &[0x02, 0x02, 0x00, 0x7e],
    &[0x02, 0x02, 0x00, 0x7f],
];

#[test]
fn test_small_nonnegative_integer() {
    with_good_i(ZERO_INTEGER, |input| {
        assert_eq!(small_nonnegative_integer(input)?, 0x00);
        Ok(())
    });
    for &(test_in, test_out) in GOOD_POSITIVE_INTEGERS {
        with_good_i(test_in, |input| {
            assert_eq!(small_nonnegative_integer(input)?, test_out);
            Ok(())
        });
    }
    for &test_in in BAD_NONNEGATIVE_INTEGERS {
        with_bad_i(test_in, |input| {
            let _: u8 = small_nonnegative_integer(input)?;
            Ok(())
        });
    }
}

#[test]
fn test_positive_integer() {
    with_bad_i(ZERO_INTEGER, |input| {
        let _: Positive<'_> = positive_integer(input)?;
        Ok(())
    });
    for &(test_in, test_out) in GOOD_POSITIVE_INTEGERS {
        with_good_i(test_in, |input| {
            let test_out = [test_out];
            assert_eq!(
                positive_integer(input)?
                    // rind-aws-lc-rs: the public counterpart of the private
                    // `big_endian_without_leading_zero_as_input`.
                    .big_endian_without_leading_zero(),
                Input::from(&test_out[..]).as_slice_less_safe()
            );
            Ok(())
        });
    }
    for &test_in in BAD_NONNEGATIVE_INTEGERS {
        with_bad_i(test_in, |input| {
            let _: Positive<'_> = positive_integer(input)?;
            Ok(())
        });
    }
}

#[test]
fn test_tag() {
    let tgt = usize::from(Tag::GeneralizedTime);
    assert_eq!(0x18usize, tgt);

    let tgt = u8::from(Tag::GeneralizedTime);
    assert_eq!(0x18u8, tgt);

    let tgt = Tag::GeneralizedTime;
    assert_eq!(tgt, Tag::GeneralizedTime);
}

#[test]
fn test_big() {
    for &((bytes_in_a, bytes_in_b), (bytes_out_a, bytes_out_b)) in GOOD_BIG_POSITIVE_INTEGERS {
        let mut bytes_in = Vec::new();
        bytes_in.extend(bytes_in_a);
        bytes_in.extend(bytes_in_b);
        let mut bytes_out: Vec<u8> = Vec::new();
        bytes_out.extend(bytes_out_a);
        bytes_out.extend(bytes_out_b);

        with_good_i(&bytes_in, |input| {
            let positive = positive_integer(input)?;
            let expected_bytes = positive.big_endian_without_leading_zero();
            assert_eq!(expected_bytes, &bytes_out);
            Ok(())
        });
    }
}

#[test]
fn test_bit_string_with_no_unused_bits() {
    // Not a BitString
    let mut reader_bad = untrusted::Reader::new(Input::from(&[0x02, 0x01]));
    assert!(bit_string_with_no_unused_bits(&mut reader_bad).is_err());
    // Unused bits at end
    let mut reader_bad2 = untrusted::Reader::new(Input::from(&[0x03, 0x01, 0x01]));
    assert!(bit_string_with_no_unused_bits(&mut reader_bad2).is_err());

    let mut reader_good = untrusted::Reader::new(Input::from(&[0x03, 0x01, 0x00]));
    let input = bit_string_with_no_unused_bits(&mut reader_good).unwrap();
    let expected_result: &[u8] = &[];
    assert_eq!(expected_result, input.as_slice_less_safe());
}
