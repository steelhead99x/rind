//! rind-ring's DER reader against ring's, which callers import directly.

// ring does not build for wasm.
#![cfg(not(target_family = "wasm"))]

use proptest::collection::vec;
use proptest::prelude::*;
use rind_ring::io::der as ours;
use ring::io::der as theirs;

/// Each side's tags, in the same order.
const TAGS: [(ours::Tag, theirs::Tag); 13] = [
    (ours::Tag::Boolean, theirs::Tag::Boolean),
    (ours::Tag::Integer, theirs::Tag::Integer),
    (ours::Tag::BitString, theirs::Tag::BitString),
    (ours::Tag::OctetString, theirs::Tag::OctetString),
    (ours::Tag::Null, theirs::Tag::Null),
    (ours::Tag::OID, theirs::Tag::OID),
    (ours::Tag::Sequence, theirs::Tag::Sequence),
    (ours::Tag::UTCTime, theirs::Tag::UTCTime),
    (ours::Tag::GeneralizedTime, theirs::Tag::GeneralizedTime),
    (ours::Tag::ContextSpecific1, theirs::Tag::ContextSpecific1),
    (
        ours::Tag::ContextSpecificConstructed0,
        theirs::Tag::ContextSpecificConstructed0,
    ),
    (
        ours::Tag::ContextSpecificConstructed1,
        theirs::Tag::ContextSpecificConstructed1,
    ),
    (
        ours::Tag::ContextSpecificConstructed3,
        theirs::Tag::ContextSpecificConstructed3,
    ),
];

#[test]
fn tags_match_ring() {
    assert_eq!(ours::CONSTRUCTED, theirs::CONSTRUCTED);
    assert_eq!(ours::CONTEXT_SPECIFIC, theirs::CONTEXT_SPECIFIC);
    for (i, (a, b)) in TAGS.into_iter().enumerate() {
        assert_eq!(a.into(), b.into());
        assert_eq!(u8::from(a), u8::from(b));
        assert_eq!(usize::from(a), usize::from(b));
        for (j, (c, _)) in TAGS.into_iter().enumerate() {
            assert_eq!(a == c, i == j);
        }
    }
}

/// Runs `read` on `input` and returns its result, with the bytes read as
/// slices, and the bytes it left unread.
fn run<'a, T>(
    input: &'a [u8],
    read: impl FnOnce(&mut untrusted::Reader<'a>) -> T,
) -> (T, &'a [u8]) {
    let mut reader = untrusted::Reader::new(untrusted::Input::from(input));
    let result = read(&mut reader);
    (result, reader.read_bytes_to_end().as_slice_less_safe())
}

fn slice(input: Option<untrusted::Input<'_>>) -> Option<&[u8]> {
    input.map(|i| i.as_slice_less_safe())
}

/// DER-like input: a tag, a length in any of the forms ring weighs, and
/// contents that may be shorter or longer than it says.
fn element() -> impl Strategy<Value = Vec<u8>> {
    (
        prop_oneof![any::<u8>(), Just(0x02), Just(0x03), Just(0x30), Just(0x1f)],
        prop_oneof![
            (0u16..0x80).prop_map(|len| vec![len as u8]),
            any::<u8>().prop_map(|len| vec![0x81, len]),
            any::<u16>().prop_map(|len| [&[0x82][..], &len.to_be_bytes()].concat()),
            (0x83u8..=0xff).prop_map(|first| vec![first, 0, 1]),
        ],
        vec(any::<u8>(), 0..300),
    )
        .prop_map(|(tag, len, body)| [&[tag][..], &len, &body].concat())
}

/// An `INTEGER` of a few bytes, which the integer readers weigh.
fn integer() -> impl Strategy<Value = Vec<u8>> {
    prop_oneof![
        vec(any::<u8>(), 0..4),
        vec(
            prop_oneof![Just(0u8), Just(0x7f), Just(0x80), Just(0xff), any::<u8>()],
            0..4
        ),
    ]
    .prop_map(|value| [&[0x02, value.len() as u8][..], &value].concat())
}

/// Each reader reads `input` as upstream's does.
fn same(input: &[u8]) -> Result<(), TestCaseError> {
    prop_assert_eq!(
        run(input, |r| ours::read_tag_and_get_value(r)
            .ok()
            .map(|(t, v)| (t, v.as_slice_less_safe()))),
        run(input, |r| theirs::read_tag_and_get_value(r)
            .ok()
            .map(|(t, v)| (t, v.as_slice_less_safe()))),
    );
    for (a, b) in TAGS {
        prop_assert_eq!(
            run(input, |r| slice(ours::expect_tag_and_get_value(r, a).ok())),
            run(input, |r| slice(
                theirs::expect_tag_and_get_value(r, b).ok()
            )),
        );
        prop_assert_eq!(
            run(input, |r| ours::nested(r, a, 1, |r| Ok(r
                .read_bytes_to_end()
                .as_slice_less_safe()))),
            run(input, |r| theirs::nested(r, b, 1, |r| Ok(r
                .read_bytes_to_end()
                .as_slice_less_safe()))),
        );
    }
    prop_assert_eq!(
        run(input, |r| slice(
            ours::bit_string_with_no_unused_bits(r).ok()
        )),
        run(input, |r| slice(
            theirs::bit_string_with_no_unused_bits(r).ok()
        )),
    );
    prop_assert_eq!(
        run(input, |r| ours::small_nonnegative_integer(r).ok()),
        run(input, |r| theirs::small_nonnegative_integer(r).ok()),
    );
    prop_assert_eq!(
        run(input, |r| ours::positive_integer(r).ok().map(|p| (
            p.big_endian_without_leading_zero(),
            p.first_byte()
        ))),
        run(input, |r| theirs::positive_integer(r).ok().map(|p| (
            p.big_endian_without_leading_zero(),
            p.first_byte()
        ))),
    );
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4096))]

    #[test]
    fn reads_as_ring(input in prop_oneof![element(), integer(), vec(any::<u8>(), 0..8)]) {
        same(&input)?;
    }
}

/// The edges random input may miss: each length form at its bounds, and
/// integers empty, negative, or with a needless leading zero.
#[test]
fn edges() {
    let body = [0x5a; 0x1_0001];
    let mut inputs = Vec::new();
    for (len, header) in [
        (0x7f, vec![0x7f]),
        (0x7f, vec![0x81, 0x7f]),
        (0x80, vec![0x81, 0x80]),
        (0xff, vec![0x81, 0xff]),
        (0xff, vec![0x82, 0x00, 0xff]),
        (0x100, vec![0x82, 0x01, 0x00]),
        (0xffff, vec![0x82, 0xff, 0xff]),
        (0x1_0000, vec![0x83, 0x01, 0x00, 0x00]),
    ] {
        for tag in [0x02, 0x03, 0x04, 0x30] {
            // Whole, a byte short, and a byte over.
            for extra in [0, 1] {
                inputs.push([&[tag][..], &header, &body[..len + extra]].concat());
            }
            inputs.push([&[tag][..], &header, &body[..len - 1]].concat());
        }
    }
    for value in [
        &[][..],
        &[0x00],
        &[0x01],
        &[0x7f],
        &[0x80],
        &[0xff],
        &[0x00, 0x00],
        &[0x00, 0x7f],
        &[0x00, 0x80],
        &[0xff, 0x80],
        &[0x01, 0x00],
    ] {
        inputs.push([&[0x02, value.len() as u8][..], value].concat());
    }
    for input in inputs {
        same(&input).unwrap();
    }
}
