//! ring's DER reader: tags and lengths up to two bytes, minimally encoded,
//! and nonnegative integers without a needless leading zero.

use super::Positive;
use crate::error;

/// The bit a constructed element's tag sets.
pub const CONSTRUCTED: u8 = 1 << 5;
/// The class bits of a context-specific element's tag.
pub const CONTEXT_SPECIFIC: u8 = 2 << 6;

/// The tags ring reads.
#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Tag {
    /// `BOOLEAN`.
    Boolean = 0x01,
    /// `INTEGER`.
    Integer = 0x02,
    /// `BIT STRING`.
    BitString = 0x03,
    /// `OCTET STRING`.
    OctetString = 0x04,
    /// `NULL`.
    Null = 0x05,
    /// `OBJECT IDENTIFIER`.
    OID = 0x06,
    /// `SEQUENCE`.
    Sequence = CONSTRUCTED | 0x10,
    /// `UTCTime`.
    UTCTime = 0x17,
    /// `GeneralizedTime`.
    GeneralizedTime = 0x18,
    /// `[1] IMPLICIT`, primitive.
    ContextSpecific1 = CONTEXT_SPECIFIC | 1,
    /// `[0]`, constructed.
    ContextSpecificConstructed0 = CONTEXT_SPECIFIC | CONSTRUCTED,
    /// `[1]`, constructed.
    ContextSpecificConstructed1 = CONTEXT_SPECIFIC | CONSTRUCTED | 1,
    /// `[3]`, constructed.
    ContextSpecificConstructed3 = CONTEXT_SPECIFIC | CONSTRUCTED | 3,
}

impl From<Tag> for usize {
    fn from(tag: Tag) -> Self {
        Self::from(tag.into())
    }
}

impl From<Tag> for u8 {
    fn from(tag: Tag) -> Self {
        tag.into()
    }
}

impl Tag {
    /// The tag's byte, as `u8::from` gives it but usable in a `const`.
    pub const fn into(self) -> u8 {
        self as u8
    }
}

/// Reads an element tagged `tag` and returns its contents.
pub fn expect_tag_and_get_value<'a>(
    input: &mut untrusted::Reader<'a>,
    tag: Tag,
) -> Result<untrusted::Input<'a>, error::Unspecified> {
    match read_tag_and_get_value(input)? {
        (actual, value) if actual == tag.into() => Ok(value),
        _ => Err(error::Unspecified),
    }
}

/// Reads an element and returns its tag and contents, refusing a
/// high-number tag and a length that takes over two bytes or is not
/// minimally encoded.
pub fn read_tag_and_get_value<'a>(
    input: &mut untrusted::Reader<'a>,
) -> Result<(u8, untrusted::Input<'a>), error::Unspecified> {
    let tag = input.read_byte()?;
    if tag & 0x1f == 0x1f {
        return Err(error::Unspecified);
    }
    let len = match input.read_byte()? {
        len @ 0..=0x7f => usize::from(len),
        0x81 => match input.read_byte()? {
            len @ 0x80..=0xff => usize::from(len),
            _ => return Err(error::Unspecified),
        },
        0x82 => match u16::from_be_bytes([input.read_byte()?, input.read_byte()?]) {
            len @ 0x100..=0xffff => usize::from(len),
            _ => return Err(error::Unspecified),
        },
        _ => return Err(error::Unspecified),
    };
    Ok((tag, input.read_bytes(len)?))
}

/// Reads a `BIT STRING` whose bits fill its last byte and returns them.
pub fn bit_string_with_no_unused_bits<'a>(
    input: &mut untrusted::Reader<'a>,
) -> Result<untrusted::Input<'a>, error::Unspecified> {
    nested(
        input,
        Tag::BitString,
        error::Unspecified,
        |value| match value.read_byte()? {
            0 => Ok(value.read_bytes_to_end()),
            _ => Err(error::Unspecified),
        },
    )
}

/// Reads an element tagged `tag` and decodes all of its contents with
/// `decoder`, failing with `error` if either fails.
pub fn nested<'a, F, R, E: Copy>(
    input: &mut untrusted::Reader<'a>,
    tag: Tag,
    error: E,
    decoder: F,
) -> Result<R, E>
where
    F: FnOnce(&mut untrusted::Reader<'a>) -> Result<R, E>,
{
    expect_tag_and_get_value(input, tag)
        .map_err(|_| error)?
        .read_all(error, decoder)
}

/// Reads a nonnegative `INTEGER`, returning its big-endian bytes without
/// the zero byte DER puts before a top bit that is set. Zero is `[0]`.
pub(crate) fn nonnegative_integer<'a>(
    input: &mut untrusted::Reader<'a>,
) -> Result<untrusted::Input<'a>, error::Unspecified> {
    let value = expect_tag_and_get_value(input, Tag::Integer)?;
    let bytes = value.as_slice_less_safe();
    match bytes {
        [0] | [0x01..=0x7f, ..] => Ok(value),
        [0, 0x80..=0xff, ..] => Ok(untrusted::Input::from(&bytes[1..])),
        _ => Err(error::Unspecified),
    }
}

/// Reads an `INTEGER` from 0 to 255, such as a version number.
pub fn small_nonnegative_integer(
    input: &mut untrusted::Reader<'_>,
) -> Result<u8, error::Unspecified> {
    match nonnegative_integer(input)?.as_slice_less_safe() {
        [value] => Ok(*value),
        _ => Err(error::Unspecified),
    }
}

/// Reads a positive `INTEGER`, returning it without DER's sign byte.
pub fn positive_integer<'a>(
    input: &mut untrusted::Reader<'a>,
) -> Result<Positive<'a>, error::Unspecified> {
    match nonnegative_integer(input)?.as_slice_less_safe() {
        [0] => Err(error::Unspecified),
        value => Ok(Positive(untrusted::Input::from(value))),
    }
}
