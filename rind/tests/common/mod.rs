//! Helpers the crosschecks targets share.

/// A DER element of `tag` holding `body`.
pub fn der(tag: u8, body: &[u8]) -> Vec<u8> {
    let len = match body.len() {
        len @ 0..=0x7f => vec![len as u8],
        len @ 0x80..=0xff => vec![0x81, len as u8],
        len => [&[0x82][..], &u16::try_from(len).unwrap().to_be_bytes()].concat(),
    };
    [&[tag][..], &len, body].concat()
}
