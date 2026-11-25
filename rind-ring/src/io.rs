//! ring's DER reader and the positive integer it reads, which callers such
//! as webpki import directly.

#[doc(hidden)]
pub mod der;

/// A big-endian positive integer, without leading zero bytes.
#[derive(Copy, Clone)]
pub struct Positive<'a>(untrusted::Input<'a>);

impl<'a> Positive<'a> {
    /// The integer's big-endian bytes, never empty and without leading zero bytes.
    pub fn big_endian_without_leading_zero(&self) -> &'a [u8] {
        self.0.as_slice_less_safe()
    }
}

impl Positive<'_> {
    /// The integer's first byte, which is never zero.
    pub fn first_byte(&self) -> u8 {
        self.0.as_slice_less_safe()[0]
    }
}
