// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! Reading and writing the `OSSL_PARAM` arrays OpenSSL passes, as its
//! `params.c` does for the types this provider takes and gives.
//!
//! OpenSSL vouches for an array's shape: each parameter's data is valid for
//! its size, and a null key ends it. Its values are the caller's, and are
//! checked as hostile.

use core::ffi::{CStr, c_int};
use core::marker::PhantomData;
use core::slice;

use zeroize::Zeroizing;

use crate::ffi::{INTEGER, OCTET_STRING, Param, REAL, UNSIGNED_INTEGER, UTF8_PTR, UTF8_STRING};

/// A parameter array OpenSSL passes in, or none.
#[derive(Clone, Copy)]
pub(crate) struct Params<'a> {
    first: *const Param,
    _array: PhantomData<&'a Param>,
}

impl<'a> Params<'a> {
    /// # Safety
    ///
    /// `first` is null or the start of a parameter array valid for `'a`.
    pub(crate) unsafe fn new(first: *const Param) -> Self {
        Self {
            first,
            _array: PhantomData,
        }
    }

    /// The first parameter named `name`, as `OSSL_PARAM_locate_const` finds it.
    pub(crate) fn find(self, name: &CStr) -> Option<&'a Param> {
        // SAFETY: the array is valid for `'a`, per `new`.
        unsafe { locate(self.first, name).as_ref() }
    }
}

/// The first parameter named `name` in the array at `first`, or null.
///
/// # Safety
///
/// `first` is null or the start of a parameter array.
unsafe fn locate(first: *const Param, name: &CStr) -> *const Param {
    let mut at = first;
    while !at.is_null() {
        // SAFETY: `at` is in the array, which has not ended yet.
        let key = unsafe { (*at).key };
        if key.is_null() {
            break;
        }
        // SAFETY: a parameter's key is a C string.
        if unsafe { CStr::from_ptr(key) } == name {
            return at;
        }
        // SAFETY: the array goes on to its terminator.
        at = unsafe { at.add(1) };
    }
    core::ptr::null()
}

/// A parameter array OpenSSL passes for this provider to fill, or none.
pub(crate) struct ParamsMut<'a> {
    first: *mut Param,
    _array: PhantomData<&'a mut Param>,
}

impl<'a> ParamsMut<'a> {
    /// # Safety
    ///
    /// `first` is null or the start of a writable parameter array valid for
    /// `'a`.
    pub(crate) unsafe fn new(first: *mut Param) -> Self {
        Self {
            first,
            _array: PhantomData,
        }
    }

    /// The first parameter named `name`, as `OSSL_PARAM_locate` finds it.
    pub(crate) fn find(&mut self, name: &CStr) -> Option<&mut Param> {
        // SAFETY: the array is valid and writable for `'a`, per `new`, and
        // `self` holds the only access to it.
        unsafe { locate(self.first, name).cast_mut().as_mut() }
    }
}

impl Param {
    /// The bytes of an `OSSL_PARAM_OCTET_STRING`, refused as another type or
    /// without data, as `OSSL_PARAM_get_octet_string` does.
    pub(crate) fn octets(&self) -> Option<&[u8]> {
        if self.data_type != OCTET_STRING || self.data.is_null() {
            return None;
        }
        // SAFETY: a parameter's data is valid for its size.
        Some(unsafe { slice::from_raw_parts(self.data.cast::<u8>(), self.data_size) })
    }

    /// The bytes of an `OSSL_PARAM_UTF8_STRING` up to its first NUL, refused
    /// as another type or without data.
    pub(crate) fn utf8(&self) -> Option<&[u8]> {
        if self.data_type != UTF8_STRING || self.data.is_null() {
            return None;
        }
        // SAFETY: a parameter's data is valid for its size.
        let bytes = unsafe { slice::from_raw_parts(self.data.cast::<u8>(), self.data_size) };
        bytes.split(|&b| b == 0).next()
    }

    /// The value of an `OSSL_PARAM_INTEGER` of 1, 2, 4, or 8 bytes, as
    /// `OSSL_PARAM_get_int` reads it, refused if it does not fit a `c_int`.
    pub(crate) fn int(&self) -> Option<c_int> {
        if self.data_type != INTEGER || self.data.is_null() {
            return None;
        }
        // SAFETY: a parameter's data is valid for its size.
        let bytes = unsafe { slice::from_raw_parts(self.data.cast::<u8>(), self.data_size) };
        let value = match *bytes {
            [a] => i64::from(i8::from_ne_bytes([a])),
            [a, b] => i64::from(i16::from_ne_bytes([a, b])),
            [a, b, c, d] => i64::from(i32::from_ne_bytes([a, b, c, d])),
            [a, b, c, d, e, f, g, h] => i64::from_ne_bytes([a, b, c, d, e, f, g, h]),
            _ => return None,
        };
        c_int::try_from(value).ok()
    }

    /// The value of an `OSSL_PARAM_UNSIGNED_INTEGER` of any size, as
    /// `OSSL_PARAM_get_BN` reads it, in big-endian bytes of the parameter's
    /// size. The bytes may be a private key's, so they wipe themselves.
    pub(crate) fn unsigned_be(&self) -> Option<Zeroizing<Vec<u8>>> {
        if self.data_type != UNSIGNED_INTEGER || self.data.is_null() {
            return None;
        }
        // SAFETY: a parameter's data is valid for its size.
        let native = unsafe { slice::from_raw_parts(self.data.cast::<u8>(), self.data_size) };
        let mut value = Zeroizing::new(native.to_vec());
        if cfg!(target_endian = "little") {
            value.reverse();
        }
        Some(value)
    }

    /// Sets an `OSSL_PARAM_UNSIGNED_INTEGER` to the big-endian `value`: in the
    /// parameter's native byte order, padded with zeros to its size, refused
    /// if its size is smaller than `value`. A null `data` asks only the size.
    ///
    /// It keeps `value`'s length, rather than stripping its leading zeros as
    /// `OSSL_PARAM_set_BN` does, so that a private key's length is not a
    /// secret-dependent size the caller reads.
    pub(crate) fn set_unsigned_be(&mut self, value: &[u8]) -> bool {
        if self.data_type != UNSIGNED_INTEGER {
            self.return_size = 0;
            return false;
        }
        self.return_size = value.len();
        if self.data.is_null() {
            return true;
        }
        if self.data_size < value.len() {
            return false;
        }
        let size = self.data_size;
        let data = self.data.cast::<u8>();
        for k in 0..size {
            // The k-th least significant byte.
            let byte = match value.len().checked_sub(1 + k) {
                Some(at) => value[at],
                None => 0,
            };
            let at = match cfg!(target_endian = "little") {
                true => k,
                false => size - 1 - k,
            };
            // SAFETY: a parameter's data is valid for its size, and `at` is
            // below it.
            unsafe { data.add(at).write(byte) };
        }
        true
    }

    /// Sets a `size_t` parameter, as `OSSL_PARAM_set_size_t` does: a null
    /// `data` asks for the size of a `size_t`, not of an `int`. `value` is
    /// small, as a digest's length is.
    pub(crate) fn set_size(&mut self, value: usize) -> bool {
        if self.data_type == UNSIGNED_INTEGER && self.data.is_null() {
            self.return_size = size_of::<usize>();
            return true;
        }
        match c_int::try_from(value) {
            Ok(value) => self.set_int(value),
            Err(_) => false,
        }
    }

    /// Sets an integer or real parameter of any size that holds `value`,
    /// as `OSSL_PARAM_set_int` does; a null `data` asks only the size.
    pub(crate) fn set_int(&mut self, value: c_int) -> bool {
        self.return_size = 0;
        let wide = i64::from(value);
        match self.data_type {
            INTEGER => {}
            UNSIGNED_INTEGER if value >= 0 => {}
            REAL => {
                self.return_size = size_of::<f64>();
                if self.data.is_null() {
                    return true;
                }
                if self.data_size != size_of::<f64>() {
                    return false;
                }
                // SAFETY: the data is valid for its size, a double's, and
                // OpenSSL aligns real data for it. A double holds every
                // `c_int` exactly.
                unsafe { self.data.cast::<f64>().write(wide as f64) };
                return true;
            }
            _ => return false,
        }
        self.return_size = size_of::<c_int>();
        if self.data.is_null() {
            return true;
        }
        // The value in `data_size` native-endian bytes, sign-extended or
        // truncated, refused unless the truncated bytes are all sign and
        // what is left keeps the sign, as `params.c`'s `copy_integer` does.
        let size = self.data_size;
        let fits = match size {
            0 => false,
            8.. => true,
            _ if self.data_type == INTEGER => {
                let half = 1i64 << (8 * size - 1);
                (-half..half).contains(&wide)
            }
            _ => wide < 1i64 << (8 * size),
        };
        if !fits {
            return false;
        }
        let le = wide.to_le_bytes();
        let pad = if value < 0 { 0xff } else { 0 };
        let data = self.data.cast::<u8>();
        for k in 0..size {
            let byte = le.get(k).copied().unwrap_or(pad);
            let at = match cfg!(target_endian = "little") {
                true => k,
                false => size - 1 - k,
            };
            // SAFETY: a parameter's data is valid for its size, and `at` is
            // below it.
            unsafe { data.add(at).write(byte) };
        }
        self.return_size = size;
        true
    }

    /// Sets an `OSSL_PARAM_OCTET_STRING`, as `OSSL_PARAM_set_octet_string`
    /// does; a null `data` asks only the size.
    pub(crate) fn set_octets(&mut self, value: &[u8]) -> bool {
        self.set_string(value, OCTET_STRING)
    }

    /// Sets an `OSSL_PARAM_UTF8_STRING`, NUL-terminated if it fits, as
    /// `OSSL_PARAM_set_utf8_string` does.
    pub(crate) fn set_utf8(&mut self, value: &CStr) -> bool {
        self.set_string(value.to_bytes(), UTF8_STRING)
    }

    fn set_string(&mut self, value: &[u8], data_type: u32) -> bool {
        if self.data_type != data_type {
            self.return_size = 0;
            return false;
        }
        self.return_size = value.len();
        if self.data.is_null() {
            return true;
        }
        if self.data_size < value.len() {
            return false;
        }
        // SAFETY: a parameter's data is valid for its size, which holds
        // `value`, and is the caller's own buffer, apart from `value`.
        unsafe {
            core::ptr::copy_nonoverlapping(value.as_ptr(), self.data.cast::<u8>(), value.len());
            if data_type == UTF8_STRING && self.data_size > value.len() {
                self.data.cast::<u8>().add(value.len()).write(0);
            }
        }
        true
    }

    /// Points an `OSSL_PARAM_UTF8_PTR` at `value`, as
    /// `OSSL_PARAM_set_utf8_ptr` does.
    pub(crate) fn set_utf8_ptr(&mut self, value: &'static CStr) -> bool {
        if self.data_type != UTF8_PTR {
            self.return_size = 0;
            return false;
        }
        self.return_size = value.to_bytes().len();
        if !self.data.is_null() {
            // SAFETY: a `UTF8_PTR` parameter's data holds a pointer, which
            // OpenSSL aligns.
            unsafe {
                self.data
                    .cast::<*const core::ffi::c_char>()
                    .write(value.as_ptr())
            };
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use core::ffi::c_void;

    use super::*;

    fn param(key: &'static CStr, data_type: u32, data: *mut c_void, data_size: usize) -> Param {
        Param {
            key: key.as_ptr(),
            data_type,
            data,
            data_size,
            return_size: crate::ffi::UNMODIFIED,
        }
    }

    #[test]
    fn find_takes_the_first_match() {
        let mut first = [1u8];
        let mut second = [2u8];
        let params = [
            param(c"pub", OCTET_STRING, first.as_mut_ptr().cast(), 1),
            param(c"pub", OCTET_STRING, second.as_mut_ptr().cast(), 1),
            Param::END,
        ];
        // SAFETY: the array is terminated and outlives its use.
        let params = unsafe { Params::new(params.as_ptr()) };
        assert_eq!(params.find(c"pub").unwrap().octets(), Some(&[1u8][..]));
        assert!(params.find(c"priv").is_none());
        // SAFETY: a null array is none.
        let none = unsafe { Params::new(core::ptr::null()) };
        assert!(none.find(c"pub").is_none());
    }

    #[test]
    fn reads_refuse_another_type() {
        let mut data = *b"x25519\0junk";
        let utf8 = param(c"group", UTF8_STRING, data.as_mut_ptr().cast(), data.len());
        assert_eq!(utf8.utf8(), Some(&b"x25519"[..]));
        assert_eq!(utf8.octets(), None);
        let missing = param(c"pub", OCTET_STRING, core::ptr::null_mut(), 0);
        assert_eq!(missing.octets(), None);
    }

    #[test]
    fn set_int_converts_as_openssl_does() {
        let mut four = 0i32;
        let mut p = param(c"bits", INTEGER, (&raw mut four).cast(), 4);
        assert!(p.set_int(253));
        assert_eq!((four, p.return_size), (253, 4));

        let mut eight = 0u64;
        let mut p = param(c"bits", UNSIGNED_INTEGER, (&raw mut eight).cast(), 8);
        assert!(p.set_int(253));
        assert_eq!((eight, p.return_size), (253, 8));
        assert!(!p.set_int(-1));
        assert_eq!(p.return_size, 0);

        // Any size that holds the value, sign-extended past eight bytes.
        let mut two = 0i16;
        let mut p = param(c"bits", INTEGER, (&raw mut two).cast(), 2);
        assert!(p.set_int(253));
        assert_eq!((two, p.return_size), (253, 2));
        assert!(p.set_int(-32768));
        assert_eq!(two, -32768);
        assert!(!p.set_int(32768));
        let mut sixteen = [0u8; 16];
        let mut p = param(c"bits", INTEGER, sixteen.as_mut_ptr().cast(), 16);
        assert!(p.set_int(-2));
        assert_eq!(i128::from_ne_bytes(sixteen), -2);
        let mut one = 0u8;
        let mut p = param(c"bits", UNSIGNED_INTEGER, (&raw mut one).cast(), 1);
        assert!(p.set_int(255));
        assert_eq!(one, 255);
        assert!(!p.set_int(256));
        let mut p = param(c"bits", INTEGER, (&raw mut one).cast(), 1);
        assert!(!p.set_int(128));
        let mut p = param(c"bits", INTEGER, (&raw mut one).cast(), 0);
        assert!(!p.set_int(0));

        let mut real = 0f64;
        let mut p = param(c"bits", REAL, (&raw mut real).cast(), 8);
        assert!(p.set_int(253));
        assert_eq!((real, p.return_size), (253.0, 8));

        let mut p = param(c"bits", OCTET_STRING, (&raw mut four).cast(), 4);
        assert!(!p.set_int(1));
        let mut p = param(c"bits", OCTET_STRING, core::ptr::null_mut(), 0);
        assert!(!p.set_int(1));
        assert_eq!(p.return_size, 0);
    }

    #[test]
    fn set_string_refuses_another_type_before_its_size() {
        let mut p = param(c"pub", UTF8_STRING, core::ptr::null_mut(), 0);
        assert!(!p.set_octets(&[7; 32]));
        assert_eq!(p.return_size, 0);
    }

    #[test]
    fn set_octets_asks_size_then_fills() {
        let mut p = param(c"pub", OCTET_STRING, core::ptr::null_mut(), 0);
        assert!(p.set_octets(&[7; 32]));
        assert_eq!(p.return_size, 32);

        let mut short = [0u8; 31];
        let mut p = param(c"pub", OCTET_STRING, short.as_mut_ptr().cast(), 31);
        assert!(!p.set_octets(&[7; 32]));

        let mut buf = [0u8; 40];
        let mut p = param(c"pub", OCTET_STRING, buf.as_mut_ptr().cast(), 40);
        assert!(p.set_octets(&[7; 32]));
        assert_eq!(p.return_size, 32);
        assert_eq!((&buf[..32], buf[32]), (&[7; 32][..], 0));
    }

    #[test]
    fn set_utf8_terminates_when_it_fits() {
        let mut buf = [0xffu8; 4];
        let mut p = param(c"mandatory-digest", UTF8_STRING, buf.as_mut_ptr().cast(), 4);
        assert!(p.set_utf8(c""));
        assert_eq!((buf[0], p.return_size), (0, 0));
    }

    #[test]
    fn unsigned_integers_keep_their_length_and_native_order() {
        // A value with leading zeros keeps them, into a buffer of its size.
        let value = [0, 0, 1, 2, 3];
        let mut buf = [0xffu8; 5];
        let mut p = param(c"priv", UNSIGNED_INTEGER, buf.as_mut_ptr().cast(), 5);
        assert!(p.set_unsigned_be(&value));
        assert_eq!(p.return_size, 5);
        let mut expected = value;
        if cfg!(target_endian = "little") {
            expected.reverse();
        }
        assert_eq!(buf, expected);
        assert_eq!(&p.unsigned_be().unwrap()[..], &value[..]);

        // A larger buffer pads, a smaller one refuses, a null one asks.
        let mut big = [0xffu8; 8];
        let mut p = param(c"priv", UNSIGNED_INTEGER, big.as_mut_ptr().cast(), 8);
        assert!(p.set_unsigned_be(&value));
        assert_eq!(&p.unsigned_be().unwrap()[..], &[0, 0, 0, 0, 0, 1, 2, 3][..]);
        let mut small = [0u8; 4];
        let mut p = param(c"priv", UNSIGNED_INTEGER, small.as_mut_ptr().cast(), 4);
        assert!(!p.set_unsigned_be(&value));
        let mut p = param(c"priv", UNSIGNED_INTEGER, core::ptr::null_mut(), 0);
        assert!(p.set_unsigned_be(&value));
        assert_eq!(p.return_size, 5);
        let mut p = param(c"priv", OCTET_STRING, big.as_mut_ptr().cast(), 8);
        assert!(!p.set_unsigned_be(&value));
        assert!(p.unsigned_be().is_none());
    }

    #[test]
    fn int_reads_each_size() {
        let mut four = -7i32;
        let p = param(c"mode", INTEGER, (&raw mut four).cast(), 4);
        assert_eq!(p.int(), Some(-7));
        let mut eight = 1i64 << 40;
        let p = param(c"mode", INTEGER, (&raw mut eight).cast(), 8);
        assert_eq!(p.int(), None);
        let mut unsigned = 1u32;
        let p = param(c"mode", UNSIGNED_INTEGER, (&raw mut unsigned).cast(), 4);
        assert_eq!(p.int(), None);
    }
}
