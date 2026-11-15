//! The byte buffer behind each serialized form, as aws-lc-rs has it.

use alloc::borrow::Cow;
use alloc::vec::Vec;
use core::fmt;
use core::marker::PhantomData;

use zeroize::Zeroize;

/// Bytes exposed by an encoding. `T` tells the encodings apart, and says
/// whether they hold a private key, wiped on drop when owned under the `wipe`
/// feature.
// `T` is unbounded, as in aws-lc-rs, so its impls carry no bounds either;
// whether to wipe is fixed at construction instead.
pub struct Buffer<'a, T>(Cow<'a, [u8]>, bool, PhantomData<T>);

/// Whether an encoding holds a private key.
pub trait Kind {
    /// Whether the encoding holds a private key, which is wiped on drop under
    /// the `wipe` feature.
    const SECRET: bool;
}

impl<T: Kind> Buffer<'_, T> {
    pub(crate) fn new(owned: Vec<u8>) -> Self {
        Buffer(Cow::Owned(owned), T::SECRET, PhantomData)
    }
}

impl<T> Drop for Buffer<'_, T> {
    fn drop(&mut self) {
        // `cfg!` keeps the wipe type-checked in every build.
        if let (true, Cow::Owned(bytes)) = (cfg!(feature = "wipe") && self.1, &mut self.0) {
            bytes.zeroize();
        }
    }
}

impl<T> fmt::Debug for Buffer<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Buffer(...)")
    }
}

impl<T> AsRef<[u8]> for Buffer<'_, T> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

/// Declares serialized forms, each a [`Buffer`] of its own type, and whether
/// it holds a private key.
macro_rules! generated_encodings {
    ($(($name:ident, $name_type:ident, $secret:literal)),* $(,)?) => {
        mod buffer_type {
            $(
                pub struct $name_type {
                    _priv: (),
                }

                impl $crate::buffer::Kind for $name_type {
                    const SECRET: bool = $secret;
                }
            )*
        }
        $(
            /// Serialized bytes.
            pub struct $name<'a>($crate::buffer::Buffer<'a, buffer_type::$name_type>);

            impl<'a> core::ops::Deref for $name<'a> {
                type Target = $crate::buffer::Buffer<'a, buffer_type::$name_type>;

                fn deref(&self) -> &Self::Target {
                    &self.0
                }
            }

            impl $name<'static> {
                #[allow(dead_code)]
                pub(crate) fn new(owned: alloc::vec::Vec<u8>) -> Self {
                    Self($crate::buffer::Buffer::new(owned))
                }
            }

            impl core::fmt::Debug for $name<'_> {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    f.debug_struct(stringify!($name)).finish()
                }
            }

            impl<'a> From<$crate::buffer::Buffer<'a, buffer_type::$name_type>> for $name<'a> {
                fn from(value: $crate::buffer::Buffer<'a, buffer_type::$name_type>) -> Self {
                    Self(value)
                }
            }
        )*
    };
}
pub(crate) use generated_encodings;
