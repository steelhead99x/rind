//! `digest` 0.11's traits on rind: SHA-2 and SHA-3 as `Digest`, HMAC as `Mac`.
//!
//! Each module keeps the path, names, and re-exports of the RustCrypto crate it
//! stands in for (`sha2`, `sha3`, `hmac`), so code written against those runs
//! on rind by naming a different crate. Every type is a thin wrapper that calls
//! rind; nothing here is a primitive or an encoding. The README lists what rind
//! cannot back.
#![no_std]

// One wrapper type over rind's `digest::Context` for each hash. rind's context
// is `Clone`, so a clone forks the running hash as `Clone` promises, and it
// restarts itself after `finish`, which is what `FixedOutputReset` needs.
macro_rules! hash {
    ($($(#[$meta:meta])* $name:ident, $algorithm:ident, $output:ident, $block:ident, $alg_name:literal, $oid:literal;)*) => {$(
        $(#[$meta])*
        #[derive(Clone)]
        pub struct $name {
            context: ::rind::digest::Context,
        }

        impl Default for $name {
            fn default() -> Self {
                Self { context: ::rind::digest::Context::new(&::rind::digest::$algorithm) }
            }
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                f.write_str(concat!(stringify!($name), " { .. }"))
            }
        }

        impl ::digest::HashMarker for $name {}

        // Named as RustCrypto's type names itself.
        impl ::digest::common::AlgorithmName for $name {
            fn write_alg_name(f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                f.write_str($alg_name)
            }
        }

        #[cfg(feature = "oid")]
        impl ::digest::const_oid::AssociatedOid for $name {
            const OID: ::digest::const_oid::ObjectIdentifier =
                ::digest::const_oid::ObjectIdentifier::new_unwrap($oid);
        }

        impl ::digest::OutputSizeUser for $name {
            type OutputSize = ::digest::consts::$output;
        }

        impl ::digest::common::BlockSizeUser for $name {
            type BlockSize = ::digest::consts::$block;
        }

        impl ::digest::Update for $name {
            fn update(&mut self, data: &[u8]) {
                self.context.update(data);
            }
        }

        impl ::digest::FixedOutput for $name {
            fn finalize_into(mut self, out: &mut ::digest::Output<Self>) {
                out.copy_from_slice(self.context.finish().as_ref());
            }
        }

        impl ::digest::Reset for $name {
            fn reset(&mut self) {
                *self = Self::default();
            }
        }

        impl ::digest::FixedOutputReset for $name {
            fn finalize_into_reset(&mut self, out: &mut ::digest::Output<Self>) {
                out.copy_from_slice(self.context.finish().as_ref());
            }
        }
    )*};
}

pub mod hmac;

/// The SHA-2 family, as `sha2` names its types.
pub mod sha2 {
    pub use digest::{self, Digest};

    hash! {
        /// SHA-256.
        Sha256, SHA256, U32, U64, "Sha256_32", "2.16.840.1.101.3.4.2.1";
        /// SHA-384.
        Sha384, SHA384, U48, U128, "Sha512_48", "2.16.840.1.101.3.4.2.2";
        /// SHA-512.
        Sha512, SHA512, U64, U128, "Sha512_64", "2.16.840.1.101.3.4.2.3";
        /// SHA-512/256.
        Sha512_256, SHA512_256, U32, U128, "Sha512_32", "2.16.840.1.101.3.4.2.6";
    }
}

/// The SHA-3 family, as `sha3` names its types.
pub mod sha3 {
    pub use digest::{self, Digest};

    hash! {
        /// SHA3-256.
        Sha3_256, SHA3_256, U32, U136, "Sha3_256", "2.16.840.1.101.3.4.2.8";
        /// SHA3-384.
        Sha3_384, SHA3_384, U48, U104, "Sha3_384", "2.16.840.1.101.3.4.2.9";
        /// SHA3-512.
        Sha3_512, SHA3_512, U64, U72, "Sha3_512", "2.16.840.1.101.3.4.2.10";
    }
}
