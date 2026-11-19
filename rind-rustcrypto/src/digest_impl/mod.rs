//! `digest` 0.11's traits: hashes as `Digest`, HMAC as `Mac`.

// One wrapper type over rind's `digest::Context` for each hash. rind's context
// is `Clone`, so a clone forks the running hash as `Clone` promises, and it
// restarts itself after `finish`, which is what `FixedOutputReset` needs.
macro_rules! hash {
    ($($(#[$meta:meta])* $name:ident, $algorithm:ident, $output:ident, $block:ident;)*) => {$(
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
    hash! {
        /// SHA-256.
        Sha256, SHA256, U32, U64;
        /// SHA-384.
        Sha384, SHA384, U48, U128;
        /// SHA-512.
        Sha512, SHA512, U64, U128;
        /// SHA-512/256.
        Sha512_256, SHA512_256, U32, U128;
    }
}

/// The SHA-3 family, as `sha3` names its types.
pub mod sha3 {
    hash! {
        /// SHA3-256.
        Sha3_256, SHA3_256, U32, U136;
        /// SHA3-384.
        Sha3_384, SHA3_384, U48, U104;
        /// SHA3-512.
        Sha3_512, SHA3_512, U64, U72;
    }
}
