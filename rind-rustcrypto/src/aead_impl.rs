//! `aead` 0.6's traits: AES-GCM and ChaCha20-Poly1305 as `Aead` and
//! `AeadInOut`, with the 12-byte nonce and 16-byte tag RustCrypto's aliases fix.

// One wrapper over rind's `aead::Key`, which holds the expanded key and wipes
// it on drop. The wrapper copies no key bytes: `KeyInit::new` hands the slice
// it is given straight to rind.
macro_rules! aead {
    ($($(#[$meta:meta])* $name:ident, $algorithm:ident, $key:ident;)*) => {$(
        $(#[$meta])*
        pub struct $name {
            key: ::rind::aead::Key,
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                f.write_str(concat!(stringify!($name), " { .. }"))
            }
        }

        impl ::aead::common::KeySizeUser for $name {
            type KeySize = ::aead::consts::$key;
        }

        impl ::aead::KeyInit for $name {
            fn new(key: &::aead::Key<Self>) -> Self {
                let key = ::rind::aead::Key::new(&::rind::aead::$algorithm, key.as_slice())
                    .expect("the key type has the algorithm's key length");
                Self { key }
            }
        }

        impl ::aead::AeadCore for $name {
            type NonceSize = ::aead::consts::U12;
            type TagSize = ::aead::consts::U16;
            const TAG_POSITION: ::aead::TagPosition = ::aead::TagPosition::Postfix;
        }

        impl ::aead::AeadInOut for $name {
            fn encrypt_inout_detached(
                &self,
                nonce: &::aead::Nonce<Self>,
                associated_data: &[u8],
                buffer: ::aead::inout::InOutBuf<'_, '_, u8>,
            ) -> ::aead::Result<::aead::Tag<Self>> {
                // rind seals in place, so the plaintext moves to the output
                // first when the two buffers differ.
                let in_out = buffer.into_out_with_copied_in();
                let nonce = ::rind::aead::Nonce::assume_unique_for_key((*nonce).into());
                let tag = self
                    .key
                    .seal_in_place_separate_tag(nonce, associated_data, in_out)
                    .map_err(|_| ::aead::Error)?;
                ::aead::Tag::<Self>::try_from(tag.as_ref()).map_err(|_| ::aead::Error)
            }

            fn decrypt_inout_detached(
                &self,
                nonce: &::aead::Nonce<Self>,
                associated_data: &[u8],
                buffer: ::aead::inout::InOutBuf<'_, '_, u8>,
                tag: &::aead::Tag<Self>,
            ) -> ::aead::Result<()> {
                let in_out = buffer.into_out_with_copied_in();
                let nonce = ::rind::aead::Nonce::assume_unique_for_key((*nonce).into());
                let tag = ::rind::aead::Tag::try_from(tag.as_slice()).map_err(|_| ::aead::Error)?;
                self.key
                    .open_in_place_separate_tag(nonce, associated_data, tag, in_out)
                    .map(|_| ())
                    .map_err(|_| ::aead::Error)
            }
        }
    )*};
}

/// AES-GCM with a 12-byte nonce and a 16-byte tag, as `aes_gcm` names its
/// aliases. Other nonce and tag lengths, and AES-192 (which `aes_gcm` offers
/// only as `AesGcm<Aes192, U12>`), are not offered.
pub mod aes_gcm {
    aead! {
        /// AES-128-GCM.
        Aes128Gcm, AES_128_GCM, U16;
        /// AES-256-GCM.
        Aes256Gcm, AES_256_GCM, U32;
    }
}

/// ChaCha20-Poly1305 (RFC 8439), as `chacha20poly1305` names it.
pub mod chacha20poly1305 {
    aead! {
        /// ChaCha20-Poly1305 with a 12-byte nonce.
        ChaCha20Poly1305, CHACHA20_POLY1305, U32;
    }
}
