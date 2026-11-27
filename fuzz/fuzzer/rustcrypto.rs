//! RustCrypto's AES, the AES modes' independent oracle, as TESTING.md's
//! primitives table names it.

/// Runs `$body` with `$aes` naming RustCrypto's AES type for the size of
/// `$key`: 16, 24, or 32 bytes.
macro_rules! rustcrypto_aes {
    ($key:expr, $aes:ident => $body:expr) => {
        match $key.len() {
            16 => {
                type $aes = ::aes::Aes128;
                $body
            }
            24 => {
                type $aes = ::aes::Aes192;
                $body
            }
            _ => {
                type $aes = ::aes::Aes256;
                $body
            }
        }
    };
}

pub(crate) use rustcrypto_aes;
