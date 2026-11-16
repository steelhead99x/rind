//! PKCS#8 private key documents.

use alloc::vec::Vec;

use crate::wipe::Wiped;

/// A PKCS#8 private key document, wiped on drop.
pub struct Document(Wiped<Vec<u8>>);

impl Document {
    pub(crate) fn new(der: &[u8]) -> Self {
        Self(Wiped::new(der.to_vec()))
    }
}

impl AsRef<[u8]> for Document {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}
