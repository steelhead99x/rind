//! <h1 align="center">rind-object-store</h1>
//! <img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">
//!
//! This crate provides a [`CryptoProvider`] for [object_store](https://github.com/apache/arrow-rs-object-store), backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
//! It signs S3, Azure, and GCS requests.
//!
//! Build object_store with its `aws-base`, `azure-base`, or `gcp-base` features rather than `aws`, `azure`, or `gcp`, which also compile aws-lc-rs.
//! Then hand the provider to each store's builder:
//!
//! ```rust,no_run
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let store = object_store::gcp::GoogleCloudStorageBuilder::new()
//!     .with_bucket_name("bucket")
//!     .with_crypto_provider(rind_object_store::default_provider())
//!     .build()?;
//! # Ok(())
//! # }
//! ```

use std::sync::Arc;

use object_store::client::{
    CryptoProvider, DigestAlgorithm, DigestContext, HmacContext, Signer, SigningAlgorithm,
};
use object_store::{Error, Result};
use rind::signature::{RsaKeyPair, sign};
use rind::{digest, hmac};
use rustls_pki_types::PrivateKeyDer;
use rustls_pki_types::pem::PemObject;

// Names the provider, as object_store's own providers do in this field.
const STORE: &str = "RindCryptoProvider";

/// Returns an object_store [`CryptoProvider`] backed by rind.
pub fn default_provider() -> Arc<dyn CryptoProvider> {
    Arc::new(Provider)
}

#[derive(Debug)]
struct Provider;

impl CryptoProvider for Provider {
    fn digest(&self, algorithm: DigestAlgorithm) -> Result<Box<dyn DigestContext>> {
        match algorithm {
            DigestAlgorithm::Sha256 => Ok(Box::new(Context::new(digest::Context::new(
                &digest::SHA256,
            )))),
            other => Err(unsupported(other)),
        }
    }

    fn hmac(&self, algorithm: DigestAlgorithm, secret: &[u8]) -> Result<Box<dyn HmacContext>> {
        match algorithm {
            DigestAlgorithm::Sha256 => Ok(Box::new(Context::new(hmac::Context::with_key(
                &hmac::Key::new(&hmac::HMAC_SHA256, secret),
            )))),
            other => Err(unsupported(other)),
        }
    }

    fn sign(&self, algorithm: SigningAlgorithm, pem: &[u8]) -> Result<Box<dyn Signer>> {
        match algorithm {
            SigningAlgorithm::RS256 => Ok(Box::new(Rs256(rsa_key_from_pem(pem)?))),
            other => Err(unsupported(other)),
        }
    }
}

/// A running digest or HMAC, plus storage for the output `finish` lends out.
struct Context<T, O> {
    state: T,
    output: Option<O>,
}

impl<T, O> Context<T, O> {
    fn new(state: T) -> Self {
        Self {
            state,
            output: None,
        }
    }
}

// object_store leaves use after `finish` to the provider. Finishing a clone
// keeps every call defined (a running hash) without a panic path.
impl DigestContext for Context<digest::Context, digest::Digest> {
    fn update(&mut self, data: &[u8]) {
        self.state.update(data);
    }

    fn finish(&mut self) -> Result<&[u8]> {
        let output: &digest::Digest = self.output.insert(self.state.clone().finish());
        Ok(output.as_ref())
    }
}

impl HmacContext for Context<hmac::Context, hmac::Tag> {
    fn update(&mut self, data: &[u8]) {
        self.state.update(data);
    }

    fn finish(&mut self) -> Result<&[u8]> {
        let output: &hmac::Tag = self.output.insert(self.state.clone().sign());
        Ok(output.as_ref())
    }
}

/// An RSA key that signs with RSASSA-PKCS1-v1_5 and SHA-256.
struct Rs256(RsaKeyPair);

impl Signer for Rs256 {
    fn sign(&self, message: &[u8]) -> Result<Vec<u8>> {
        let signature = self
            .0
            .sign(&sign::RSA_PKCS1_SHA256, message)
            .map_err(|err| generic(format!("RSA signing failed: {err}")))?;
        Ok(signature.as_ref().to_vec())
    }
}

/// Parses the first private key in `pem`, which must be RSA in PKCS#8 or PKCS#1 form.
fn rsa_key_from_pem(pem: &[u8]) -> Result<RsaKeyPair> {
    let key = match PrivateKeyDer::from_pem_slice(pem) {
        Ok(PrivateKeyDer::Pkcs8(key)) => RsaKeyPair::from_pkcs8(key.secret_pkcs8_der()),
        Ok(PrivateKeyDer::Pkcs1(key)) => RsaKeyPair::from_pkcs1(key.secret_pkcs1_der()),
        Ok(_) => return Err(generic("no RSA private key in PEM".into())),
        Err(err) => return Err(generic(format!("invalid PEM: {err}"))),
    };
    key.map_err(|err| generic(format!("invalid RSA private key: {err}")))
}

fn generic(message: String) -> Error {
    Error::Generic {
        store: STORE,
        source: message.into(),
    }
}

fn unsupported(algorithm: impl core::fmt::Debug) -> Error {
    Error::NotSupported {
        source: format!("rind does not support {algorithm:?}").into(),
    }
}
