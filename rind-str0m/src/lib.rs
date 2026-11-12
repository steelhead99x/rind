//! <h1 align="center">rind-str0m</h1>
//! <img width="40%" align="right" src="https://raw.githubusercontent.com/moq-dev/rind/main/admin/logo.png">
//!
//! This crate provides a [`CryptoProvider`] for [str0m](https://github.com/algesten/str0m), backed by [rind](https://github.com/moq-dev/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
//!
//! Build str0m with `default-features = false`, since its default features compile aws-lc-rs.
//! Then hand the provider to each connection:
//!
//! ```rust
//! use std::sync::Arc;
//! use std::time::Instant;
//!
//! let provider = rind_str0m::default_provider();
//! let rtc = str0m::Rtc::builder()
//!     .set_crypto_provider(Arc::new(provider))
//!     .build(Instant::now());
//! # let _ = rtc;
//! ```
//!
//! Or install it for the process with [`CryptoProvider::install_process_default`].

use str0m::crypto::CryptoProvider;

mod dtls;
mod hash;
mod srtp;

/// Returns a str0m [`CryptoProvider`] backed by rind.
///
/// It protects SRTP with AES-128-CM-HMAC-SHA1-80, AEAD-AES-128-GCM, and
/// AEAD-AES-256-GCM, signs STUN with HMAC-SHA1, hashes certificate
/// fingerprints with SHA-1 and SHA-256, and runs DTLS 1.2 and 1.3 through
/// dimpl on rind-dimpl with a self-signed ECDSA P-256 certificate.
///
/// An empty certificate or a private key rind-dimpl cannot load is an error.
/// str0m-aws-lc-rs passes those straight to dimpl, which panics.
pub fn default_provider() -> CryptoProvider {
    CryptoProvider {
        srtp_provider: &srtp::SRTP,
        sha1_hmac_provider: &hash::SHA1_HMAC,
        sha1_provider: &hash::SHA1,
        sha256_provider: &hash::SHA256,
        dtls_provider: &dtls::DTLS,
    }
}

/// Returns the rind-dimpl [`dimpl::crypto::CryptoProvider`] this crate's DTLS uses.
///
/// Callers who build their own `dimpl::Config` use it the way
/// `str0m_aws_lc_rs::dimpl_crypto_provider` exposes dimpl's aws-lc-rs provider.
pub fn dimpl_crypto_provider() -> dimpl::crypto::CryptoProvider {
    rind_dimpl::default_provider()
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use str0m::crypto::CryptoError;
    use str0m::crypto::dtls::{DtlsCert, DtlsVersion};

    #[test]
    fn dimpl_provider_builds_config() {
        dimpl::Config::builder()
            .with_crypto_provider(super::dimpl_crypto_provider())
            .build()
            .expect("rind-dimpl's provider builds a config");
    }

    #[test]
    fn empty_certificate_and_bad_key_are_errors() {
        let provider = super::default_provider();
        let now = Instant::now();
        let empty = DtlsCert {
            certificate: Vec::new(),
            private_key: vec![1, 2, 3],
        };
        let err = provider
            .dtls_provider
            .new_dtls(&empty, now, DtlsVersion::Dtls13, None)
            .unwrap_err();
        match err {
            CryptoError::Other(message) => assert!(message.contains("empty"), "{message}"),
            other => panic!("empty certificate should be an error, got {other:?}"),
        }

        let bad = DtlsCert {
            certificate: vec![0x30],
            private_key: vec![1, 2, 3],
        };
        assert!(matches!(
            provider
                .dtls_provider
                .new_dtls(&bad, now, DtlsVersion::Dtls13, None)
                .unwrap_err(),
            CryptoError::Other(_)
        ));
    }
}
