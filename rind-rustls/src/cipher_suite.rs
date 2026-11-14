use rustls::crypto::tls12::PrfUsingHmac;
use rustls::crypto::tls13::HkdfUsingHmac;
use rustls::crypto::{CipherSuiteCommon, KeyExchangeAlgorithm};
use rustls::{
    CipherSuite, SignatureScheme, SupportedCipherSuite, Tls12CipherSuite, Tls13CipherSuite,
};

use super::{aead, hash, hmac, quic};

/// The TLS1.3 `TLS_AES_256_GCM_SHA384` cipher suite.
pub static TLS13_AES_256_GCM_SHA384: SupportedCipherSuite =
    SupportedCipherSuite::Tls13(&Tls13CipherSuite {
        common: CipherSuiteCommon {
            suite: CipherSuite::TLS13_AES_256_GCM_SHA384,
            hash_provider: &hash::SHA384,
            confidentiality_limit: 1 << 24,
        },
        hkdf_provider: &HkdfUsingHmac(&hmac::SHA384),
        aead_alg: &aead::AES_256_GCM,
        quic: Some(&quic::AES_256_GCM),
    });

/// The TLS1.3 `TLS_AES_128_GCM_SHA256` cipher suite.
pub static TLS13_AES_128_GCM_SHA256: SupportedCipherSuite =
    SupportedCipherSuite::Tls13(&Tls13CipherSuite {
        common: CipherSuiteCommon {
            suite: CipherSuite::TLS13_AES_128_GCM_SHA256,
            hash_provider: &hash::SHA256,
            confidentiality_limit: 1 << 24,
        },
        hkdf_provider: &HkdfUsingHmac(&hmac::SHA256),
        aead_alg: &aead::AES_128_GCM,
        quic: Some(&quic::AES_128_GCM),
    });

/// The TLS1.3 `TLS_CHACHA20_POLY1305_SHA256` cipher suite.
pub static TLS13_CHACHA20_POLY1305_SHA256: SupportedCipherSuite =
    SupportedCipherSuite::Tls13(&Tls13CipherSuite {
        common: CipherSuiteCommon {
            suite: CipherSuite::TLS13_CHACHA20_POLY1305_SHA256,
            hash_provider: &hash::SHA256,
            confidentiality_limit: u64::MAX,
        },
        hkdf_provider: &HkdfUsingHmac(&hmac::SHA256),
        aead_alg: &aead::Chacha20Poly1305,
        quic: Some(&quic::CHACHA20_POLY1305),
    });

/// The TLS1.2 `TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256` cipher suite.
pub static TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256: SupportedCipherSuite =
    SupportedCipherSuite::Tls12(&Tls12CipherSuite {
        common: CipherSuiteCommon {
            suite: CipherSuite::TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256,
            hash_provider: &hash::SHA256,
            confidentiality_limit: u64::MAX,
        },
        kx: rustls::crypto::KeyExchangeAlgorithm::ECDHE,
        sign: TLS12_RSA_SCHEMES,
        aead_alg: &aead::Chacha20Poly1305,
        prf_provider: &PrfUsingHmac(&hmac::SHA256),
    });

/// The TLS1.2 `TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256` cipher suite.
pub static TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256: SupportedCipherSuite =
    SupportedCipherSuite::Tls12(&Tls12CipherSuite {
        common: CipherSuiteCommon {
            suite: CipherSuite::TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256,
            hash_provider: &hash::SHA256,
            confidentiality_limit: u64::MAX,
        },
        kx: KeyExchangeAlgorithm::ECDHE,
        sign: TLS12_ECDSA_SCHEMES,
        aead_alg: &aead::Chacha20Poly1305,
        prf_provider: &PrfUsingHmac(&hmac::SHA256),
    });

/// The TLS1.2 `TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256` cipher suite.
pub static TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256: SupportedCipherSuite =
    SupportedCipherSuite::Tls12(&Tls12CipherSuite {
        common: CipherSuiteCommon {
            suite: CipherSuite::TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
            hash_provider: &hash::SHA256,
            confidentiality_limit: 1 << 24,
        },
        kx: KeyExchangeAlgorithm::ECDHE,
        sign: TLS12_RSA_SCHEMES,
        aead_alg: &aead::AES_128_GCM,
        prf_provider: &PrfUsingHmac(&hmac::SHA256),
    });

/// The TLS1.2 `TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384` cipher suite.
pub static TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384: SupportedCipherSuite =
    SupportedCipherSuite::Tls12(&Tls12CipherSuite {
        common: CipherSuiteCommon {
            suite: CipherSuite::TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
            hash_provider: &hash::SHA384,
            confidentiality_limit: 1 << 24,
        },
        kx: KeyExchangeAlgorithm::ECDHE,
        sign: TLS12_RSA_SCHEMES,
        aead_alg: &aead::AES_256_GCM,
        prf_provider: &PrfUsingHmac(&hmac::SHA384),
    });

/// The TLS1.2 `TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256` cipher suite.
pub static TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256: SupportedCipherSuite =
    SupportedCipherSuite::Tls12(&Tls12CipherSuite {
        common: CipherSuiteCommon {
            suite: CipherSuite::TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
            hash_provider: &hash::SHA256,
            confidentiality_limit: 1 << 24,
        },
        kx: KeyExchangeAlgorithm::ECDHE,
        sign: TLS12_ECDSA_SCHEMES,
        aead_alg: &aead::AES_128_GCM,
        prf_provider: &PrfUsingHmac(&hmac::SHA256),
    });

/// The TLS1.2 `TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384` cipher suite.
pub static TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384: SupportedCipherSuite =
    SupportedCipherSuite::Tls12(&Tls12CipherSuite {
        common: CipherSuiteCommon {
            suite: CipherSuite::TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
            hash_provider: &hash::SHA384,
            confidentiality_limit: 1 << 24,
        },
        kx: KeyExchangeAlgorithm::ECDHE,
        sign: TLS12_ECDSA_SCHEMES,
        aead_alg: &aead::AES_256_GCM,
        prf_provider: &PrfUsingHmac(&hmac::SHA384),
    });

static TLS12_ECDSA_SCHEMES: &[SignatureScheme] = &[
    SignatureScheme::ED25519,
    SignatureScheme::ECDSA_NISTP521_SHA512,
    SignatureScheme::ECDSA_NISTP384_SHA384,
    SignatureScheme::ECDSA_NISTP256_SHA256,
];

static TLS12_RSA_SCHEMES: &[SignatureScheme] = &[
    SignatureScheme::RSA_PSS_SHA512,
    SignatureScheme::RSA_PSS_SHA384,
    SignatureScheme::RSA_PSS_SHA256,
    SignatureScheme::RSA_PKCS1_SHA512,
    SignatureScheme::RSA_PKCS1_SHA384,
    SignatureScheme::RSA_PKCS1_SHA256,
];

#[cfg(test)]
mod tests {
    use rustls::SupportedCipherSuite;

    use super::{
        TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
        TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256, TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
        TLS13_AES_128_GCM_SHA256, TLS13_AES_256_GCM_SHA384,
    };

    #[test]
    fn aes_gcm_confidentiality_limit_is_two_to_the_24() {
        // `1 << 24` mutated to `1 >> 24` is zero, which also stalls a handshake.
        // The value is the one rustls's aws-lc-rs provider uses for AES-GCM.
        for suite in [
            TLS13_AES_128_GCM_SHA256,
            TLS13_AES_256_GCM_SHA384,
            TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
            TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
            TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
            TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
        ] {
            let limit = match suite {
                SupportedCipherSuite::Tls12(suite) => suite.common.confidentiality_limit,
                SupportedCipherSuite::Tls13(suite) => suite.common.confidentiality_limit,
            };
            assert_eq!(limit, 1 << 24);
        }
    }
}
