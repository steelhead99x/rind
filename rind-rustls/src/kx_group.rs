use crypto::SupportedKxGroup;
use rind::agreement;
#[cfg(feature = "fips")]
use rind_fips::agreement as module;
use rustls::crypto;
use rustls::ffdhe_groups::FfdheGroup;

mod hybrid;
mod mlkem;

/// Key exchange with X25519.
pub static X25519: &dyn SupportedKxGroup = &KxGroup {
    name: rustls::NamedGroup::X25519,
    algorithm: &agreement::X25519,
};

/// Key exchange with ECDH on P-256, also known as secp256r1.
#[cfg(not(feature = "fips"))]
pub static SECP256R1: &dyn SupportedKxGroup = &KxGroup {
    name: rustls::NamedGroup::secp256r1,
    algorithm: &agreement::ECDH_P256,
};

/// Key exchange with ECDH on P-384, also known as secp384r1.
#[cfg(not(feature = "fips"))]
pub static SECP384R1: &dyn SupportedKxGroup = &KxGroup {
    name: rustls::NamedGroup::secp384r1,
    algorithm: &agreement::ECDH_P384,
};

/// Key exchange with ECDH on P-256, also known as secp256r1, in the module.
#[cfg(feature = "fips")]
pub static SECP256R1: &dyn SupportedKxGroup = &ModuleKxGroup {
    name: rustls::NamedGroup::secp256r1,
    algorithm: &module::ECDH_P256,
};

/// Key exchange with ECDH on P-384, also known as secp384r1, in the module.
#[cfg(feature = "fips")]
pub static SECP384R1: &dyn SupportedKxGroup = &ModuleKxGroup {
    name: rustls::NamedGroup::secp384r1,
    algorithm: &module::ECDH_P384,
};

/// Hybrid key exchange with X25519 and ML-KEM-768, for TLS 1.3 only.
pub static X25519MLKEM768: &dyn SupportedKxGroup = &hybrid::Hybrid {
    classical: X25519,
    post_quantum: MLKEM768,
    layout: hybrid::Layout {
        classical_share_len: 32,
        post_quantum_client_share_len: mlkem::MlKem768::ENCAPS_LEN,
        post_quantum_server_share_len: mlkem::MlKem768::CIPHERTEXT_LEN,
        post_quantum_first: true,
    },
    name: rustls::NamedGroup::X25519MLKEM768,
};

/// Hybrid key exchange with ECDH on P-256 and ML-KEM-768, for TLS 1.3 only.
pub static SECP256R1MLKEM768: &dyn SupportedKxGroup = &hybrid::Hybrid {
    classical: SECP256R1,
    post_quantum: MLKEM768,
    layout: hybrid::Layout {
        classical_share_len: 65,
        post_quantum_client_share_len: mlkem::MlKem768::ENCAPS_LEN,
        post_quantum_server_share_len: mlkem::MlKem768::CIPHERTEXT_LEN,
        post_quantum_first: false,
    },
    name: rustls::NamedGroup::secp256r1MLKEM768,
};

/// Key exchange with ML-KEM-768 alone, for TLS 1.3 only.
pub static MLKEM768: &dyn SupportedKxGroup = &mlkem::MlKem768::new(rustls::NamedGroup::MLKEM768);

/// Key exchange with ML-KEM-1024 alone, for TLS 1.3 only.
pub static MLKEM1024: &dyn SupportedKxGroup = &mlkem::MlKem1024::new(rustls::NamedGroup::MLKEM1024);

/// An elliptic-curve key exchange group.
#[derive(Debug)]
struct KxGroup {
    name: rustls::NamedGroup,
    algorithm: &'static agreement::Algorithm,
}

impl SupportedKxGroup for KxGroup {
    fn start(&self) -> Result<Box<dyn crypto::ActiveKeyExchange>, rustls::Error> {
        let priv_key = agreement::PrivateKey::generate(self.algorithm)
            .or(Err(rustls::Error::from(crypto::GetRandomFailed)))?;
        Ok(Box::new(Active {
            group: self.name,
            priv_key,
        }))
    }

    fn ffdhe_group(&self) -> Option<FfdheGroup<'static>> {
        None
    }

    fn name(&self) -> rustls::NamedGroup {
        self.name
    }
}

struct Active {
    group: rustls::NamedGroup,
    priv_key: agreement::PrivateKey,
}

impl crypto::ActiveKeyExchange for Active {
    fn complete(self: Box<Self>, peer: &[u8]) -> Result<crypto::SharedSecret, rustls::Error> {
        let shared_secret = self
            .priv_key
            .agree(peer)
            .map_err(|_| rustls::Error::from(rustls::PeerMisbehaved::InvalidKeyShare))?;
        Ok(crypto::SharedSecret::from(shared_secret.as_ref()))
    }

    fn pub_key(&self) -> &[u8] {
        self.priv_key.public_key().as_ref()
    }

    fn ffdhe_group(&self) -> Option<FfdheGroup<'static>> {
        None
    }

    fn group(&self) -> rustls::NamedGroup {
        self.group
    }
}

/// An elliptic-curve key exchange group whose ECDH runs in the module.
#[cfg(feature = "fips")]
#[derive(Debug)]
struct ModuleKxGroup {
    name: rustls::NamedGroup,
    algorithm: &'static module::Algorithm,
}

#[cfg(feature = "fips")]
impl SupportedKxGroup for ModuleKxGroup {
    fn start(&self) -> Result<Box<dyn crypto::ActiveKeyExchange>, rustls::Error> {
        let priv_key = module::PrivateKey::generate(self.algorithm)
            .map_err(|_| rustls::Error::from(crypto::GetRandomFailed))?;
        Ok(Box::new(ModuleActive {
            group: self.name,
            priv_key,
        }))
    }

    fn ffdhe_group(&self) -> Option<FfdheGroup<'static>> {
        None
    }

    fn name(&self) -> rustls::NamedGroup {
        self.name
    }

    fn fips(&self) -> bool {
        true
    }
}

#[cfg(feature = "fips")]
struct ModuleActive {
    group: rustls::NamedGroup,
    priv_key: module::PrivateKey,
}

#[cfg(feature = "fips")]
impl crypto::ActiveKeyExchange for ModuleActive {
    fn complete(self: Box<Self>, peer: &[u8]) -> Result<crypto::SharedSecret, rustls::Error> {
        let shared_secret = self
            .priv_key
            .agree(peer)
            .map_err(|_| rustls::Error::from(rustls::PeerMisbehaved::InvalidKeyShare))?;
        Ok(crypto::SharedSecret::from(shared_secret.as_ref()))
    }

    fn pub_key(&self) -> &[u8] {
        self.priv_key.public_key().as_ref()
    }

    fn ffdhe_group(&self) -> Option<FfdheGroup<'static>> {
        None
    }

    fn group(&self) -> rustls::NamedGroup {
        self.group
    }
}

#[cfg(test)]
mod tests {
    use rustls::NamedGroup;
    use rustls::ProtocolVersion;

    use super::*;

    #[test]
    fn classical_groups() {
        for (group, name, algorithm) in [
            (X25519, NamedGroup::X25519, &agreement::X25519),
            (SECP256R1, NamedGroup::secp256r1, &agreement::ECDH_P256),
            (SECP384R1, NamedGroup::secp384r1, &agreement::ECDH_P384),
        ] {
            assert_eq!(group.name(), name);
            assert_eq!(group.ffdhe_group(), None);
            assert!(group.usable_for_version(ProtocolVersion::TLSv1_2));
            assert!(group.usable_for_version(ProtocolVersion::TLSv1_3));

            // A key exchange with an invalid peer public key should fail.
            let active = group.start().unwrap();
            assert_eq!(active.group(), name);
            assert!(active.complete(&[0u8]).is_err());

            // A key exchange with a valid peer public key should succeed.
            let active = group.start().unwrap();
            assert_eq!(active.ffdhe_group(), None);
            let peer = agreement::PrivateKey::generate(algorithm).unwrap();
            assert!(active.complete(peer.public_key().as_ref()).is_ok());
        }
    }

    #[test]
    fn hybrid_refuses_shares_of_the_wrong_length() {
        for (group, classical_len) in [(X25519MLKEM768, 32), (SECP256R1MLKEM768, 65)] {
            let client_len = mlkem::MlKem768::ENCAPS_LEN + classical_len;
            let server_len = mlkem::MlKem768::CIPHERTEXT_LEN + classical_len;
            assert_eq!(group.ffdhe_group(), None);
            let active = group.start().unwrap();
            assert_eq!(active.pub_key().len(), client_len);
            assert_eq!(active.ffdhe_group(), None);

            for len in [0, client_len - 1, client_len + 1] {
                assert!(group.start_and_complete(&vec![0; len]).is_err());
            }
            for len in [0, server_len - 1, server_len + 1] {
                let active = group.start().unwrap();
                assert!(active.complete(&vec![0; len]).is_err());
            }
        }
    }

    // X25519MLKEM768 puts ML-KEM first in its shares and secret, and
    // SECP256R1MLKEM768 puts ECDH first, so each hybrid's classical part sits
    // where its own layout says.
    #[test]
    fn hybrid_layouts() {
        for (group, classical, classical_len, post_quantum_first) in [
            (X25519MLKEM768, X25519, 32, true),
            (SECP256R1MLKEM768, SECP256R1, 65, false),
        ] {
            let client = group.start().unwrap();
            let (classical_group, classical_share) = client.hybrid_component().unwrap();
            assert_eq!(classical_group, classical.name());
            let share = client.pub_key();
            let at = match post_quantum_first {
                true => share.len() - classical_len,
                false => 0,
            };
            assert_eq!(&share[at..at + classical_len], classical_share);
        }
    }
}
