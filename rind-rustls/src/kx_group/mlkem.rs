use rind::kem::{self, MlKem768 as Set};
use rustls::crypto::{ActiveKeyExchange, CompletedKeyExchange, SharedSecret, SupportedKxGroup};
use rustls::ffdhe_groups::FfdheGroup;
use rustls::{Error, NamedGroup, PeerMisbehaved, ProtocolVersion};

#[derive(Debug)]
pub(super) struct MlKem768;

impl MlKem768 {
    pub(super) const ENCAPS_LEN: usize = 1184;
    pub(super) const CIPHERTEXT_LEN: usize = 1088;
}

impl SupportedKxGroup for MlKem768 {
    fn start(&self) -> Result<Box<dyn ActiveKeyExchange>, Error> {
        let decaps_key =
            kem::DecapsulationKey::<Set>::generate().map_err(|_| Error::FailedToGetRandomBytes)?;
        let encaps_key_bytes = decaps_key.public_key().as_ref().to_vec();

        Ok(Box::new(Active {
            decaps_key,
            encaps_key_bytes,
        }))
    }

    fn start_and_complete(&self, client_share: &[u8]) -> Result<CompletedKeyExchange, Error> {
        let encaps_key =
            kem::EncapsulationKey::<Set>::new(client_share).map_err(|_| INVALID_KEY_SHARE)?;

        let (ciphertext, shared_secret) = encaps_key
            .encapsulate()
            .map_err(|_| Error::FailedToGetRandomBytes)?;

        Ok(CompletedKeyExchange {
            group: self.name(),
            pub_key: Vec::from(ciphertext.as_ref()),
            secret: SharedSecret::from(shared_secret.as_ref()),
        })
    }

    fn ffdhe_group(&self) -> Option<FfdheGroup<'static>> {
        None
    }

    fn name(&self) -> NamedGroup {
        NamedGroup::MLKEM768
    }

    fn usable_for_version(&self, version: ProtocolVersion) -> bool {
        version == ProtocolVersion::TLSv1_3
    }
}

struct Active {
    decaps_key: kem::DecapsulationKey<Set>,
    encaps_key_bytes: Vec<u8>,
}

impl ActiveKeyExchange for Active {
    fn complete(self: Box<Self>, peer_pub_key: &[u8]) -> Result<SharedSecret, Error> {
        let ciphertext = kem::Ciphertext::new(peer_pub_key).map_err(|_| INVALID_KEY_SHARE)?;
        let shared_secret = self.decaps_key.decapsulate(&ciphertext);

        Ok(SharedSecret::from(shared_secret.as_ref()))
    }

    fn pub_key(&self) -> &[u8] {
        &self.encaps_key_bytes
    }

    fn ffdhe_group(&self) -> Option<FfdheGroup<'static>> {
        None
    }

    fn group(&self) -> NamedGroup {
        NamedGroup::MLKEM768
    }
}

const INVALID_KEY_SHARE: Error = Error::PeerMisbehaved(PeerMisbehaved::InvalidKeyShare);

#[cfg(test)]
mod tests {
    use rustls::ProtocolVersion;

    use super::*;

    #[test]
    fn test_kx_mlkem() {
        // Create a private key and verify its metadata.
        let key = MlKem768;
        assert_eq!(key.name(), NamedGroup::MLKEM768);
        assert_eq!(key.ffdhe_group(), None);
        assert!(!key.usable_for_version(ProtocolVersion::TLSv1_2));
        assert!(key.usable_for_version(ProtocolVersion::TLSv1_3));
        assert_eq!(key.start().unwrap().group(), NamedGroup::MLKEM768);

        // A key exchange with an invalid peer public key should fail.
        assert!(key.start_and_complete(&[0u8]).is_err());

        // A key exchange with a valid peer public key should succeed.
        let active = key.start().unwrap();
        assert_eq!(active.ffdhe_group(), None);
        let peer_public_key = active.pub_key();
        assert!(key.start_and_complete(peer_public_key).is_ok());
    }
}
