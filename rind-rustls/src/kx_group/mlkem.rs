use core::fmt;
use core::marker::PhantomData;

use rustls::crypto::{ActiveKeyExchange, CompletedKeyExchange, SharedSecret, SupportedKxGroup};
use rustls::ffdhe_groups::FfdheGroup;
use rustls::{Error, NamedGroup, PeerMisbehaved, ProtocolVersion};

use crate::backend::kem;

/// A key exchange with one ML-KEM parameter set alone, which `group` names.
pub(super) struct MlKem<A> {
    group: NamedGroup,
    set: PhantomData<fn() -> A>,
}

impl<A> fmt::Debug for MlKem<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MlKem")
            .field("group", &self.group)
            .finish_non_exhaustive()
    }
}

pub(super) type MlKem768 = MlKem<kem::MlKem768>;
pub(super) type MlKem1024 = MlKem<kem::MlKem1024>;

impl<A: kem::Algorithm> MlKem<A> {
    pub(super) const fn new(group: NamedGroup) -> Self {
        Self {
            group,
            set: PhantomData,
        }
    }
}

impl MlKem768 {
    pub(super) const ENCAPS_LEN: usize = 1184;
    pub(super) const CIPHERTEXT_LEN: usize = 1088;
}

impl<A: kem::Algorithm> SupportedKxGroup for MlKem<A> {
    fn start(&self) -> Result<Box<dyn ActiveKeyExchange>, Error> {
        let decaps_key =
            kem::DecapsulationKey::<A>::generate().map_err(|_| Error::FailedToGetRandomBytes)?;
        let encaps_key_bytes = decaps_key.public_key().as_ref().to_vec();

        Ok(Box::new(Active {
            decaps_key,
            encaps_key_bytes,
            group: self.group,
        }))
    }

    fn start_and_complete(&self, client_share: &[u8]) -> Result<CompletedKeyExchange, Error> {
        let encaps_key =
            kem::EncapsulationKey::<A>::new(client_share).map_err(|_| INVALID_KEY_SHARE)?;

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
        self.group
    }

    fn usable_for_version(&self, version: ProtocolVersion) -> bool {
        version == ProtocolVersion::TLSv1_3
    }

    /// ML-KEM runs in the module under `fips`.
    fn fips(&self) -> bool {
        cfg!(feature = "fips")
    }
}

struct Active<A: kem::Algorithm> {
    decaps_key: kem::DecapsulationKey<A>,
    encaps_key_bytes: Vec<u8>,
    group: NamedGroup,
}

impl<A: kem::Algorithm> ActiveKeyExchange for Active<A> {
    fn complete(self: Box<Self>, peer_pub_key: &[u8]) -> Result<SharedSecret, Error> {
        let ciphertext = kem::Ciphertext::<A>::new(peer_pub_key).map_err(|_| INVALID_KEY_SHARE)?;
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
        self.group
    }
}

const INVALID_KEY_SHARE: Error = Error::PeerMisbehaved(PeerMisbehaved::InvalidKeyShare);

#[cfg(test)]
mod tests {
    use crabgrind::memcheck::{self, MemState};
    use crabgrind::valgrind::{self, RunningMode};
    use rustls::ProtocolVersion;

    use super::*;
    use crate::kx_group::{MLKEM768, MLKEM1024};

    /// Marks a shared secret public under `admin/ctgrind`'s valgrind, so a
    /// test may compare it: these tests check agreement, which a handshake
    /// never branches on.
    fn public(value: &[u8]) {
        if let RunningMode::Valgrind = valgrind::running_mode() {
            memcheck::mark_memory(value.as_ptr().cast(), value.len(), MemState::Defined).unwrap();
        }
    }

    /// Each group with its name and its public key and ciphertext lengths.
    fn groups() -> [(&'static dyn SupportedKxGroup, NamedGroup, usize, usize); 2] {
        [
            (
                MLKEM768,
                NamedGroup::MLKEM768,
                MlKem768::ENCAPS_LEN,
                MlKem768::CIPHERTEXT_LEN,
            ),
            // FIPS 203's sizes: ML-KEM-1024's key and ciphertext are both 1568 bytes.
            (MLKEM1024, NamedGroup::MLKEM1024, 1568, 1568),
        ]
    }

    #[test]
    fn test_kx_mlkem() {
        for (key, name, encaps_len, ciphertext_len) in groups() {
            // Create a private key and verify its metadata.
            assert_eq!(key.name(), name);
            // `MlKem`'s `Debug` is hand-written, so a test has to format it.
            assert_eq!(
                format!("{key:?}"),
                format!("MlKem {{ group: {name:?}, .. }}")
            );
            assert_eq!(key.ffdhe_group(), None);
            assert!(!key.usable_for_version(ProtocolVersion::TLSv1_2));
            assert!(key.usable_for_version(ProtocolVersion::TLSv1_3));
            assert_eq!(key.start().unwrap().group(), name);

            // A key exchange with an invalid peer public key should fail.
            assert!(key.start_and_complete(&[0u8]).is_err());

            // A key exchange with a valid peer public key should succeed, and
            // both sides should end with the same 32-byte secret.
            let client = key.start().unwrap();
            assert_eq!(client.ffdhe_group(), None);
            assert_eq!(client.pub_key().len(), encaps_len);
            let server = key.start_and_complete(client.pub_key()).unwrap();
            assert_eq!(server.group, name);
            assert_eq!(server.pub_key.len(), ciphertext_len);
            let secret = client.complete(&server.pub_key).unwrap();
            public(secret.secret_bytes());
            public(server.secret.secret_bytes());
            assert_eq!(secret.secret_bytes().len(), 32);
            assert_eq!(secret.secret_bytes(), server.secret.secret_bytes());
        }
    }

    // FIPS 203's modulus check refuses a client share with a coefficient of q
    // or more, and a ciphertext of the wrong length is refused; a tampered
    // one of the right length is not: it yields an unrelated secret, which
    // fails later, as FIPS 203's implicit rejection has it.
    #[test]
    fn test_kx_mlkem_refuses_malformed_shares() {
        for (key, _, encaps_len, ciphertext_len) in groups() {
            for share in [vec![0xff; encaps_len], vec![0; encaps_len - 1]] {
                assert_eq!(
                    key.start_and_complete(&share).err(),
                    Some(INVALID_KEY_SHARE)
                );
            }
            assert!(key.start_and_complete(&vec![0; encaps_len + 1]).is_err());

            for len in [0, ciphertext_len - 1, ciphertext_len + 1] {
                let client = key.start().unwrap();
                assert_eq!(
                    client.complete(&vec![0; len]).err(),
                    Some(INVALID_KEY_SHARE)
                );
            }

            let client = key.start().unwrap();
            let mut server = key.start_and_complete(client.pub_key()).unwrap();
            server.pub_key[0] ^= 1;
            let secret = client.complete(&server.pub_key).unwrap();
            public(secret.secret_bytes());
            public(server.secret.secret_bytes());
            assert_ne!(secret.secret_bytes(), server.secret.secret_bytes());
        }
    }

    // rustls's aws-lc-rs provider and this one finish each other's exchanges
    // and agree on which shares to refuse.
    // aws-lc-rs does not build for wasm.
    #[cfg(not(target_family = "wasm"))]
    #[test]
    fn test_kx_mlkem_matches_aws_lc_rs() {
        use rustls::crypto::aws_lc_rs::kx_group as aws_lc_rs;

        for ((ours, name, encaps_len, ciphertext_len), theirs) in groups()
            .into_iter()
            .zip([aws_lc_rs::MLKEM768, aws_lc_rs::MLKEM1024])
        {
            assert_eq!(theirs.name(), name);
            assert!(!theirs.usable_for_version(ProtocolVersion::TLSv1_2));
            assert_eq!(theirs.start().unwrap().pub_key().len(), encaps_len);

            for (client, server) in [(ours, theirs), (theirs, ours)] {
                let client = client.start().unwrap();
                let server = server.start_and_complete(client.pub_key()).unwrap();
                assert_eq!(server.pub_key.len(), ciphertext_len);
                let secret = client.complete(&server.pub_key).unwrap();
                public(secret.secret_bytes());
                public(server.secret.secret_bytes());
                assert_eq!(secret.secret_bytes(), server.secret.secret_bytes());
            }

            let shares = [
                vec![],
                vec![0; 1],
                vec![0; encaps_len - 1],
                vec![0; encaps_len],
                vec![0; encaps_len + 1],
                vec![0xff; encaps_len],
                vec![0xff; ciphertext_len],
            ];
            for (i, share) in shares.iter().enumerate() {
                assert_eq!(
                    ours.start_and_complete(share).map(drop),
                    theirs.start_and_complete(share).map(drop),
                    "client share {i}"
                );
                assert_eq!(
                    ours.start().unwrap().complete(share).map(drop),
                    theirs.start().unwrap().complete(share).map(drop),
                    "server share {i}"
                );
            }
        }
    }
}
