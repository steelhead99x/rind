use alloc::boxed::Box;
use alloc::vec::Vec;

use rustls::crypto::{ActiveKeyExchange, CompletedKeyExchange, SharedSecret, SupportedKxGroup};
use rustls::ffdhe_groups::FfdheGroup;
use rustls::{Error, NamedGroup, PeerMisbehaved, ProtocolVersion};

/// A hybrid key exchange, which concatenates its parts' shares and secrets.
#[derive(Debug)]
pub(super) struct Hybrid {
    pub(super) classical: &'static dyn SupportedKxGroup,
    pub(super) post_quantum: &'static dyn SupportedKxGroup,
    pub(super) name: NamedGroup,
    pub(super) layout: Layout,
}

/// Where each part sits in a hybrid's shares and secret.
#[derive(Clone, Copy, Debug)]
pub(super) struct Layout {
    pub(super) classical_share_len: usize,
    pub(super) post_quantum_client_share_len: usize,
    pub(super) post_quantum_server_share_len: usize,
    /// X25519MLKEM768 puts the post-quantum part first; SECP256R1MLKEM768 the classical one.
    pub(super) post_quantum_first: bool,
}

impl Layout {
    /// Splits a received share into its post-quantum and classical parts,
    /// refusing any other length.
    fn split(self, share: &[u8], post_quantum_len: usize) -> Result<(&[u8], &[u8]), Error> {
        if share.len() != post_quantum_len + self.classical_share_len {
            return Err(INVALID_KEY_SHARE);
        }
        Ok(match self.post_quantum_first {
            true => share.split_at(post_quantum_len),
            false => {
                let (classical, post_quantum) = share.split_at(self.classical_share_len);
                (post_quantum, classical)
            }
        })
    }

    fn concat(self, post_quantum: &[u8], classical: &[u8]) -> Vec<u8> {
        match self.post_quantum_first {
            true => [post_quantum, classical].concat(),
            false => [classical, post_quantum].concat(),
        }
    }
}

impl SupportedKxGroup for Hybrid {
    fn start(&self) -> Result<Box<dyn ActiveKeyExchange>, Error> {
        let classical = self.classical.start()?;
        let post_quantum = self.post_quantum.start()?;
        let combined_pub_key = self
            .layout
            .concat(post_quantum.pub_key(), classical.pub_key());

        Ok(Box::new(ActiveHybrid {
            classical,
            post_quantum,
            name: self.name,
            layout: self.layout,
            combined_pub_key,
        }))
    }

    fn start_and_complete(&self, client_share: &[u8]) -> Result<CompletedKeyExchange, Error> {
        let (post_quantum_share, classical_share) = self
            .layout
            .split(client_share, self.layout.post_quantum_client_share_len)?;

        let cl = self.classical.start_and_complete(classical_share)?;
        let pq = self.post_quantum.start_and_complete(post_quantum_share)?;

        Ok(CompletedKeyExchange {
            group: self.name,
            pub_key: self.layout.concat(&pq.pub_key, &cl.pub_key),
            secret: SharedSecret::from(
                self.layout
                    .concat(pq.secret.secret_bytes(), cl.secret.secret_bytes()),
            ),
        })
    }

    fn ffdhe_group(&self) -> Option<FfdheGroup<'static>> {
        None
    }

    fn name(&self) -> NamedGroup {
        self.name
    }

    fn usable_for_version(&self, version: ProtocolVersion) -> bool {
        version == ProtocolVersion::TLSv1_3
    }
}

struct ActiveHybrid {
    classical: Box<dyn ActiveKeyExchange>,
    post_quantum: Box<dyn ActiveKeyExchange>,
    name: NamedGroup,
    layout: Layout,
    combined_pub_key: Vec<u8>,
}

impl ActiveKeyExchange for ActiveHybrid {
    fn complete(self: Box<Self>, peer_pub_key: &[u8]) -> Result<SharedSecret, Error> {
        let (post_quantum_share, classical_share) = self
            .layout
            .split(peer_pub_key, self.layout.post_quantum_server_share_len)?;

        let cl = self.classical.complete(classical_share)?;
        let pq = self.post_quantum.complete(post_quantum_share)?;

        Ok(SharedSecret::from(
            self.layout.concat(pq.secret_bytes(), cl.secret_bytes()),
        ))
    }

    /// Allow the classical computation to be offered and selected separately.
    fn hybrid_component(&self) -> Option<(NamedGroup, &[u8])> {
        Some((self.classical.group(), self.classical.pub_key()))
    }

    fn complete_hybrid_component(
        self: Box<Self>,
        peer_pub_key: &[u8],
    ) -> Result<SharedSecret, Error> {
        self.classical.complete(peer_pub_key)
    }

    fn pub_key(&self) -> &[u8] {
        &self.combined_pub_key
    }

    fn ffdhe_group(&self) -> Option<FfdheGroup<'static>> {
        None
    }

    fn group(&self) -> NamedGroup {
        self.name
    }
}

const INVALID_KEY_SHARE: Error = Error::PeerMisbehaved(PeerMisbehaved::InvalidKeyShare);
