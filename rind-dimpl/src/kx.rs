use std::fmt;

use dimpl::crypto::{ActiveKeyExchange, Buf, NamedGroup, SupportedKxGroup};
use dimpl::{CryptoError, CryptoOperation};
use rind::agreement::{self, PrivateKey, PublicKey};

#[derive(Debug)]
struct Group {
    name: NamedGroup,
    algorithm: &'static agreement::Algorithm,
}

/// Key exchange groups, in order of preference.
pub(crate) static ALL: &[&dyn SupportedKxGroup] = &[
    &Group {
        name: NamedGroup::X25519,
        algorithm: &agreement::X25519,
    },
    &Group {
        name: NamedGroup::Secp256r1,
        algorithm: &agreement::ECDH_P256,
    },
    &Group {
        name: NamedGroup::Secp384r1,
        algorithm: &agreement::ECDH_P384,
    },
];

impl SupportedKxGroup for Group {
    fn name(&self) -> NamedGroup {
        self.name
    }

    fn start_exchange(&self, mut pub_key: Buf) -> Result<Box<dyn ActiveKeyExchange>, CryptoError> {
        let key = PrivateKey::generate(self.algorithm)
            .map_err(|_| CryptoError::OperationFailed(CryptoOperation::GenerateEphemeralKey))?;
        pub_key.clear();
        pub_key.extend_from_slice(key.public_key().as_ref());
        Ok(Box::new(Exchange {
            group: self.name,
            key,
            pub_key,
        }))
    }
}

struct Exchange {
    group: NamedGroup,
    key: PrivateKey,
    pub_key: Buf,
}

impl fmt::Debug for Exchange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Exchange")
            .field("group", &self.group())
            .finish_non_exhaustive()
    }
}

/// Uncompressed P-384, the longest NIST share these groups use.
const MAX_NIST_SHARE: usize = 97;

/// `peer` as the uncompressed point [`PrivateKey::agree`] takes.
///
/// X25519 is unchanged. A NIST compressed point is decompressed, as aws-lc-rs
/// and `PublicKey::new` do. Every other form reaches `agree`, which refuses
/// it: hybrid points (SEC1 prefix `0x06` or `0x07`) and
/// `SubjectPublicKeyInfo`, which aws-lc-rs accepts and RFC 8422 section 5.1.2
/// forbids.
fn nist_share<'a>(
    exchange: &Exchange,
    peer: &'a [u8],
    buf: &'a mut [u8; MAX_NIST_SHARE],
) -> Result<&'a [u8], rind::Error> {
    if !matches!(
        exchange.group,
        NamedGroup::Secp256r1 | NamedGroup::Secp384r1
    ) || !matches!(peer.first(), Some(0x02 | 0x03))
    {
        return Ok(peer);
    }
    let public = PublicKey::new(exchange.key.algorithm(), peer)?;
    let encoded = public.as_ref();
    let out = buf
        .get_mut(..encoded.len())
        .ok_or(rind::Error::WrongLength)?;
    out.copy_from_slice(encoded);
    Ok(out)
}

impl ActiveKeyExchange for Exchange {
    fn pub_key(&self) -> &[u8] {
        &self.pub_key
    }

    fn complete(self: Box<Self>, peer_pub: &[u8], out: &mut Buf) -> Result<(), CryptoError> {
        // Covers a malformed or off-curve point, and X25519's all-zero output
        // from a low-order point (RFC 7748 section 6.1).
        //
        // aws-lc-rs also accepts a NIST point's SEC1 compressed form, which
        // `agree` does not take.
        let mut canonical = [0u8; MAX_NIST_SHARE];
        let peer = nist_share(&self, peer_pub, &mut canonical)
            .map_err(|_| CryptoError::InvalidPublicKey(self.group))?;
        let secret = self
            .key
            .agree(peer)
            .map_err(|_| CryptoError::InvalidPublicKey(self.group))?;
        out.clear();
        out.extend_from_slice(secret.as_ref());
        Ok(())
    }

    fn group(&self) -> NamedGroup {
        self.group
    }
}
