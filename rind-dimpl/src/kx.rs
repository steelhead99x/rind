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

/// Splits the DER element tagged `tag` off the front of `input`, returning its
/// contents and what follows. Only minimal definite lengths below 65536
/// parse, as aws-lc's `CBS_get_asn1` reads them, which covers every
/// `SubjectPublicKeyInfo` these groups take.
fn der(tag: u8, input: &[u8]) -> Option<(&[u8], &[u8])> {
    let [actual, len, rest @ ..] = input else {
        return None;
    };
    let (len, rest) = match (*len, rest) {
        (0..=0x7f, rest) => (usize::from(*len), rest),
        (0x81, [len @ 0x80..=0xff, rest @ ..]) => (usize::from(*len), rest),
        (0x82, [high @ 0x01..=0xff, low, rest @ ..]) => {
            (usize::from(u16::from_be_bytes([*high, *low])), rest)
        }
        _ => return None,
    };
    if *actual != tag {
        return None;
    }
    rest.split_at_checked(len)
}

/// Whether `bytes`, less any leading zeros, is `value`, which has none: how
/// aws-lc compares an explicit curve's fields with a built-in curve's.
fn same_integer(bytes: &[u8], value: &[u8]) -> bool {
    let start = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len());
    bytes[start..] == *value
}

/// Whether `contents` is a minimal, non-negative DER INTEGER.
fn unsigned_integer(contents: &[u8]) -> bool {
    match contents {
        [] => false,
        [0, next, ..] => next & 0x80 != 0,
        [first, ..] => first & 0x80 == 0,
    }
}

/// A NIST curve's named-curve OID and domain parameters, each big-endian
/// with no leading zeros.
struct Curve {
    oid: &'static [u8],
    p: &'static [u8],
    a: &'static [u8],
    b: &'static [u8],
    gx: &'static [u8],
    gy: &'static [u8],
    n: &'static [u8],
}

static P256: Curve = Curve {
    oid: &[0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07],
    p: &[
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff,
    ],
    a: &[
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xfc,
    ],
    b: &[
        0x5a, 0xc6, 0x35, 0xd8, 0xaa, 0x3a, 0x93, 0xe7, 0xb3, 0xeb, 0xbd, 0x55, 0x76, 0x98, 0x86,
        0xbc, 0x65, 0x1d, 0x06, 0xb0, 0xcc, 0x53, 0xb0, 0xf6, 0x3b, 0xce, 0x3c, 0x3e, 0x27, 0xd2,
        0x60, 0x4b,
    ],
    gx: &[
        0x6b, 0x17, 0xd1, 0xf2, 0xe1, 0x2c, 0x42, 0x47, 0xf8, 0xbc, 0xe6, 0xe5, 0x63, 0xa4, 0x40,
        0xf2, 0x77, 0x03, 0x7d, 0x81, 0x2d, 0xeb, 0x33, 0xa0, 0xf4, 0xa1, 0x39, 0x45, 0xd8, 0x98,
        0xc2, 0x96,
    ],
    gy: &[
        0x4f, 0xe3, 0x42, 0xe2, 0xfe, 0x1a, 0x7f, 0x9b, 0x8e, 0xe7, 0xeb, 0x4a, 0x7c, 0x0f, 0x9e,
        0x16, 0x2b, 0xce, 0x33, 0x57, 0x6b, 0x31, 0x5e, 0xce, 0xcb, 0xb6, 0x40, 0x68, 0x37, 0xbf,
        0x51, 0xf5,
    ],
    n: &[
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63,
        0x25, 0x51,
    ],
};

static P384: Curve = Curve {
    oid: &[0x06, 0x05, 0x2b, 0x81, 0x04, 0x00, 0x22],
    p: &[
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff,
        0xff, 0xff, 0xff,
    ],
    a: &[
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff,
        0xff, 0xff, 0xfc,
    ],
    b: &[
        0xb3, 0x31, 0x2f, 0xa7, 0xe2, 0x3e, 0xe7, 0xe4, 0x98, 0x8e, 0x05, 0x6b, 0xe3, 0xf8, 0x2d,
        0x19, 0x18, 0x1d, 0x9c, 0x6e, 0xfe, 0x81, 0x41, 0x12, 0x03, 0x14, 0x08, 0x8f, 0x50, 0x13,
        0x87, 0x5a, 0xc6, 0x56, 0x39, 0x8d, 0x8a, 0x2e, 0xd1, 0x9d, 0x2a, 0x85, 0xc8, 0xed, 0xd3,
        0xec, 0x2a, 0xef,
    ],
    gx: &[
        0xaa, 0x87, 0xca, 0x22, 0xbe, 0x8b, 0x05, 0x37, 0x8e, 0xb1, 0xc7, 0x1e, 0xf3, 0x20, 0xad,
        0x74, 0x6e, 0x1d, 0x3b, 0x62, 0x8b, 0xa7, 0x9b, 0x98, 0x59, 0xf7, 0x41, 0xe0, 0x82, 0x54,
        0x2a, 0x38, 0x55, 0x02, 0xf2, 0x5d, 0xbf, 0x55, 0x29, 0x6c, 0x3a, 0x54, 0x5e, 0x38, 0x72,
        0x76, 0x0a, 0xb7,
    ],
    gy: &[
        0x36, 0x17, 0xde, 0x4a, 0x96, 0x26, 0x2c, 0x6f, 0x5d, 0x9e, 0x98, 0xbf, 0x92, 0x92, 0xdc,
        0x29, 0xf8, 0xf4, 0x1d, 0xbd, 0x28, 0x9a, 0x14, 0x7c, 0xe9, 0xda, 0x31, 0x13, 0xb5, 0xf0,
        0xb8, 0xc0, 0x0a, 0x60, 0xb1, 0xce, 0x1d, 0x7e, 0x81, 0x9d, 0x7a, 0x43, 0x1d, 0x7c, 0x90,
        0xea, 0x0e, 0x5f,
    ],
    n: &[
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xc7, 0x63, 0x4d, 0x81, 0xf4, 0x37,
        0x2d, 0xdf, 0x58, 0x1a, 0x0d, 0xb2, 0x48, 0xb0, 0xa7, 0x7a, 0xec, 0xec, 0x19, 0x6a, 0xcc,
        0xc5, 0x29, 0x73,
    ],
};

impl Curve {
    /// Whether `params`, an `id-ecPublicKey` AlgorithmIdentifier's
    /// parameters, name this curve, as aws-lc's `EC_KEY_parse_parameters`
    /// decides: its OID, or explicit `ECParameters` (RFC 3279 section 2.3.5)
    /// that match it. Those may pad `p`, `a`, `b`, `n`, and each coordinate of
    /// the uncompressed base point with zeros, may carry a seed, and may give
    /// a cofactor of one.
    fn named_by(&self, params: &[u8]) -> bool {
        params == self.oid || self.explicit(params).is_some()
    }

    fn explicit(&self, params: &[u8]) -> Option<()> {
        const PRIME_FIELD: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x01, 0x01];
        let (params, []) = der(0x30, params)? else {
            return None;
        };
        let (version, params) = der(0x02, params)?;
        let (field, params) = der(0x30, params)?;
        let (field_type, field) = der(0x06, field)?;
        let (p, []) = der(0x02, field)? else {
            return None;
        };
        let (curve, params) = der(0x30, params)?;
        let (a, curve) = der(0x04, curve)?;
        let (b, curve) = der(0x04, curve)?;
        let seeded = der(0x03, curve).map_or(curve, |(_, rest)| rest);
        let (base, params) = der(0x04, params)?;
        let (n, params) = der(0x02, params)?;
        let cofactor = match der(0x02, params) {
            Some((cofactor, rest)) => rest.is_empty() && cofactor == [1],
            None => params.is_empty(),
        };
        let [0x04, base @ ..] = base else {
            return None;
        };
        let (gx, gy) = base.split_at_checked(base.len() / 2)?;
        (version == [1]
            && field_type == PRIME_FIELD
            && unsigned_integer(p)
            && same_integer(p, self.p)
            && seeded.is_empty()
            && same_integer(a, self.a)
            && same_integer(b, self.b)
            && base.len() % 2 == 0
            && same_integer(gx, self.gx)
            && same_integer(gy, self.gy)
            && unsigned_integer(n)
            && same_integer(n, self.n)
            && cofactor)
            .then_some(())
    }
}

/// The key inside `peer` when it is a `SubjectPublicKeyInfo` for `group`, as
/// aws-lc-rs's `ParsedPublicKey::new` tries before the raw share.
///
/// As aws-lc's `EVP_parse_public_key` reads it, a NIST key names
/// `id-ecPublicKey` and the group's curve ([`Curve::named_by`]), an X25519
/// key names `id-X25519` with no parameters and holds 32 bytes, and bytes
/// after the structure are ignored. WebCrypto's `id-ecDH`, which
/// `PublicKey::from_spki` takes, is refused, as aws-lc refuses it.
fn spki_key(group: NamedGroup, peer: &[u8]) -> Option<&[u8]> {
    const EC_PUBLIC_KEY: &[u8] = &[0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
    const X25519: &[u8] = &[0x06, 0x03, 0x2b, 0x65, 0x6e];
    let (spki, _) = der(0x30, peer)?;
    let (identifier, spki) = der(0x30, spki)?;
    let (bits, []) = der(0x03, spki)? else {
        return None;
    };
    let [0, key @ ..] = bits else {
        return None;
    };
    let named = match group {
        NamedGroup::X25519 => identifier == X25519 && key.len() == 32,
        NamedGroup::Secp256r1 => identifier
            .strip_prefix(EC_PUBLIC_KEY)
            .is_some_and(|params| P256.named_by(params)),
        NamedGroup::Secp384r1 => identifier
            .strip_prefix(EC_PUBLIC_KEY)
            .is_some_and(|params| P384.named_by(params)),
        _ => false,
    };
    named.then_some(key)
}

/// Uncompressed P-384, the longest NIST share these groups use.
const MAX_NIST_SHARE: usize = 97;

/// `peer` as the uncompressed point [`PrivateKey::agree`] takes.
///
/// X25519 is unchanged. A NIST compressed point is decompressed. A hybrid
/// point of the group's uncompressed length is rewritten to `0x04` when its
/// prefix parity matches `y`, which is the check aws-lc's `EC_POINT_oct2point`
/// makes, and left alone otherwise so `agree` refuses it.
fn nist_share<'a>(
    exchange: &Exchange,
    peer: &'a [u8],
    buf: &'a mut [u8; MAX_NIST_SHARE],
) -> Result<&'a [u8], rind::Error> {
    if !matches!(
        exchange.group,
        NamedGroup::Secp256r1 | NamedGroup::Secp384r1
    ) {
        return Ok(peer);
    }

    let uncompressed_len = exchange.key.public_key().as_ref().len();
    match peer.first().copied() {
        Some(0x02 | 0x03) => {
            let public = PublicKey::new(exchange.key.algorithm(), peer)?;
            let encoded = public.as_ref();
            let out = buf
                .get_mut(..encoded.len())
                .ok_or(rind::Error::WrongLength)?;
            out.copy_from_slice(encoded);
            Ok(out)
        }
        Some(prefix @ (0x06 | 0x07))
            if peer.len() == uncompressed_len
                && peer.len() <= buf.len()
                && (prefix & 1) == (peer[peer.len() - 1] & 1) =>
        {
            buf[..peer.len()].copy_from_slice(peer);
            buf[0] = 0x04;
            Ok(&buf[..peer.len()])
        }
        _ => Ok(peer),
    }
}

impl ActiveKeyExchange for Exchange {
    fn pub_key(&self) -> &[u8] {
        &self.pub_key
    }

    fn complete(self: Box<Self>, peer_pub: &[u8], out: &mut Buf) -> Result<(), CryptoError> {
        // Covers a malformed or off-curve point, and X25519's all-zero output
        // from a low-order point (RFC 7748 section 6.1).
        //
        // aws-lc-rs also accepts the share wrapped in a
        // `SubjectPublicKeyInfo`, a NIST point's SEC1 compressed form, and its
        // hybrid form when the prefix's low bit matches `y`. `agree` takes
        // only the bare share, a NIST point uncompressed.
        let peer = spki_key(self.group, peer_pub).unwrap_or(peer_pub);
        let mut canonical = [0u8; MAX_NIST_SHARE];
        let peer = nist_share(&self, peer, &mut canonical)
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
