// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! OPAQUE-3DH (RFC 9807), in its two Argon2id configurations.
//!
//! Each suite's OPRF is `super::oprf`'s OPRF mode, over the group the 3DH
//! key exchange runs on too; HKDF, HMAC, and the transcript hash run the
//! OPRF's hash. Every step is RFC 9807's, written once over the group.
//!
//! Everything derived from the password, the server's private key, its OPRF
//! seed, or a record's masking key runs in constant time, except Argon2id's
//! data-dependent addressing after its first pass's first half, which reads
//! memory at password-derived indexes: the cost of its memory hardness, which
//! RFC 9106 and RFC 9807 accept. A peer's elements are decoded as public
//! data. The client declassifies the server's public
//! key, which it unmasks with a password-derived pad, only once the
//! envelope's tag has authenticated it.

use core::fmt;

use super::argon2::Params;
use super::oprf::{
    Bytes, ClientState, Group, MAX_ELEMENT, Mode, P256, Ristretto255, decode, derive_scalar,
    encode, scalar_from_key,
};
use super::{digest, hkdf, hmac};
use crate::error::{Error, KeyFormatError};
use crate::low::{Entry, Zeroable, ZeroableRef, ct, ct_equal, zeroise_value};
use crate::mid::argon2::{Cost, argon2id};
use crate::mid::hash_to_curve::Xmd;
use crate::mid::rng::{RandomSource, SystemRandom};

/// `Nn` and `Nseed`: every nonce and seed is 32 bytes.
const NN: usize = 32;
const NSEED: usize = 32;

/// `Nsk` and `Nok`: both groups' scalars are 32 bytes.
const NSK: usize = 32;

/// The lengths RFC 9807 names for a suite's group and hash. `Noe` is `Npk`,
/// and `Nm` and `Nx` are `Nh`, in both suites.
#[derive(Clone, Copy)]
struct Lens {
    npk: usize,
    nh: usize,
}

impl Lens {
    /// `client_public_key || masking_key || envelope_nonce || auth_tag`.
    const fn record(self) -> usize {
        self.npk + self.nh + NN + self.nh
    }

    /// `server_public_key || envelope`, masked.
    const fn masked(self) -> usize {
        self.npk + NN + self.nh
    }

    /// `blinded_message || client_nonce || client_public_keyshare`.
    const fn ke1(self) -> usize {
        self.npk + NN + self.npk
    }

    /// `evaluated_message || masking_nonce || masked_response || server_nonce
    /// || server_public_keyshare || server_mac`.
    const fn ke2(self) -> usize {
        self.npk + NN + self.masked() + NN + self.npk + self.nh
    }

    /// `oprf_seed || server_private_key || fake_client_public_key`.
    const fn setup(self) -> usize {
        self.nh + NSK + self.npk
    }
}

// The longest of each, over both suites, as `tests::lengths` checks: P-256's
// compressed points, and ristretto255's suite for everything holding a hash.
const MAX_PK: usize = 33;
const MAX_HASH: usize = 64;
const MAX_RECORD: usize = 192;
const MAX_MASKED: usize = 128;
const MAX_KE1: usize = 98;
const MAX_KE2: usize = 320;
const MAX_SETUP: usize = 128;

/// RFC 9807's Argon2id: `S = zeroes(16)`, `T = Nh`, no secret or data.
const STRETCH_SALT: [u8; 16] = [0; 16];

/// An RFC 9807 configuration: the OPRF and the group 3DH runs on, the hash
/// HKDF, HMAC, and the transcript run, and the key stretching function.
pub struct Suite {
    group: GroupId,
    stretch: Stretch,
    name: &'static str,
}

#[derive(Clone, Copy)]
enum GroupId {
    Ristretto255,
    P256,
}

/// The key stretching function, `Stretch`.
#[derive(Clone, Copy)]
enum Stretch {
    Argon2id(Cost),
    /// RFC 9807's test vectors' identity function, which no shipped suite
    /// may reach.
    #[cfg(test)]
    Identity,
}

impl PartialEq for Suite {
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self, other)
    }
}

impl Eq for Suite {}

impl fmt::Debug for Suite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name)
    }
}

/// OPAQUE-3DH over ristretto255 with SHA-512, HKDF-SHA-512, and HMAC-SHA-512,
/// stretching with RFC 9807's Argon2id: 2 GiB, one pass, and four lanes.
///
/// Elements, scalars, and public keys are 32-byte encodings, which makes KE1
/// 96 bytes and KE2 320; session and export keys are 64 bytes.
pub static RISTRETTO255_SHA512_ARGON2ID: Suite = Suite {
    group: GroupId::Ristretto255,
    stretch: Stretch::Argon2id(Params::FIRST_RECOMMENDED.cost()),
    name: "OPAQUE-3DH(ristretto255-SHA512, Argon2id)",
};

/// OPAQUE-3DH over P-256 with SHA-256, HKDF-SHA-256, and HMAC-SHA-256,
/// stretching with RFC 9807's Argon2id: 2 GiB, one pass, and four lanes.
///
/// Elements and public keys are 33-byte compressed points and scalars 32
/// bytes, which makes KE1 98 bytes and KE2 259; session and export keys are
/// 32 bytes.
pub static P256_SHA256_ARGON2ID: Suite = Suite {
    group: GroupId::P256,
    stretch: Stretch::Argon2id(Params::FIRST_RECOMMENDED.cost()),
    name: "OPAQUE-3DH(P256-SHA256, Argon2id)",
};

/// A suite's group, with the algorithms its hash runs.
trait Ake: Group {
    const LENS: Lens = Lens {
        npk: Self::ELEMENT_LEN,
        nh: <Self::Hash as Xmd>::OUTPUT,
    };
    fn hkdf() -> &'static hkdf::Algorithm;
    fn hmac() -> &'static hmac::Algorithm;
    fn digest() -> &'static digest::Algorithm;
}

impl Ake for Ristretto255 {
    fn hkdf() -> &'static hkdf::Algorithm {
        &hkdf::HKDF_SHA512
    }

    fn hmac() -> &'static hmac::Algorithm {
        &hmac::HMAC_SHA512
    }

    fn digest() -> &'static digest::Algorithm {
        &digest::SHA512
    }
}

impl Ake for P256 {
    fn hkdf() -> &'static hkdf::Algorithm {
        &hkdf::HKDF_SHA256
    }

    fn hmac() -> &'static hmac::Algorithm {
        &hmac::HMAC_SHA256
    }

    fn digest() -> &'static digest::Algorithm {
        &digest::SHA256
    }
}

/// Runs `$body` with `$G` the [`Ake`] group of the suite `$suite`.
macro_rules! with_ake {
    ($suite:expr, $G:ident => $body:expr) => {
        match $suite.group {
            GroupId::Ristretto255 => {
                type $G = Ristretto255;
                $body
            }
            GroupId::P256 => {
                type $G = P256;
                $body
            }
        }
    };
}

/// Defines `$name`, holding a `$inner<G>` for each suite's group `G`, with a
/// `From` for each.
///
/// `repr(u8)` puts `Ristretto255` at tag zero, and each variant is plain
/// words and hash states, so all-bits-zero is a valid value, and a drop can
/// wipe the tag and any unused tail along with the rest.
macro_rules! grouped {
    ($(#[$attr:meta])* enum $name:ident($inner:ident)) => {
        $(#[$attr])*
        #[repr(u8)]
        enum $name {
            Ristretto255($inner<Ristretto255>),
            P256($inner<P256>),
        }

        impl Zeroable for $name {}

        impl From<$inner<Ristretto255>> for $name {
            fn from(inner: $inner<Ristretto255>) -> Self {
                Self::Ristretto255(inner)
            }
        }

        impl From<$inner<P256>> for $name {
            fn from(inner: $inner<P256>) -> Self {
                Self::P256(inner)
            }
        }
    };
}

/// Runs `$body` with `$inner` the group's value inside `$value`, one of
/// `$name`'s variants.
macro_rules! dispatch {
    ($name:ident, $value:expr, $inner:ident => $body:expr) => {
        match $value {
            $name::Ristretto255($inner) => $body,
            $name::P256($inner) => $body,
        }
    };
}

/// What both parties bind into a login's transcript: the application's
/// context and each party's identity.
///
/// An identity left `None` is that party's public key, as RFC 9807 section 4
/// sets it; most applications leave both so. Registration binds the
/// identities into the record's envelope, so each login must pass the same
/// ones; only logins bind the context. The client and the server must pass
/// the same values.
#[derive(Clone, Copy, Debug, Default)]
pub struct Session<'a> {
    /// The application's context string, under 2^16 bytes, such as its name
    /// and version.
    pub context: &'a [u8],
    /// The client's identity, 1 byte to under 2^16, such as its user name.
    pub client_identity: Option<&'a [u8]>,
    /// The server's identity, 1 byte to under 2^16, such as its domain name.
    pub server_identity: Option<&'a [u8]>,
}

impl Session<'_> {
    /// Refuses a context or identity RFC 9807's two-byte lengths cannot
    /// encode, or an empty identity, which its `<1..2^16-1>` excludes.
    fn check(&self) -> Result<(), Error> {
        let identity = |id: Option<&[u8]>| id.is_none_or(|id| !id.is_empty() && fits_u16(id));
        match fits_u16(self.context)
            && identity(self.client_identity)
            && identity(self.server_identity)
        {
            true => Ok(()),
            false => Err(Error::WrongLength),
        }
    }
}

fn fits_u16(bytes: &[u8]) -> bool {
    bytes.len() <= usize::from(u16::MAX)
}

/// `I2OSP(len(x), 2)`, for an `x` [`Session::check`] bounded.
fn len_prefix(x: &[u8]) -> [u8; 2] {
    debug_assert!(fits_u16(x));
    (x.len() as u16).to_be_bytes()
}

/// The concatenation of `parts`, at most `N` bytes.
fn concat<const N: usize>(parts: &[&[u8]]) -> Bytes<N> {
    let mut out = Bytes::zeroed(parts.iter().map(|part| part.len()).sum());
    let mut at = 0;
    for part in parts {
        out.as_mut()[at..at + part.len()].copy_from_slice(part);
        at += part.len();
    }
    out
}

/// Refuses `bytes` unless it is `len` long.
fn check_len(bytes: &[u8], len: usize) -> Result<(), Error> {
    match bytes.len() == len {
        true => Ok(()),
        false => Err(KeyFormatError::WrongLength.into()),
    }
}

/// `Expand(prk, concat(info), len(out))`.
fn expand(prk: &hkdf::Prk, info: &[&[u8]], out: &mut [u8]) -> Result<(), Error> {
    prk.fill(info, out)
}

/// `MAC(key, msg)`.
fn mac<G: Ake>(key: &[u8], msg: &[u8]) -> hmac::Tag {
    hmac::sign(&hmac::Key::new(G::hmac(), key), msg)
}

/// RFC 9807 6.4.1's `DeriveDiffieHellmanKeyPair(seed)`: the private key and
/// the encoded public key, both secret.
fn derive_dh<G: Ake>(seed: &[u8]) -> Result<(G::Scalar, Bytes<MAX_ELEMENT>), Error> {
    let private = derive_scalar::<G>(Mode::Oprf, seed, b"OPAQUE-DeriveDiffieHellmanKeyPair")?;
    let public = encode::<G>(&G::mul_base(&private));
    Ok((private, public))
}

/// `DeriveDiffieHellmanKeyPair(random(Nseed))`, the public key made public.
fn generate_dh<G: Ake>(
    rng: &mut dyn RandomSource,
) -> Result<(G::Scalar, Bytes<MAX_ELEMENT>), Error> {
    let mut seed = [0u8; NSEED];
    rng.fill(&mut seed)?;
    ct::secret_slice(&seed);
    let (private, public) = derive_dh::<G>(&seed)?;
    Ok((private, ct::into_public(public)))
}

/// `DiffieHellman(k, B)`, secret. Neither the scalar, which is nonzero, nor
/// the element, which is not the identity, makes the identity in a
/// prime-order group.
fn dh<G: Ake>(k: &G::Scalar, b: &G::Element) -> Bytes<MAX_ELEMENT> {
    encode::<G>(&G::mul(b, k))
}

impl Stretch {
    /// `Stretch(msg)`, into `out`, `Nh` bytes.
    fn apply(self, msg: &[u8], out: &mut [u8]) -> Result<(), Error> {
        match self {
            Self::Argon2id(cost) => argon2id(cost, msg, &STRETCH_SALT, &[], &[], out),
            #[cfg(test)]
            Self::Identity => {
                out.copy_from_slice(msg);
                Ok(())
            }
        }
    }
}

/// `randomized_password = Extract("", concat(oprf_output,
/// Stretch(oprf_output)))`.
fn randomized_password<G: Ake>(stretch: Stretch, oprf_output: &[u8]) -> Result<hkdf::Prk, Error> {
    let nh = G::LENS.nh;
    let mut ikm = [0u8; 2 * MAX_HASH];
    ikm[..nh].copy_from_slice(oprf_output);
    stretch.apply(oprf_output, &mut ikm[nh..2 * nh])?;
    hkdf::Salt::new(G::hkdf(), b"").extract(&ikm[..2 * nh])
}

/// `masking_key = Expand(randomized_password, "MaskingKey", Nh)`.
fn masking_key<G: Ake>(randomized_password: &hkdf::Prk) -> Result<[u8; MAX_HASH], Error> {
    let mut key = [0u8; MAX_HASH];
    expand(
        randomized_password,
        &[b"MaskingKey"],
        &mut key[..G::LENS.nh],
    )?;
    Ok(key)
}

/// `credential_response_pad`, XORed into `out`: `Npk + Nn + Nm` bytes.
fn mask<G: Ake>(masking_key: &[u8], masking_nonce: &[u8], out: &mut [u8]) -> Result<(), Error> {
    let mut pad = [0u8; MAX_MASKED];
    let pad = &mut pad[..out.len()];
    let prk = hkdf::Prk::new(G::hkdf(), masking_key);
    expand(&prk, &[masking_nonce, b"CredentialResponsePad"], pad)?;
    for (out, pad) in out.iter_mut().zip(pad.iter()) {
        *out ^= pad;
    }
    Ok(())
}

/// The keys RFC 9807 4.1.2's `Store` and 4.1.3's `Recover` expand from the
/// randomized password and an envelope's nonce.
struct EnvelopeKeys {
    auth_key: [u8; MAX_HASH],
    export_key: ExportKey,
    /// The client's key pair's.
    seed: [u8; NSEED],
}

impl EnvelopeKeys {
    fn new<G: Ake>(randomized_password: &hkdf::Prk, nonce: &[u8]) -> Result<Self, Error> {
        let nh = G::LENS.nh;
        let mut keys = Self {
            auth_key: [0; MAX_HASH],
            export_key: ExportKey(Bytes::zeroed(nh)),
            seed: [0; NSEED],
        };
        expand(
            randomized_password,
            &[nonce, b"AuthKey"],
            &mut keys.auth_key[..nh],
        )?;
        expand(
            randomized_password,
            &[nonce, b"ExportKey"],
            keys.export_key.0.as_mut(),
        )?;
        expand(randomized_password, &[nonce, b"PrivateKey"], &mut keys.seed)?;
        Ok(keys)
    }

    /// The envelope's `auth_tag`, over its nonce and the cleartext
    /// credentials: the server's public key and both identities, each
    /// defaulting to its party's public key.
    fn auth_tag<G: Ake>(
        &self,
        nonce: &[u8],
        server_public_key: &[u8],
        client_public_key: &[u8],
        session: &Session<'_>,
    ) -> hmac::Tag {
        let key = hmac::Key::new(G::hmac(), &self.auth_key[..G::LENS.nh]);
        let mut ctx = hmac::Context::with_key(&key);
        ctx.update(nonce);
        ctx.update(server_public_key);
        for identity in [
            session.server_identity.unwrap_or(server_public_key),
            session.client_identity.unwrap_or(client_public_key),
        ] {
            ctx.update(&len_prefix(identity));
            ctx.update(identity);
        }
        ctx.sign()
    }
}

/// RFC 9807 6.4.2.1's `Preamble`, hashed: `ke2_head` is KE2 short of its
/// MAC, `credential_response || server_nonce || server_public_keyshare`.
fn preamble<G: Ake>(
    context: &[u8],
    client_identity: &[u8],
    ke1: &[u8],
    server_identity: &[u8],
    ke2_head: &[u8],
) -> digest::Context {
    let mut hash = digest::Context::new(G::digest());
    hash.update(b"OPAQUEv1-");
    for (prefixed, then) in [
        (context, &[][..]),
        (client_identity, ke1),
        (server_identity, ke2_head),
    ] {
        hash.update(&len_prefix(prefixed));
        hash.update(prefixed);
        hash.update(then);
    }
    hash
}

/// The keys RFC 9807 6.4.2.2's `DeriveKeys` makes, and the MACs over the
/// transcript they key.
struct AkeKeys {
    km2: [u8; MAX_HASH],
    km3: [u8; MAX_HASH],
    session_key: SessionKey,
}

impl AkeKeys {
    /// `DeriveKeys(ikm, preamble)`, for the hash of the preamble.
    fn new<G: Ake>(ikm: &[u8], preamble_hash: &[u8]) -> Result<Self, Error> {
        let nx = G::LENS.nh;
        let prk = hkdf::Salt::new(G::hkdf(), b"").extract(ikm)?;
        let mut handshake_secret = [0u8; MAX_HASH];
        let mut keys = Self {
            km2: [0; MAX_HASH],
            km3: [0; MAX_HASH],
            session_key: SessionKey(Bytes::zeroed(nx)),
        };
        derive_secret(
            &prk,
            b"HandshakeSecret",
            preamble_hash,
            &mut handshake_secret[..nx],
        )?;
        derive_secret(
            &prk,
            b"SessionKey",
            preamble_hash,
            keys.session_key.0.as_mut(),
        )?;
        let handshake_secret = hkdf::Prk::new(G::hkdf(), &handshake_secret[..nx]);
        derive_secret(&handshake_secret, b"ServerMAC", b"", &mut keys.km2[..nx])?;
        derive_secret(&handshake_secret, b"ClientMAC", b"", &mut keys.km3[..nx])?;
        Ok(keys)
    }

    /// `server_mac = MAC(Km2, Hash(preamble))`.
    fn server_mac<G: Ake>(&self, preamble_hash: &[u8]) -> hmac::Tag {
        mac::<G>(&self.km2[..G::LENS.nh], preamble_hash)
    }

    /// `MAC(Km3, Hash(concat(preamble, server_mac)))`, for `preamble`'s hash
    /// context.
    fn client_mac<G: Ake>(&self, mut preamble: digest::Context, server_mac: &[u8]) -> hmac::Tag {
        preamble.update(server_mac);
        mac::<G>(&self.km3[..G::LENS.nh], preamble.finish().as_ref())
    }
}

/// `Derive-Secret(secret, label, transcript_hash)`: TLS 1.3's
/// `Expand-Label`, with the label under `"OPAQUE-"`, to `Nx` bytes.
fn derive_secret(
    secret: &hkdf::Prk,
    label: &[u8],
    transcript_hash: &[u8],
    out: &mut [u8],
) -> Result<(), Error> {
    let length = (out.len() as u16).to_be_bytes();
    let label_len = [(b"OPAQUE-".len() + label.len()) as u8];
    let context_len = [transcript_hash.len() as u8];
    let info: [&[u8]; 6] = [
        &length,
        &label_len,
        b"OPAQUE-",
        label,
        &context_len,
        transcript_hash,
    ];
    expand(secret, &info, out)
}

/// The server's long-term state: its OPRF seed, its key pair, and the
/// public key of the fake record it answers an unknown client with; wiped
/// on drop.
///
/// It encodes as `oprf_seed || server_private_key ||
/// fake_client_public_key`, as opaque-ke's `ServerSetup` serializes, so a
/// server can move between the two.
pub struct ServerSetup {
    suite: ZeroableRef<Suite>,
    bytes: Bytes<MAX_SETUP>,
    public_key: Bytes<MAX_PK>,
}

impl ServerSetup {
    /// Generates an OPRF seed and key pairs for `suite` from the system
    /// random source.
    ///
    /// Every record a server registers depends on the setup, so it keeps
    /// [`Self::to_bytes`] for as long as any record lives.
    pub fn generate(suite: &'static Suite) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        with_ake!(suite, G => Self::generate_with::<G>(suite, &mut SystemRandom))
    }

    fn generate_with<G: Ake>(
        suite: &'static Suite,
        rng: &mut dyn RandomSource,
    ) -> Result<Self, Error> {
        let l = G::LENS;
        let mut oprf_seed = [0u8; MAX_HASH];
        rng.fill(&mut oprf_seed[..l.nh])?;
        ct::secret_slice(&oprf_seed);
        let private = G::random_scalar()?;
        let fake = ct::into_public(encode::<G>(&G::mul_base(&G::random_scalar()?)));
        let mut private_bytes = [0u8; NSK];
        G::scalar_to_bytes(&private, &mut private_bytes);
        Self::new::<G>(
            suite,
            concat(&[&oprf_seed[..l.nh], &private_bytes, fake.as_ref()]),
        )
    }

    /// Loads a setup for `suite` from [`Self::to_bytes`]'s encoding, which
    /// opaque-ke's `ServerSetup::serialize` writes too.
    ///
    /// A wrong length is refused with [`Error::KeyRejected`], as is a private
    /// key outside 1 to the group order less one, or a fake public key that
    /// does not decode. The fake public key must have been generated at
    /// random with its private key discarded, as [`Self::generate`] and
    /// opaque-ke's setups do: one whose private key is known lets anyone
    /// check an unknown account's KE2 MAC, which tells it from a registered
    /// one. [`ServerLogin::finish`] still refuses its logins.
    pub fn from_bytes(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        with_ake!(suite, G => {
            check_len(bytes, G::LENS.setup())?;
            let mut copy = Bytes::zeroed(bytes.len());
            copy.as_mut().copy_from_slice(bytes);
            Self::new::<G>(suite, copy)
        })
    }

    /// Checks `bytes`, of the suite's setup length, and derives the public
    /// key. Marks the seed and private key secret.
    fn new<G: Ake>(suite: &'static Suite, bytes: Bytes<MAX_SETUP>) -> Result<Self, Error> {
        let l = G::LENS;
        ct::secret_slice(&bytes.as_ref()[..l.nh + NSK]);
        let private = scalar_from_key::<G>(&bytes.as_ref()[l.nh..l.nh + NSK])?;
        decode::<G>(&bytes.as_ref()[l.nh + NSK..])?;
        let public = ct::into_public(encode::<G>(&G::mul_base(&private)));
        Ok(Self {
            suite: ZeroableRef::new(suite),
            bytes,
            public_key: concat(&[public.as_ref()]),
        })
    }

    /// Encodes the setup as [`Self::from_bytes`] loads it.
    pub fn to_bytes(&self) -> SetupBytes {
        SetupBytes(self.bytes.clone())
    }

    /// Returns the setup's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite.get()
    }

    /// The server's public key, which RFC 9807's client recovers from its
    /// envelope rather than takes as an input.
    pub fn public_key(&self) -> &[u8] {
        self.public_key.as_ref()
    }

    fn oprf_seed(&self, l: Lens) -> &[u8] {
        &self.bytes.as_ref()[..l.nh]
    }

    fn private_key(&self, l: Lens) -> &[u8] {
        &self.bytes.as_ref()[l.nh..l.nh + NSK]
    }

    fn fake_public_key(&self, l: Lens) -> &[u8] {
        &self.bytes.as_ref()[l.nh + NSK..]
    }

    /// Answers a client's registration request for the account
    /// `credential_identifier`, by RFC 9807 5.2.2's
    /// `CreateRegistrationResponse`.
    ///
    /// The identifier must be the one later logins pass in
    /// [`Credential::identifier`], and no other account's. A request for
    /// another suite is refused with [`Error::Unsupported`].
    pub fn register(
        &self,
        request: &RegistrationRequest,
        credential_identifier: &[u8],
    ) -> Result<RegistrationResponse, Error> {
        let _entry = Entry::new_secret();
        if request.suite() != self.suite() {
            return Err(Error::Unsupported);
        }
        with_ake!(self.suite(), G => {
            let evaluated = self.evaluate::<G>(credential_identifier, request.as_ref())?;
            Ok(RegistrationResponse(Message::new(
                self.suite(),
                &[evaluated.as_ref(), self.public_key()],
            )))
        })
    }

    /// `BlindEvaluate` of `blinded` under the account's OPRF key, made public.
    fn evaluate<G: Ake>(
        &self,
        credential_identifier: &[u8],
        blinded: &[u8],
    ) -> Result<Bytes<MAX_ELEMENT>, Error> {
        let l = G::LENS;
        let prk = hkdf::Prk::new(G::hkdf(), self.oprf_seed(l));
        let mut seed = [0u8; NSK];
        expand(&prk, &[credential_identifier, b"OprfKey"], &mut seed)?;
        let key = derive_scalar::<G>(Mode::Oprf, &seed, b"OPAQUE-DeriveKeyPair")?;
        let blinded = decode::<G>(blinded)?;
        Ok(ct::into_public(encode::<G>(&G::mul(&blinded, &key))))
    }

    /// Answers a client's KE1 for `credential`, by RFC 9807 6.2.2's
    /// `GenerateKE2`, returning the state that checks its KE3 and the KE2 to
    /// send it.
    ///
    /// An unregistered account, whose [`Credential::record`] is `None`, gets
    /// RFC 9807 6.3.2.2's fake record: this setup's fake public key, a random
    /// masking key, and a zero envelope. Its KE2 takes the same steps as a
    /// registered one's, and no client that cannot guess a password tells
    /// the two apart; its login then fails at [`ServerLogin::finish`]. The
    /// caller must look the record up in a way that does not reveal whether
    /// the account has one, such as the same query and cache path for both.
    ///
    /// A KE1 or record for another suite is refused with
    /// [`Error::Unsupported`], and a session whose context or identities are
    /// too long with [`Error::WrongLength`].
    pub fn login(
        &self,
        ke1: &Ke1,
        credential: &Credential<'_>,
        session: &Session<'_>,
    ) -> Result<(ServerLogin, Ke2), Error> {
        let _entry = Entry::new_secret();
        self.login_with(ke1, credential, session, &mut SystemRandom)
    }

    fn login_with(
        &self,
        ke1: &Ke1,
        credential: &Credential<'_>,
        session: &Session<'_>,
        rng: &mut dyn RandomSource,
    ) -> Result<(ServerLogin, Ke2), Error> {
        let suite = self.suite();
        if ke1.suite() != suite || credential.record.is_some_and(|r| r.suite() != suite) {
            return Err(Error::Unsupported);
        }
        session.check()?;
        with_ake!(suite, G => self.respond::<G>(ke1, credential, session, rng))
    }

    fn respond<G: Ake>(
        &self,
        ke1: &Ke1,
        credential: &Credential<'_>,
        session: &Session<'_>,
        rng: &mut dyn RandomSource,
    ) -> Result<(ServerLogin, Ke2), Error> {
        let l = G::LENS;
        // Both paths draw the fake masking key, so neither takes longer.
        let mut fake_masking_key = [0u8; MAX_HASH];
        rng.fill(&mut fake_masking_key[..l.nh])?;
        ct::secret_slice(&fake_masking_key);
        let record: Bytes<MAX_RECORD> = match credential.record {
            Some(record) => concat(&[record.as_ref()]),
            None => concat(&[
                self.fake_public_key(l),
                &fake_masking_key[..l.nh],
                &[0; NN + MAX_HASH][..NN + l.nh],
            ]),
        };
        let (client_public_key, rest) = record.as_ref().split_at(l.npk);
        let (masking_key, envelope) = rest.split_at(l.nh);
        // A stored record's masking key hides whether its account exists.
        ct::secret_slice(masking_key);

        // RFC 9807 6.3.2.2's `CreateCredentialResponse`.
        let ke1 = ke1.as_ref();
        let evaluated = self.evaluate::<G>(credential.identifier, &ke1[..l.npk])?;
        let mut masking_nonce = [0u8; NN];
        rng.fill(&mut masking_nonce)?;
        let mut masked: Bytes<MAX_MASKED> = concat(&[self.public_key(), envelope]);
        mask::<G>(masking_key, &masking_nonce, masked.as_mut())?;
        let masked = ct::into_public(masked);

        // RFC 9807 6.4.4's `AuthServerRespond`.
        let mut server_nonce = [0u8; NN];
        rng.fill(&mut server_nonce)?;
        let (keyshare_private, keyshare_public) = generate_dh::<G>(rng)?;
        let mut ke2: Bytes<MAX_KE2> = concat(&[
            evaluated.as_ref(),
            &masking_nonce,
            masked.as_ref(),
            &server_nonce,
            keyshare_public.as_ref(),
            &[0; MAX_HASH][..l.nh],
        ]);
        let head = l.ke2() - l.nh;
        let preamble = preamble::<G>(
            session.context,
            session.client_identity.unwrap_or(client_public_key),
            ke1,
            session.server_identity.unwrap_or(self.public_key()),
            &ke2.as_ref()[..head],
        );

        let client_keyshare = decode::<G>(&ke1[l.npk + NN..])?;
        let client_public_key = decode::<G>(client_public_key)?;
        let private = scalar_from_key::<G>(self.private_key(l))?;
        let ikm: Bytes<{ 3 * MAX_ELEMENT }> = concat(&[
            dh::<G>(&keyshare_private, &client_keyshare).as_ref(),
            dh::<G>(&private, &client_keyshare).as_ref(),
            dh::<G>(&keyshare_private, &client_public_key).as_ref(),
        ]);
        let keys = AkeKeys::new::<G>(ikm.as_ref(), preamble.clone().finish().as_ref())?;
        let server_mac = ct::into_public(keys.server_mac::<G>(preamble.clone().finish().as_ref()));
        ke2.as_mut()[head..].copy_from_slice(server_mac.as_ref());
        let expected_client_mac = keys.client_mac::<G>(preamble, server_mac.as_ref());

        Ok((
            ServerLogin {
                suite: ZeroableRef::new(self.suite()),
                expected_client_mac: concat(&[expected_client_mac.as_ref()]),
                session_key: keys.session_key.0.clone(),
                registered: credential.record.is_some(),
            },
            Ke2(Message {
                suite: self.suite(),
                bytes: ke2,
            }),
        ))
    }
}

impl Drop for ServerSetup {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for ServerSetup {}

impl fmt::Debug for ServerSetup {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ServerSetup")
            .field("suite", self.suite())
            .finish_non_exhaustive()
    }
}

/// The account a login is for: the identifier its registration used and, if
/// it registered, its record.
#[derive(Clone, Copy, Debug)]
pub struct Credential<'a> {
    /// The account's `credential_identifier`, unique to it, such as its
    /// user name.
    pub identifier: &'a [u8],
    /// The account's record, or `None` for an unknown account, which gets a
    /// fake response.
    pub record: Option<&'a RegistrationRecord>,
}

/// A client's state between its registration request and the server's
/// response, wiped on drop.
pub struct ClientRegistration {
    suite: ZeroableRef<Suite>,
    inner: RegistrationInner,
}

grouped!(
    /// A registering client's OPRF state, for one suite.
    enum RegistrationInner(ClientState)
);

impl ClientRegistration {
    /// Starts registering `password` for `suite`, by RFC 9807 5.2.1's
    /// `CreateRegistrationRequest`, returning the state to finish with and
    /// the request to send the server.
    ///
    /// A password of `2^16 - 1` bytes or more is refused with
    /// [`Error::WrongLength`].
    pub fn start(
        suite: &'static Suite,
        password: &[u8],
    ) -> Result<(Self, RegistrationRequest), Error> {
        let _entry = Entry::new_secret();
        with_ake!(suite, G => Self::start_with::<G>(suite, password, G::random_scalar()?))
    }

    fn start_with<G: Ake>(
        suite: &'static Suite,
        password: &[u8],
        blind: G::Scalar,
    ) -> Result<(Self, RegistrationRequest), Error>
    where
        RegistrationInner: From<ClientState<G>>,
    {
        let (state, _, blinded) = ClientState::<G>::blind(Mode::Oprf, password, blind)?;
        Ok((
            Self {
                suite: ZeroableRef::new(suite),
                inner: state.into(),
            },
            RegistrationRequest(Message::new(suite, &[blinded.as_ref()])),
        ))
    }

    /// Finishes registering with the server's response, by RFC 9807 5.2.3's
    /// `FinalizeRegistrationRequest`, returning the record to upload to the
    /// server and the export key.
    ///
    /// Run registration only over a channel that authenticates the server
    /// and keeps the messages confidential and unaltered, such as TLS: the
    /// record carries the masking key that hides whether the account exists
    /// (RFC 9807 3.2 and 10.10).
    ///
    /// This runs the suite's Argon2id, which holds 2 GiB for the call, and
    /// fails with [`Error::OutOfMemory`] if that reservation fails. A host
    /// that overcommits memory can grant it and still kill the process when
    /// the pages are touched, so size the process's limit for it. The
    /// session's identities are bound into the record, so every login must
    /// pass the same ones. A response for another suite is refused with
    /// [`Error::Unsupported`], and identities that are too long with
    /// [`Error::WrongLength`].
    pub fn finish(
        self,
        response: &RegistrationResponse,
        session: &Session<'_>,
    ) -> Result<(RegistrationRecord, ExportKey), Error> {
        let _entry = Entry::new_secret();
        self.finish_with(response, session, &mut SystemRandom)
    }

    fn finish_with(
        &self,
        response: &RegistrationResponse,
        session: &Session<'_>,
        rng: &mut dyn RandomSource,
    ) -> Result<(RegistrationRecord, ExportKey), Error> {
        let suite = self.suite.get();
        if response.suite() != suite {
            return Err(Error::Unsupported);
        }
        session.check()?;
        dispatch!(RegistrationInner, &self.inner, state => store(suite, state, response, session, rng))
    }

    /// Returns the registration's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite.get()
    }
}

/// `FinalizeRegistrationRequest`, with RFC 9807 4.1.2's `Store`.
fn store<G: Ake>(
    suite: &'static Suite,
    state: &ClientState<G>,
    response: &RegistrationResponse,
    session: &Session<'_>,
    rng: &mut dyn RandomSource,
) -> Result<(RegistrationRecord, ExportKey), Error> {
    let l = G::LENS;
    let (evaluated, server_public_key) = response.as_ref().split_at(l.npk);
    let oprf_output = state.finalize(&decode::<G>(evaluated)?);
    let randomized_password = randomized_password::<G>(suite.stretch, oprf_output.as_ref())?;
    let mut nonce = [0u8; NN];
    rng.fill(&mut nonce)?;
    let masking_key = masking_key::<G>(&randomized_password)?;
    let keys = EnvelopeKeys::new::<G>(&randomized_password, &nonce)?;
    let (_, client_public_key) = derive_dh::<G>(&keys.seed)?;
    let auth_tag = keys.auth_tag::<G>(
        &nonce,
        server_public_key,
        client_public_key.as_ref(),
        session,
    );
    // The client uploads all of it.
    let record = ct::into_public(concat(&[
        client_public_key.as_ref(),
        &masking_key[..l.nh],
        &nonce,
        auth_tag.as_ref(),
    ]));
    Ok((
        RegistrationRecord {
            suite: ZeroableRef::new(suite),
            bytes: record,
        },
        keys.export_key,
    ))
}

impl Drop for ClientRegistration {
    fn drop(&mut self) {
        // The OPRF's hash holds the password.
        zeroise_value(self);
    }
}

impl Zeroable for ClientRegistration {}

impl fmt::Debug for ClientRegistration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ClientRegistration")
            .field("suite", self.suite())
            .finish_non_exhaustive()
    }
}

/// A logging-in client's OPRF state, ephemeral key, and KE1.
struct LoginState<G: Group> {
    oprf: ClientState<G>,
    keyshare: G::Scalar,
    ke1: Bytes<MAX_KE1>,
}

grouped!(
    /// A logging-in client's state, for one suite.
    enum LoginInner(LoginState)
);

/// A client's state between its KE1 and the server's KE2, wiped on drop.
pub struct ClientLogin {
    suite: ZeroableRef<Suite>,
    inner: LoginInner,
}

impl ClientLogin {
    /// Starts logging in with `password` for `suite`, by RFC 9807 6.2.1's
    /// `GenerateKE1`, returning the state to finish with and the KE1 to send
    /// the server.
    ///
    /// A password of `2^16 - 1` bytes or more is refused with
    /// [`Error::WrongLength`].
    pub fn start(suite: &'static Suite, password: &[u8]) -> Result<(Self, Ke1), Error> {
        let _entry = Entry::new_secret();
        with_ake!(suite, G => {
            Self::start_with::<G>(suite, password, G::random_scalar()?, &mut SystemRandom)
        })
    }

    fn start_with<G: Ake>(
        suite: &'static Suite,
        password: &[u8],
        blind: G::Scalar,
        rng: &mut dyn RandomSource,
    ) -> Result<(Self, Ke1), Error>
    where
        LoginInner: From<LoginState<G>>,
    {
        let (oprf, _, blinded) = ClientState::<G>::blind(Mode::Oprf, password, blind)?;
        let mut nonce = [0u8; NN];
        rng.fill(&mut nonce)?;
        let (keyshare, keyshare_public) = generate_dh::<G>(rng)?;
        let ke1: Bytes<MAX_KE1> = concat(&[blinded.as_ref(), &nonce, keyshare_public.as_ref()]);
        Ok((
            Self {
                suite: ZeroableRef::new(suite),
                inner: LoginState {
                    oprf,
                    keyshare,
                    ke1: ke1.clone(),
                }
                .into(),
            },
            Ke1(Message { suite, bytes: ke1 }),
        ))
    }

    /// Finishes logging in with the server's KE2, by RFC 9807 6.2.3's
    /// `GenerateKE3`, returning the KE3 to send the server, the session
    /// key, and the export key.
    ///
    /// This runs the suite's Argon2id, which holds 2 GiB for the call, and
    /// fails with [`Error::OutOfMemory`] if that reservation fails. A host
    /// that overcommits memory can grant it and still kill the process when
    /// the pages are touched, so size the process's limit for it. A wrong
    /// password, other identities than registration bound, an unknown
    /// account, or a server that does not hold the record fails with
    /// [`Error::BadSignature`]; the server learns of it only when no valid
    /// KE3 arrives. A KE2 for another suite is refused with
    /// [`Error::Unsupported`], and a session whose context or identities
    /// are too long with [`Error::WrongLength`].
    pub fn finish(
        self,
        ke2: &Ke2,
        session: &Session<'_>,
    ) -> Result<(Ke3, SessionKey, ExportKey), Error> {
        let _entry = Entry::new_secret();
        let suite = self.suite();
        if ke2.suite() != suite {
            return Err(Error::Unsupported);
        }
        session.check()?;
        dispatch!(LoginInner, &self.inner, state => state.finish(suite, ke2, session))
    }

    /// Returns the login's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite.get()
    }
}

impl<G: Ake> LoginState<G> {
    /// `GenerateKE3`: RFC 9807 6.3.2.3's `RecoverCredentials`, then 6.4.3's
    /// `AuthClientFinalize`.
    fn finish(
        &self,
        suite: &'static Suite,
        ke2: &Ke2,
        session: &Session<'_>,
    ) -> Result<(Ke3, SessionKey, ExportKey), Error> {
        let l = G::LENS;
        let ke2 = ke2.as_ref();
        let (evaluated, rest) = ke2.split_at(l.npk);
        let (masking_nonce, rest) = rest.split_at(NN);
        let (masked, rest) = rest.split_at(l.masked());
        let server_keyshare = &rest[NN..NN + l.npk];
        let server_mac = &rest[NN + l.npk..];

        let oprf_output = self.oprf.finalize(&decode::<G>(evaluated)?);
        let randomized_password = randomized_password::<G>(suite.stretch, oprf_output.as_ref())?;
        let masking_key = masking_key::<G>(&randomized_password)?;
        let mut unmasked: Bytes<MAX_MASKED> = concat(&[masked]);
        mask::<G>(&masking_key[..l.nh], masking_nonce, unmasked.as_mut())?;
        let (server_public_key, envelope) = unmasked.as_ref().split_at(l.npk);
        let (envelope_nonce, auth_tag) = envelope.split_at(NN);

        // RFC 9807 4.1.3's `Recover`.
        let keys = EnvelopeKeys::new::<G>(&randomized_password, envelope_nonce)?;
        let (client_private_key, client_public_key) = derive_dh::<G>(&keys.seed)?;
        let expected = keys.auth_tag::<G>(
            envelope_nonce,
            server_public_key,
            client_public_key.as_ref(),
            session,
        );
        if !ct::into_public(ct_equal(expected.as_ref(), auth_tag)) {
            return Err(Error::BadSignature);
        }
        // The tag authenticated the server's public key, which the server
        // holds anyway, so it is public from here.
        let server_public_key = ct::into_public(concat::<MAX_PK>(&[server_public_key]));

        let server_keyshare_element = decode::<G>(server_keyshare)?;
        let server_public_key_element = decode::<G>(server_public_key.as_ref())?;
        let ikm: Bytes<{ 3 * MAX_ELEMENT }> = concat(&[
            dh::<G>(&self.keyshare, &server_keyshare_element).as_ref(),
            dh::<G>(&self.keyshare, &server_public_key_element).as_ref(),
            dh::<G>(&client_private_key, &server_keyshare_element).as_ref(),
        ]);
        let preamble = preamble::<G>(
            session.context,
            session
                .client_identity
                .unwrap_or(client_public_key.as_ref()),
            self.ke1.as_ref(),
            session
                .server_identity
                .unwrap_or(server_public_key.as_ref()),
            &ke2[..l.ke2() - l.nh],
        );
        let preamble_hash = preamble.clone().finish();
        let ake = AkeKeys::new::<G>(ikm.as_ref(), preamble_hash.as_ref())?;
        let expected_server_mac = ake.server_mac::<G>(preamble_hash.as_ref());
        if !ct::into_public(ct_equal(expected_server_mac.as_ref(), server_mac)) {
            return Err(Error::BadSignature);
        }
        let client_mac = ct::into_public(ake.client_mac::<G>(preamble, server_mac));
        Ok((
            Ke3(Message::new(suite, &[client_mac.as_ref()])),
            ake.session_key,
            keys.export_key,
        ))
    }
}

impl Drop for ClientLogin {
    fn drop(&mut self) {
        // The OPRF's hash holds the password.
        zeroise_value(self);
    }
}

impl Zeroable for ClientLogin {}

impl fmt::Debug for ClientLogin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ClientLogin")
            .field("suite", self.suite())
            .finish_non_exhaustive()
    }
}

/// A server's state between its KE2 and the client's KE3, wiped on drop.
pub struct ServerLogin {
    suite: ZeroableRef<Suite>,
    expected_client_mac: Bytes<MAX_HASH>,
    session_key: Bytes<MAX_HASH>,
    /// Whether the account had a record. A fake record's key is only secret
    /// while the setup's fake public key has no known private part, which
    /// [`ServerSetup::from_bytes`] cannot check, so an unknown account never
    /// gets a session key whatever the KE3 says.
    registered: bool,
}

impl ServerLogin {
    /// Checks the client's KE3, by RFC 9807 6.2.4's `ServerFinish`,
    /// returning the session key once it proves the client holds the
    /// credential its record binds. That is the password's derived key, but
    /// a client may keep it and skip re-entering the password (RFC 9807
    /// 10.13), so a login is no proof the user typed it.
    ///
    /// A KE3 that does not verify, as from a wrong password or an unknown
    /// account, fails with [`Error::BadSignature`]; one for another suite is
    /// refused with [`Error::Unsupported`].
    pub fn finish(self, ke3: &Ke3) -> Result<SessionKey, Error> {
        let _entry = Entry::new_secret();
        if ke3.suite() != self.suite() {
            return Err(Error::Unsupported);
        }
        // The MAC is compared on both paths, so an unknown account takes as long.
        let mac_ok = ct::into_public(ct_equal(ke3.as_ref(), self.expected_client_mac.as_ref()));
        match mac_ok && self.registered {
            true => Ok(SessionKey(self.session_key.clone())),
            false => Err(Error::BadSignature),
        }
    }

    /// Returns the login's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite.get()
    }
}

impl Drop for ServerLogin {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for ServerLogin {}

impl fmt::Debug for ServerLogin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ServerLogin")
            .field("suite", self.suite())
            .finish_non_exhaustive()
    }
}

/// A message's suite and bytes.
#[derive(Clone)]
struct Message<const N: usize> {
    suite: &'static Suite,
    bytes: Bytes<N>,
}

impl<const N: usize> Message<N> {
    fn new(suite: &'static Suite, parts: &[&[u8]]) -> Self {
        Self {
            suite,
            bytes: concat(parts),
        }
    }
}

/// Defines the message `$name` of up to `$max` bytes, which `$check`
/// validates for a group.
macro_rules! message {
    ($(#[$attr:meta])* $name:ident, $max:expr, $check:ident) => {
        $(#[$attr])*
        #[derive(Clone)]
        pub struct $name(Message<{ $max }>);

        impl $name {
            /// Decodes a message for `suite`, refusing a wrong length with
            /// [`Error::KeyRejected`], as it refuses an element that does
            /// not decode or is the identity.
            pub fn new(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
                let _entry = Entry::new_public();
                with_ake!(suite, G => $check::<G>(bytes))?;
                Ok(Self(Message::new(suite, &[bytes])))
            }

            /// Returns the message's suite.
            pub fn suite(&self) -> &'static Suite {
                self.0.suite
            }
        }

        impl AsRef<[u8]> for $name {
            fn as_ref(&self) -> &[u8] {
                self.0.bytes.as_ref()
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_tuple(stringify!($name)).field(&self.as_ref()).finish()
            }
        }
    };
}

/// `blinded_message`.
fn check_request<G: Ake>(bytes: &[u8]) -> Result<(), Error> {
    decode::<G>(bytes).map(|_| ())
}

/// `evaluated_message || server_public_key`.
fn check_response<G: Ake>(bytes: &[u8]) -> Result<(), Error> {
    let l = G::LENS;
    check_len(bytes, 2 * l.npk)?;
    decode::<G>(&bytes[..l.npk])?;
    decode::<G>(&bytes[l.npk..])?;
    Ok(())
}

/// `client_public_key || masking_key || envelope`.
fn check_record<G: Ake>(bytes: &[u8]) -> Result<(), Error> {
    let l = G::LENS;
    check_len(bytes, l.record())?;
    decode::<G>(&bytes[..l.npk]).map(|_| ())
}

/// `blinded_message || client_nonce || client_public_keyshare`.
fn check_ke1<G: Ake>(bytes: &[u8]) -> Result<(), Error> {
    let l = G::LENS;
    check_len(bytes, l.ke1())?;
    decode::<G>(&bytes[..l.npk])?;
    decode::<G>(&bytes[l.npk + NN..])?;
    Ok(())
}

/// `credential_response || server_nonce || server_public_keyshare ||
/// server_mac`.
fn check_ke2<G: Ake>(bytes: &[u8]) -> Result<(), Error> {
    let l = G::LENS;
    check_len(bytes, l.ke2())?;
    decode::<G>(&bytes[..l.npk])?;
    let keyshare = l.npk + NN + l.masked() + NN;
    decode::<G>(&bytes[keyshare..keyshare + l.npk])?;
    Ok(())
}

/// `client_mac`.
fn check_ke3<G: Ake>(bytes: &[u8]) -> Result<(), Error> {
    check_len(bytes, G::LENS.nh)
}

message!(
    /// A client's registration request, its blinded password, which it
    /// sends the server.
    RegistrationRequest,
    MAX_PK,
    check_request
);

message!(
    /// The server's registration response, its evaluated element and public
    /// key, which it returns to the client.
    RegistrationResponse,
    2 * MAX_PK,
    check_response
);

message!(
    /// A client's KE1, its credential request and ephemeral key share,
    /// which it sends the server.
    Ke1,
    MAX_KE1,
    check_ke1
);

message!(
    /// The server's KE2, its masked credential response, ephemeral key
    /// share, and MAC, which it returns to the client.
    Ke2,
    MAX_KE2,
    check_ke2
);

message!(
    /// A client's KE3, its MAC, which it sends the server.
    Ke3,
    MAX_HASH,
    check_ke3
);

/// A client's registration record, which the server stores for its account
/// and passes to every login, wiped on drop.
///
/// It holds the client's public key, its envelope, and the masking key that
/// hides the envelope from anyone who cannot guess the password. Guessing
/// needs the server's OPRF key too, so a stolen record alone allows no
/// offline attack; with the setup it is as sensitive as a password hash, each
/// guess paced by the suite's Argon2id. Protect both.
pub struct RegistrationRecord {
    suite: ZeroableRef<Suite>,
    bytes: Bytes<MAX_RECORD>,
}

impl RegistrationRecord {
    /// Decodes a record for `suite`, refusing a wrong length, or a client
    /// public key that does not decode or is the identity, with
    /// [`Error::KeyRejected`].
    pub fn new(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        with_ake!(suite, G => check_record::<G>(bytes))?;
        Ok(Self {
            suite: ZeroableRef::new(suite),
            bytes: concat(&[bytes]),
        })
    }

    /// Returns the record's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite.get()
    }
}

impl AsRef<[u8]> for RegistrationRecord {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl Drop for RegistrationRecord {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for RegistrationRecord {}

impl fmt::Debug for RegistrationRecord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RegistrationRecord")
            .field("suite", self.suite())
            .finish_non_exhaustive()
    }
}

/// Defines a secret `$name` of the suite's hash length, wiped on drop.
macro_rules! secret {
    ($(#[$attr:meta])* $name:ident) => {
        $(#[$attr])*
        pub struct $name(Bytes<MAX_HASH>);

        impl AsRef<[u8]> for $name {
            fn as_ref(&self) -> &[u8] {
                self.0.as_ref()
            }
        }

        impl Drop for $name {
            fn drop(&mut self) {
                zeroise_value(&mut self.0);
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_tuple(stringify!($name)).finish_non_exhaustive()
            }
        }
    };
}

secret!(
    /// The key a login agrees on, the suite's hash length. The client gets it
    /// once it authenticated the server, before the server has checked the
    /// KE3, so it does not show the server accepted the login; the server
    /// gets it only once it verified the KE3.
    SessionKey
);

secret!(
    /// A key only the client derives, the same at registration and each
    /// login, for the application to encrypt its own data under, as RFC
    /// 9807 section 10.4 describes.
    ///
    /// A login returns it only after the server authenticated. It is stable
    /// only across logins with one record: registering again, even with the
    /// same password, gives a new key that cannot decrypt what the old one
    /// did, so re-encrypt the data under the new key before replacing a
    /// record, or keep the old key until you have.
    ExportKey
);

/// A [`ServerSetup`] as its encoding, which `from_bytes` loads, wiped on
/// drop.
pub struct SetupBytes(Bytes<MAX_SETUP>);

impl AsRef<[u8]> for SetupBytes {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl Drop for SetupBytes {
    fn drop(&mut self) {
        zeroise_value(&mut self.0);
    }
}

impl fmt::Debug for SetupBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SetupBytes").finish_non_exhaustive()
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests;
