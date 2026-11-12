// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RFC 9591's two-round FROST signing protocol.
//!
//! A trusted dealer splits a signing key. Each participant commits to fresh
//! nonces, then signs, and a coordinator aggregates the shares. The
//! [`ED25519_SHA512`] signature is an Ed25519 signature.

mod ed25519;
mod p256;
mod protocol;
mod ristretto;

#[cfg(all(test, not(any(miri, target_family = "wasm"))))]
mod cross;
#[cfg(test)]
mod vectors;

use core::cmp::Ordering;
use core::fmt;

use protocol::{Group, Party};

use crate::error::{Error, KeyFormatError};
use crate::low::{Entry, Zeroable, zeroise_value};
use crate::mid::rng::SystemRandom;

macro_rules! suites {
    ($kind:expr, |$G:ident| $body:expr) => {{
        match $kind {
            Kind::Ed25519 => {
                type $G = ed25519::Ed25519;
                $body
            }
            Kind::Ristretto255 => {
                type $G = ristretto::Ristretto;
                $body
            }
            Kind::P256 => {
                type $G = p256::P256;
                $body
            }
        }
    }};
}

/// FROST(Ed25519, SHA-512). A signature verifies with
/// [`signature::verify::ED25519`](crate::signature::verify::ED25519).
pub static ED25519_SHA512: Suite = Suite {
    kind: Kind::Ed25519,
};

/// FROST(ristretto255, SHA-512).
pub static RISTRETTO255_SHA512: Suite = Suite {
    kind: Kind::Ristretto255,
};

/// FROST(P-256, SHA-256).
pub static P256_SHA256: Suite = Suite { kind: Kind::P256 };

/// One FROST ciphersuite.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Suite {
    kind: Kind,
}

/// All-zero is [`Kind::Ed25519`], so a wiped share still holds a valid tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum Kind {
    Ed25519 = 0,
    Ristretto255 = 1,
    P256 = 2,
}

impl Suite {
    fn element_len(self) -> usize {
        match self.kind {
            Kind::P256 => 33,
            Kind::Ed25519 | Kind::Ristretto255 => 32,
        }
    }

    /// Split a fresh signing key into `max_signers` shares, of which any
    /// `min_signers` can sign.
    ///
    /// Identifiers are the integers `1` through `max_signers`, as RFC 9591
    /// section 5 assigns them. `min_signers` and `max_signers` are refused
    /// when `min_signers` is zero or greater than `max_signers`.
    pub fn deal(&self, min_signers: u16, max_signers: u16) -> Result<DealerOutput, Error> {
        let _entry = Entry::new_secret();
        let dealt = suites!(self.kind, |G| protocol::deal::<G>(
            min_signers,
            max_signers,
            &mut SystemRandom
        ))?;
        Ok(self.output(min_signers, max_signers, dealt))
    }

    /// Aggregate the participants' signature shares into one signature.
    ///
    /// When a share does not verify, this reports the first such participant,
    /// in identifier order, as [`AggregateError::InvalidShare`]. That includes
    /// a verifying share that is not the signer's. Fewer participants than the
    /// threshold, or more than the dealer created, is
    /// [`AggregateError::Failed`] with [`Error::Unsupported`].
    /// [`Error::BadSignature`] is only returned, as [`AggregateError::Failed`],
    /// when every share verifies and the combined signature does not.
    pub fn aggregate(
        &self,
        package: &SigningPackage,
        shares: &[SignatureShare],
        verifying_shares: &[VerifyingShare],
        verifying_key: &VerifyingKey,
    ) -> Result<Signature, AggregateError> {
        let _entry = Entry::new_public();
        if package.kind != self.kind
            || verifying_key.kind != self.kind
            || shares.iter().any(|share| share.kind != self.kind)
            || verifying_shares.iter().any(|share| share.kind != self.kind)
        {
            return Err(AggregateError::Failed(Error::Unsupported));
        }
        let parties = package.parties();
        let mut signature_shares: Vec<([u8; 32], [u8; 32])> = shares
            .iter()
            .map(|share| (share.identifier, share.share))
            .collect();
        sort_by_identifier(self.kind, &mut signature_shares, |share| &share.0);
        let verifying: Vec<([u8; 32], [u8; 33])> = verifying_shares
            .iter()
            .map(|share| (share.identifier, share.element))
            .collect();
        let result = suites!(self.kind, |G| protocol::aggregate::<G>(
            verifying_key.as_bytes(),
            &parties,
            &package.message,
            &signature_shares,
            &verifying,
            verifying_key.min_signers,
            verifying_key.max_signers,
        ));
        match result {
            Ok(bytes) => Signature::new(self.kind, bytes).map_err(AggregateError::Failed),
            Err(protocol::AggFail::Failed(error)) => Err(AggregateError::Failed(error)),
            Err(protocol::AggFail::InvalidShare(identifier)) => {
                Err(AggregateError::InvalidShare(identifier))
            }
        }
    }

    fn output(&self, min_signers: u16, max_signers: u16, dealt: protocol::Dealt) -> DealerOutput {
        // One allocation each. Growth would free the previous block with the
        // signing share still in it, and `Vec` does not drop elements it moves.
        let mut signing_shares = Vec::with_capacity(dealt.shares.len());
        let mut verifying_shares = Vec::with_capacity(dealt.shares.len());
        for share in dealt.shares.iter() {
            signing_shares.push(SigningShare {
                scalar: share.scalar,
                identifier: share.identifier,
                min_signers,
                max_signers,
                kind: self.kind,
            });
            verifying_shares.push(VerifyingShare {
                kind: self.kind,
                identifier: share.identifier,
                element: share.verifying,
            });
        }
        DealerOutput {
            signing_shares,
            verifying_shares,
            verifying_key: VerifyingKey {
                kind: self.kind,
                element: dealt.group,
                min_signers,
                max_signers,
            },
        }
    }
}

impl fmt::Display for Suite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self.kind {
            Kind::Ed25519 => "FROST(Ed25519, SHA-512)",
            Kind::Ristretto255 => "FROST(ristretto255, SHA-512)",
            Kind::P256 => "FROST(P-256, SHA-256)",
        })
    }
}

/// The shares and keys [`Suite::deal`] produced.
pub struct DealerOutput {
    /// One signing share per participant, identifier `1` first.
    pub signing_shares: Vec<SigningShare>,
    /// Each participant's public share, in the same order.
    pub verifying_shares: Vec<VerifyingShare>,
    /// The group's verifying key.
    pub verifying_key: VerifyingKey,
}

/// A participant's secret share of the group's signing key.
///
/// The whole value is wiped on drop under the `wipe` feature.
pub struct SigningShare {
    scalar: [u8; 32],
    identifier: [u8; 32],
    min_signers: u16,
    max_signers: u16,
    kind: Kind,
}

impl SigningShare {
    /// The ciphersuite this share signs with.
    pub fn suite(&self) -> &'static Suite {
        suite(self.kind)
    }

    /// The participant's identifier, in the ciphersuite's scalar encoding.
    pub fn identifier(&self) -> &[u8; 32] {
        &self.identifier
    }

    /// The secret share. Tests use it to feed the Zcash crates.
    #[cfg(all(test, not(any(miri, target_family = "wasm"))))]
    pub(in crate::high::frost) fn scalar_bytes(&self) -> &[u8; 32] {
        &self.scalar
    }
}

impl Drop for SigningShare {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for SigningShare {}

impl Clone for SigningShare {
    fn clone(&self) -> Self {
        Self {
            scalar: self.scalar,
            identifier: self.identifier,
            min_signers: self.min_signers,
            max_signers: self.max_signers,
            kind: self.kind,
        }
    }
}

impl fmt::Debug for SigningShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningShare")
            .field("suite", &self.suite())
            .field("identifier", &self.identifier)
            .finish_non_exhaustive()
    }
}

/// A participant's public share of the group's verifying key.
#[derive(Clone, Debug)]
pub struct VerifyingShare {
    kind: Kind,
    identifier: [u8; 32],
    element: [u8; 33],
}

impl VerifyingShare {
    /// The ciphersuite.
    pub fn suite(&self) -> &'static Suite {
        suite(self.kind)
    }

    /// The participant's identifier, in the ciphersuite's scalar encoding.
    pub fn identifier(&self) -> &[u8; 32] {
        &self.identifier
    }

    /// The share, as the ciphersuite encodes a group element.
    pub fn as_bytes(&self) -> &[u8] {
        &self.element[..suite(self.kind).element_len()]
    }
}

/// The group's verifying key.
#[derive(Clone, Debug)]
pub struct VerifyingKey {
    kind: Kind,
    element: [u8; 33],
    min_signers: u16,
    max_signers: u16,
}

impl VerifyingKey {
    /// The ciphersuite.
    pub fn suite(&self) -> &'static Suite {
        suite(self.kind)
    }

    /// The key, as the ciphersuite encodes a group element.
    ///
    /// For [`ED25519_SHA512`] this is an Ed25519 public key.
    pub fn as_bytes(&self) -> &[u8] {
        &self.element[..suite(self.kind).element_len()]
    }
}

/// The hiding and binding nonces of one commitment.
///
/// [`Self::sign`] consumes them, and drop wipes them under the `wipe`
/// feature, so a nonce cannot sign twice.
pub struct SigningNonces {
    hiding: [u8; 32],
    binding: [u8; 32],
    kind: Kind,
}

impl SigningNonces {
    /// Commit to fresh nonces for `share`.
    ///
    /// Each nonce is `H3(random || share)` with 32 bytes from the system
    /// random source, as RFC 9591 section 4.1 recommends. The commitments are
    /// what the participant sends.
    pub fn commit(share: &SigningShare) -> Result<(Self, Commitments), Error> {
        let _entry = Entry::new_secret();
        let nonces = suites!(share.kind, |G| protocol::commit::<G>(
            &share.scalar,
            &mut SystemRandom
        ))?;
        Ok((
            Self {
                hiding: nonces.hiding,
                binding: nonces.binding,
                kind: share.kind,
            },
            Commitments {
                kind: share.kind,
                identifier: share.identifier,
                hiding: nonces.hiding_commitment,
                binding: nonces.binding_commitment,
            },
        ))
    }

    /// Sign `package`'s message with `share`.
    ///
    /// `package` must contain this participant's commitment. Fewer
    /// participants than the dealer required, or more than it created, is
    /// refused.
    pub fn sign(
        self,
        package: &SigningPackage,
        share: &SigningShare,
        verifying_key: &VerifyingKey,
    ) -> Result<SignatureShare, Error> {
        let _entry = Entry::new_secret();
        if self.kind != share.kind || package.kind != share.kind || verifying_key.kind != share.kind
        {
            return Err(Error::Unsupported);
        }
        let hiding = self.hiding;
        let binding = self.binding;
        let share_bytes = sign_dispatch::sign_share(
            share.kind,
            &share.scalar,
            &share.identifier,
            share.min_signers,
            share.max_signers,
            &hiding,
            &binding,
            verifying_key.as_bytes(),
            &package.parties(),
            &package.message,
        )?;
        Ok(SignatureShare {
            kind: share.kind,
            identifier: share.identifier,
            share: share_bytes,
        })
    }
}

impl Drop for SigningNonces {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for SigningNonces {}

impl fmt::Debug for SigningNonces {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningNonces").finish_non_exhaustive()
    }
}

/// The commitments one participant sends after [`SigningNonces::commit`].
#[derive(Clone, Debug)]
pub struct Commitments {
    kind: Kind,
    identifier: [u8; 32],
    hiding: [u8; 33],
    binding: [u8; 33],
}

impl Commitments {
    /// The ciphersuite.
    pub fn suite(&self) -> &'static Suite {
        suite(self.kind)
    }

    /// The participant's identifier, in the ciphersuite's scalar encoding.
    pub fn identifier(&self) -> &[u8; 32] {
        &self.identifier
    }

    /// The encoding to send: identifier, hiding commitment, binding commitment.
    pub fn to_bytes(&self) -> Vec<u8> {
        let len = self.suite().element_len();
        let mut out = Vec::with_capacity(32 + 2 * len);
        out.extend_from_slice(&self.identifier);
        out.extend_from_slice(&self.hiding[..len]);
        out.extend_from_slice(&self.binding[..len]);
        out
    }

    /// Parse a commitment another participant sent.
    ///
    /// A malformed element or identifier is an error, and so is the identity
    /// element. Ed25519 elements must be in the prime-order subgroup.
    pub fn from_bytes(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        let len = suite.element_len();
        if bytes.len() != 32 + 2 * len {
            return Err(Error::WrongLength);
        }
        let commitments = Self {
            kind: suite.kind,
            identifier: bytes[..32].try_into().unwrap(),
            hiding: element_bytes(&bytes[32..32 + len])?,
            binding: element_bytes(&bytes[32 + len..])?,
        };
        suites!(suite.kind, |G| protocol::validate_party::<G>(
            &commitments.party()
        ))?;
        Ok(commitments)
    }

    fn party(&self) -> Party {
        Party {
            identifier: self.identifier,
            hiding: self.hiding,
            binding: self.binding,
        }
    }
}

/// The message bound to every participant's commitments.
#[derive(Clone, Debug)]
pub struct SigningPackage {
    kind: Kind,
    message: Vec<u8>,
    commitments: Vec<Commitments>,
}

impl SigningPackage {
    /// Bind `message` to `commitments`.
    ///
    /// Commitments are ordered by identifier, as RFC 9591 requires of the
    /// list the binding factor is computed from. A duplicate identifier, an
    /// empty list, or mixed ciphersuites is refused.
    pub fn new(mut commitments: Vec<Commitments>, message: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        // Identifiers are `u16`s, so a list cannot be longer than that.
        if commitments.is_empty() || commitments.len() > usize::from(u16::MAX) {
            return Err(Error::Unsupported);
        }
        let first = &commitments[0];
        let kind = first.kind;
        if commitments.iter().any(|commitment| commitment.kind != kind) {
            return Err(Error::Unsupported);
        }
        sort_by_identifier(kind, &mut commitments, |commitment| &commitment.identifier);
        for pair in commitments.windows(2) {
            if pair[0].identifier == pair[1].identifier {
                return Err(Error::Unsupported);
            }
        }
        for commitment in &commitments {
            suites!(kind, |G| protocol::validate_party::<G>(&commitment.party()))?;
        }
        Ok(Self {
            kind,
            message: message.to_vec(),
            commitments,
        })
    }

    /// The message the signature will cover.
    pub fn message(&self) -> &[u8] {
        &self.message
    }

    fn parties(&self) -> Vec<Party> {
        self.commitments.iter().map(Commitments::party).collect()
    }
}

/// One participant's signature share.
#[derive(Clone, Debug)]
pub struct SignatureShare {
    kind: Kind,
    identifier: [u8; 32],
    share: [u8; 32],
}

impl SignatureShare {
    /// The ciphersuite.
    pub fn suite(&self) -> &'static Suite {
        suite(self.kind)
    }

    /// The participant this share came from.
    pub fn identifier(&self) -> &[u8; 32] {
        &self.identifier
    }

    /// The share, as the ciphersuite encodes a scalar.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.share
    }

    /// Parse a scalar share from `identifier`.
    ///
    /// The scalar must be in `0..order`. Zero is a legal share.
    pub fn from_bytes(
        suite: &'static Suite,
        identifier: &[u8; 32],
        share: &[u8],
    ) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        let share: &[u8; 32] = share.try_into().map_err(|_| Error::WrongLength)?;
        suites!(suite.kind, |G| {
            if G::scalar_from_canonical(identifier).is_none()
                || G::scalar_from_canonical(share).is_none()
            {
                return Err(KeyFormatError::ScalarOutOfRange.into());
            }
            Ok::<(), Error>(())
        })?;
        Ok(Self {
            kind: suite.kind,
            identifier: *identifier,
            share: *share,
        })
    }
}

/// A FROST signature, `R || z` as RFC 9591 appendix A encodes it.
#[derive(Clone, Debug)]
pub struct Signature {
    kind: Kind,
    bytes: [u8; 65],
    len: usize,
}

impl Signature {
    fn new(kind: Kind, bytes: Vec<u8>) -> Result<Self, Error> {
        if bytes.len() > 65 {
            return Err(Error::WrongLength);
        }
        let mut stored = [0u8; 65];
        stored[..bytes.len()].copy_from_slice(&bytes);
        Ok(Self {
            kind,
            bytes: stored,
            len: bytes.len(),
        })
    }

    /// Verify `message` under `verifying_key`.
    ///
    /// [`ED25519_SHA512`] verifies with Ed25519, the same check as
    /// [`signature::verify::ED25519`](crate::signature::verify::ED25519).
    pub fn verify(&self, verifying_key: &VerifyingKey, message: &[u8]) -> Result<(), Error> {
        let _entry = Entry::new_public();
        if self.kind != verifying_key.kind {
            return Err(Error::Unsupported);
        }
        if self.kind == Kind::Ed25519 {
            let key = crate::signature::PublicKey::new(
                &crate::signature::verify::ED25519,
                verifying_key.as_bytes(),
            )?;
            return key.verify(message, self.as_bytes());
        }
        suites!(self.kind, |G| protocol::verify::<G>(
            verifying_key.as_bytes(),
            message,
            self.as_bytes(),
        ))
    }

    /// The signature encoding.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

/// Why [`Suite::aggregate`] failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum AggregateError {
    /// A share, commitment, or key was refused, the participants do not match,
    /// or every share verified while the signature did not.
    Failed(Error),
    /// The participant with this identifier, in the ciphersuite's scalar
    /// encoding, produced a share that does not verify.
    InvalidShare([u8; 32]),
}

impl fmt::Display for AggregateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Failed(error) => write!(f, "{error}"),
            Self::InvalidShare(identifier) => {
                write!(f, "a signature share from participant ")?;
                for byte in identifier {
                    write!(f, "{byte:02x}")?;
                }
                f.write_str(" did not verify")
            }
        }
    }
}

impl core::error::Error for AggregateError {}

fn cmp_identifier(kind: Kind, left: &[u8; 32], right: &[u8; 32]) -> Ordering {
    if kind == Kind::P256 {
        left.cmp(right)
    } else {
        left.iter().rev().cmp(right.iter().rev())
    }
}

/// Insertion sort by public identifier. The standard library's sort
/// divides in its merge path, which `admin/ct-vartime` rejects.
fn sort_by_identifier<T>(kind: Kind, items: &mut [T], identifier: impl Fn(&T) -> &[u8; 32]) {
    for i in 1..items.len() {
        let mut j = i;
        while j > 0
            && cmp_identifier(kind, identifier(&items[j - 1]), identifier(&items[j]))
                == Ordering::Greater
        {
            items.swap(j - 1, j);
            j -= 1;
        }
    }
}

#[cfg(all(test, not(any(miri, target_family = "wasm"))))]
pub(in crate::high::frost) fn signature_from_bytes(
    suite: &Suite,
    bytes: Vec<u8>,
) -> Result<Signature, Error> {
    Signature::new(suite.kind, bytes)
}

fn suite(kind: Kind) -> &'static Suite {
    match kind {
        Kind::Ed25519 => &ED25519_SHA512,
        Kind::Ristretto255 => &RISTRETTO255_SHA512,
        Kind::P256 => &P256_SHA256,
    }
}

fn element_bytes(bytes: &[u8]) -> Result<[u8; 33], Error> {
    if bytes.len() > 33 {
        return Err(Error::WrongLength);
    }
    let mut out = [0u8; 33];
    out[..bytes.len()].copy_from_slice(bytes);
    Ok(out)
}

/// [`SigningNonces::sign`] picks its ciphersuite here. A method cannot grow a
/// type parameter without putting it on the type.
mod sign_dispatch {
    use super::*;

    pub(super) fn sign_share(
        kind: Kind,
        share: &[u8; 32],
        identifier: &[u8; 32],
        min_signers: u16,
        max_signers: u16,
        hiding: &[u8; 32],
        binding: &[u8; 32],
        group_public: &[u8],
        parties: &[Party],
        message: &[u8],
    ) -> Result<[u8; 32], Error> {
        suites!(kind, |G| protocol::sign::<G>(
            share,
            identifier,
            min_signers,
            max_signers,
            hiding,
            binding,
            group_public,
            parties,
            message,
        ))
    }
}

#[cfg(test)]
mod api_tests {
    use super::*;

    /// Under `admin/ctgrind`, nothing may branch on or index by the dealer's
    /// random scalars, a signing share, or a nonce, except the public
    /// zero-or-in-range bit that discards a draw.
    #[test]
    fn secret_dealing_and_signing() {
        each_suite_signs_and_verifies();
    }

    #[test]
    fn each_suite_signs_and_verifies() {
        for suite in [&ED25519_SHA512, &RISTRETTO255_SHA512, &P256_SHA256] {
            let dealt = suite.deal(2, 3).unwrap();
            let (left_nonces, left) = SigningNonces::commit(&dealt.signing_shares[0]).unwrap();
            let (right_nonces, right) = SigningNonces::commit(&dealt.signing_shares[2]).unwrap();
            // Passed in reverse identifier order; the package sorts them.
            let package = SigningPackage::new(vec![right, left], b"frost").unwrap();
            let left_share = left_nonces
                .sign(&package, &dealt.signing_shares[0], &dealt.verifying_key)
                .unwrap();
            let right_share = right_nonces
                .sign(&package, &dealt.signing_shares[2], &dealt.verifying_key)
                .unwrap();
            let signature = suite
                .aggregate(
                    &package,
                    &[right_share, left_share],
                    &dealt.verifying_shares,
                    &dealt.verifying_key,
                )
                .unwrap();
            signature.verify(&dealt.verifying_key, b"frost").unwrap();
            if core::ptr::eq(suite, &ED25519_SHA512) {
                let key = crate::signature::PublicKey::new(
                    &crate::signature::verify::ED25519,
                    dealt.verifying_key.as_bytes(),
                )
                .unwrap();
                key.verify(b"frost", signature.as_bytes()).unwrap();
            }
        }
    }

    #[test]
    fn an_altered_share_names_its_participant() {
        let dealt = ED25519_SHA512.deal(2, 2).unwrap();
        let (left_nonces, left) = SigningNonces::commit(&dealt.signing_shares[0]).unwrap();
        let (right_nonces, right) = SigningNonces::commit(&dealt.signing_shares[1]).unwrap();
        let package = SigningPackage::new(vec![left, right], b"frost").unwrap();
        let left_share = left_nonces
            .sign(&package, &dealt.signing_shares[0], &dealt.verifying_key)
            .unwrap();
        let right_share = right_nonces
            .sign(&package, &dealt.signing_shares[1], &dealt.verifying_key)
            .unwrap();
        let bad =
            SignatureShare::from_bytes(left_share.suite(), left_share.identifier(), &[0u8; 32])
                .unwrap();
        let err = ED25519_SHA512
            .aggregate(
                &package,
                &[bad, right_share],
                &dealt.verifying_shares,
                &dealt.verifying_key,
            )
            .unwrap_err();
        assert_eq!(
            err,
            AggregateError::InvalidShare(*dealt.signing_shares[0].identifier())
        );
    }

    /// Edges the appendix E vectors do not hit: a scalar at the group order,
    /// a non-canonical point, a duplicate identifier, mixed suites, and fewer
    /// signers than the dealer required.
    #[test]
    fn hostile_input_is_refused() {
        // RFC 8032's L, little-endian. The first integer Ed25519 and
        // ristretto255 refuse.
        let order_l = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
            0xde, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x10,
        ];
        // FIPS 186-4's n, big-endian.
        let order_n = [
            0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2,
            0xfc, 0x63, 0x25, 0x51,
        ];
        // 2^255 - 19, little-endian: a non-canonical field element.
        let mut noncanonical_y = [0xffu8; 32];
        noncanonical_y[0] = 0xed;
        noncanonical_y[31] = 0x7f;
        // P-256's p, big-endian, with the compressed-point tag. `x` is not below p.
        let mut noncanonical_p256 = [0u8; 33];
        noncanonical_p256[0] = 0x02;
        noncanonical_p256[1..].copy_from_slice(&[
            0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff,
        ]);

        for (suite, order, point) in [
            (&ED25519_SHA512, &order_l, &noncanonical_y[..]),
            (&RISTRETTO255_SHA512, &order_l, &noncanonical_y[..]),
            (&P256_SHA256, &order_n, &noncanonical_p256[..]),
        ] {
            let mut identifier = [0u8; 32];
            if suite.element_len() == 33 {
                identifier[31] = 1;
            } else {
                identifier[0] = 1;
            }
            let err = SignatureShare::from_bytes(suite, &identifier, order).unwrap_err();
            assert_eq!(err, KeyFormatError::ScalarOutOfRange.into(), "{suite}");
            assert_eq!(
                Commitments::from_bytes(suite, &[0; 10]).unwrap_err(),
                Error::WrongLength,
                "{suite}"
            );
            let mut commitment = identifier.to_vec();
            commitment.extend_from_slice(point);
            commitment.extend_from_slice(point);
            // Rejected on every backend. Ed25519's variant is not the same
            // on s2n-bignum and dalek, so this checks only the refusal.
            let err = Commitments::from_bytes(suite, &commitment).unwrap_err();
            assert!(matches!(err, Error::KeyRejected(_)), "{suite}: {err:?}");

            let dealt = suite.deal(2, 2).unwrap();
            let (nonces, commitment) = SigningNonces::commit(&dealt.signing_shares[0]).unwrap();
            let err = SigningPackage::new(vec![commitment.clone(), commitment.clone()], b"frost")
                .unwrap_err();
            assert_eq!(err, Error::Unsupported, "{suite}");
            let package = SigningPackage::new(vec![commitment], b"frost").unwrap();
            let err = nonces
                .sign(&package, &dealt.signing_shares[0], &dealt.verifying_key)
                .unwrap_err();
            assert_eq!(err, Error::Unsupported, "{suite}");
        }

        // ristretto255's identity is 32 zero bytes. P-256's point at infinity
        // has no compressed encoding. Ed25519's identity is
        // `refuses_a_bad_commitment`.
        let mut identity = [0u8; 96];
        identity[0] = 1;
        assert_eq!(
            Commitments::from_bytes(&RISTRETTO255_SHA512, &identity).unwrap_err(),
            KeyFormatError::SmallOrder.into()
        );

        let dealt_ed = ED25519_SHA512.deal(2, 2).unwrap();
        let dealt_p256 = P256_SHA256.deal(2, 2).unwrap();
        let (_, ed) = SigningNonces::commit(&dealt_ed.signing_shares[0]).unwrap();
        let (_, p256) = SigningNonces::commit(&dealt_p256.signing_shares[0]).unwrap();
        assert_eq!(
            SigningPackage::new(vec![ed, p256], b"frost").unwrap_err(),
            Error::Unsupported
        );
    }
}
