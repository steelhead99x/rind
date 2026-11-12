// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RFC 9591 sections 4 and 5, and the trusted dealer in appendix C, over one
//! ciphersuite's group.

use core::cmp::Ordering;
use core::ops::Deref;

use crate::error::{Error, KeyFormatError};
use crate::low::{Zeroable, ct, ct_equal, zeroise};
use crate::mid::rng::RandomSource;

/// One FROST ciphersuite's group and hash functions.
pub(super) trait Group {
    const CONTEXT: &'static [u8];
    const ELEMENT_LEN: usize;
    const HASH_LEN: usize;
    /// Scalars compare as integers in this byte order.
    const SCALAR_BE: bool;

    /// All-zero bytes are the scalar zero, so a wiped buffer is still a `Scalar`.
    type Scalar: Copy + Zeroable;
    type Element: Clone;

    fn scalar_from_canonical(bytes: &[u8; 32]) -> Option<Self::Scalar>;
    fn scalar_to_bytes(scalar: &Self::Scalar) -> [u8; 32];
    fn scalar_from_u64(value: u64) -> Self::Scalar;
    fn scalar_add(a: &Self::Scalar, b: &Self::Scalar) -> Self::Scalar;
    fn scalar_sub(a: &Self::Scalar, b: &Self::Scalar) -> Self::Scalar;
    fn scalar_mul(a: &Self::Scalar, b: &Self::Scalar) -> Self::Scalar;
    fn scalar_invert(scalar: &Self::Scalar) -> Option<Self::Scalar>;
    /// Public. Callers declassify before branching on a secret scalar.
    fn scalar_is_zero(scalar: &Self::Scalar) -> bool;

    fn random_scalar(rng: &mut dyn RandomSource) -> Result<Self::Scalar, Error>;

    /// `[scalar]B`, or the identity when `scalar` is zero.
    fn base(scalar: &Self::Scalar) -> Option<Self::Element>;
    /// `[scalar]point`, or the identity when `scalar` is zero.
    fn mul(point: &Self::Element, scalar: &Self::Scalar) -> Option<Self::Element>;
    /// `a + b`, or the identity.
    fn add(a: &Self::Element, b: &Self::Element) -> Option<Self::Element>;
    fn equals(a: &Self::Element, b: &Self::Element) -> bool;

    /// The ciphersuite encoding, in the first [`Self::ELEMENT_LEN`] bytes.
    /// The identity is refused.
    fn serialize(point: &Self::Element) -> Result<[u8; 33], Error>;
    fn deserialize(bytes: &[u8]) -> Result<Self::Element, Error>;

    fn h1(msg: &[u8]) -> Result<Self::Scalar, Error>;
    fn h2(msg: &[u8]) -> Result<Self::Scalar, Error>;
    fn h3(msg: &[u8]) -> Result<Self::Scalar, Error>;
    fn h4(msg: &[u8]) -> [u8; 64];
    fn h5(msg: &[u8]) -> [u8; 64];
}

/// One participant's published round-one commitments, already checked.
#[derive(Clone)]
pub(super) struct Party {
    pub identifier: [u8; 32],
    pub hiding: [u8; 33],
    pub binding: [u8; 33],
}

#[derive(Clone, Copy)]
pub(super) struct ShareBytes {
    pub identifier: [u8; 32],
    pub scalar: [u8; 32],
    pub verifying: [u8; 33],
}

impl Zeroable for ShareBytes {}

impl Zeroable for crate::mid::edwards25519::Scalar {}
impl Zeroable for crate::mid::p256::Scalar {}
// Native ristretto255 re-exports edwards25519's scalar. The portable one is its own type.
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
impl Zeroable for crate::mid::ristretto255::Scalar {}

/// Heap buffer of secret `T`, wiped on drop, capacity included.
///
/// `reserve_exact` runs before any secret is written, and `push` stores by
/// index, so the buffer never grows. Growth would free the previous
/// allocation still holding the secret. Drop wipes every byte of the one
/// allocation through `low::zeroise`, which does nothing without `wipe`.
pub(super) struct Wiped<T: Zeroable> {
    values: Vec<T>,
    len: usize,
}

impl<T: Copy + Zeroable> Wiped<T> {
    fn with_capacity(slots: usize, zero: T) -> Self {
        let mut values = Vec::new();
        if slots > 0 {
            values.reserve_exact(slots);
            // The spare slots are the zero `T`, so the allocation is
            // initialized out to its capacity and a later wipe covers it.
            values.resize(values.capacity(), zero);
        }
        Self { values, len: 0 }
    }

    fn push(&mut self, value: T) {
        self.values[self.len] = value;
        self.len += 1;
    }
}

impl<T: Zeroable> Drop for Wiped<T> {
    fn drop(&mut self) {
        zeroise(&mut self.values);
    }
}

impl<T: Zeroable> Deref for Wiped<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.values[..self.len]
    }
}

pub(super) struct Dealt {
    pub shares: Wiped<ShareBytes>,
    pub group: [u8; 33],
}

pub(super) struct NonceBytes {
    pub hiding: [u8; 32],
    pub binding: [u8; 32],
    pub hiding_commitment: [u8; 33],
    pub binding_commitment: [u8; 33],
}

#[derive(Debug)]
pub(super) enum AggFail {
    Failed(Error),
    InvalidShare([u8; 32]),
}

/// `min` of `max` shares of a fresh secret. Identifiers are `1..=max`.
pub(super) fn deal<G: Group>(
    min_signers: u16,
    max_signers: u16,
    rng: &mut dyn RandomSource,
) -> Result<Dealt, Error> {
    if min_signers == 0 || min_signers > max_signers {
        return Err(Error::Unsupported);
    }
    for _ in 0..64 {
        let mut coefficients =
            Wiped::with_capacity(usize::from(min_signers), G::scalar_from_u64(0));
        coefficients.push(G::random_scalar(rng)?);
        for _ in 1..min_signers {
            coefficients.push(G::random_scalar(rng)?);
        }
        if let Some(dealt) = shares_of::<G>(&coefficients, max_signers)? {
            return Ok(dealt);
        }
    }
    Err(Error::RngFailed)
}

/// Appendix C from a fixed secret and the polynomial's higher coefficients.
#[cfg(test)]
pub(super) fn deal_from_coefficients<G: Group>(
    secret: &[u8; 32],
    coefficients: &[[u8; 32]],
    max_signers: u16,
) -> Result<Dealt, Error> {
    if max_signers == 0 {
        return Err(Error::Unsupported);
    }
    let mut polynomial = Wiped::with_capacity(1 + coefficients.len(), G::scalar_from_u64(0));
    polynomial.push(scalar::<G>(secret)?);
    for coefficient in coefficients {
        polynomial.push(scalar::<G>(coefficient)?);
    }
    shares_of::<G>(&polynomial, max_signers)?.ok_or(KeyFormatError::ScalarOutOfRange.into())
}

/// Round one. A zero nonce is drawn again: its commitment would be the identity.
pub(super) fn commit<G: Group>(
    share: &[u8; 32],
    rng: &mut dyn RandomSource,
) -> Result<NonceBytes, Error> {
    let share = load_secret::<G>(share)?;
    for _ in 0..64 {
        let mut hiding_random = [0u8; 32];
        let mut binding_random = [0u8; 32];
        rng.fill(&mut hiding_random)?;
        rng.fill(&mut binding_random)?;
        ct::secret_slice(&hiding_random);
        ct::secret_slice(&binding_random);
        if let Some(nonces) = commit_from_random::<G>(&share, &hiding_random, &binding_random)? {
            return Ok(nonces);
        }
    }
    Err(Error::RngFailed)
}

/// Round one from the two 32-byte strings `nonce_generate` hashes in.
#[cfg(test)]
pub(super) fn commit_with_randomness<G: Group>(
    share: &[u8; 32],
    hiding_random: &[u8; 32],
    binding_random: &[u8; 32],
) -> Result<NonceBytes, Error> {
    let share = load_secret::<G>(share)?;
    ct::secret_slice(hiding_random);
    ct::secret_slice(binding_random);
    commit_from_random::<G>(&share, hiding_random, binding_random)?
        .ok_or(KeyFormatError::ScalarOutOfRange.into())
}

pub(super) fn sign<G: Group>(
    share: &[u8; 32],
    identifier: &[u8; 32],
    min_signers: u16,
    max_signers: u16,
    hiding_nonce: &[u8; 32],
    binding_nonce: &[u8; 32],
    group_public: &[u8],
    parties: &[Party],
    message: &[u8],
) -> Result<[u8; 32], Error> {
    let share = load_secret::<G>(share)?;
    let hiding = load_secret::<G>(hiding_nonce)?;
    let binding = load_secret::<G>(binding_nonce)?;
    check_parties::<G>(parties, min_signers, max_signers)?;
    let mine = parties
        .iter()
        .find(|party| party.identifier == *identifier)
        .ok_or(Error::Unsupported)?;
    let hiding_commitment = write_point::<G>(G::base(&hiding))?;
    let binding_commitment = write_point::<G>(G::base(&binding))?;
    // The recomputed commitment is secret-derived. Whether it is the one this
    // signer published is public.
    if !ct::into_public(ct_equal(
        &hiding_commitment[..G::ELEMENT_LEN],
        &mine.hiding[..G::ELEMENT_LEN],
    )) || !ct::into_public(ct_equal(
        &binding_commitment[..G::ELEMENT_LEN],
        &mine.binding[..G::ELEMENT_LEN],
    )) {
        return Err(KeyFormatError::MismatchedPublicKey.into());
    }

    if group_public.len() != G::ELEMENT_LEN {
        return Err(Error::WrongLength);
    }
    let parsed = parse_parties::<G>(parties)?;
    let factors = binding_factors::<G>(group_public, parties, message)?;
    let rho = factors[mine_index(parties, identifier)?];
    let group_commitment = group_commitment::<G>(&parsed, &factors)?;
    let challenge = challenge::<G>(&group_commitment[..G::ELEMENT_LEN], group_public, message)?;
    let lambda = lagrange::<G>(parties, identifier)?;
    // z = hiding + binding * rho + lambda * sk * c
    let z = G::scalar_add(
        &G::scalar_add(&hiding, &G::scalar_mul(&binding, &rho)),
        &G::scalar_mul(&G::scalar_mul(&lambda, &share), &challenge),
    );
    // The share is sent to the coordinator, so it is public from here.
    let z = G::scalar_to_bytes(&z);
    ct::public_slice(&z);
    Ok(z)
}

#[cfg(test)]
pub(super) fn binding_factor<G: Group>(
    group_public: &[u8],
    parties: &[Party],
    message: &[u8],
    identifier: &[u8; 32],
) -> Result<[u8; 32], Error> {
    let factors = binding_factors::<G>(group_public, parties, message)?;
    Ok(G::scalar_to_bytes(
        &factors[mine_index(parties, identifier)?],
    ))
}

pub(super) fn aggregate<G: Group>(
    group_public: &[u8],
    parties: &[Party],
    message: &[u8],
    shares: &[([u8; 32], [u8; 32])],
    verifying: &[([u8; 32], [u8; 33])],
    min_signers: u16,
    max_signers: u16,
) -> Result<Vec<u8>, AggFail> {
    if group_public.len() != G::ELEMENT_LEN {
        return Err(AggFail::Failed(Error::WrongLength));
    }
    check_parties::<G>(parties, min_signers, max_signers).map_err(AggFail::Failed)?;
    if shares.len() != parties.len() {
        return Err(AggFail::Failed(Error::Unsupported));
    }
    let mut signature_shares = Vec::with_capacity(shares.len());
    for (party, (identifier, share)) in parties.iter().zip(shares) {
        if party.identifier != *identifier {
            return Err(AggFail::Failed(Error::Unsupported));
        }
        let share = G::scalar_from_canonical(share)
            .ok_or(AggFail::Failed(KeyFormatError::ScalarOutOfRange.into()))?;
        signature_shares.push(share);
    }
    let parsed = parse_parties::<G>(parties).map_err(AggFail::Failed)?;
    let factors = binding_factors::<G>(group_public, parties, message).map_err(AggFail::Failed)?;
    let group_commitment = group_commitment::<G>(&parsed, &factors).map_err(AggFail::Failed)?;
    let mut z = G::scalar_from_u64(0);
    for share in &signature_shares {
        z = G::scalar_add(&z, share);
    }
    let z_bytes = G::scalar_to_bytes(&z);
    let mut signature = Vec::with_capacity(G::ELEMENT_LEN + 32);
    signature.extend_from_slice(&group_commitment[..G::ELEMENT_LEN]);
    signature.extend_from_slice(&z_bytes);

    if verify::<G>(group_public, message, &signature).is_ok() {
        return Ok(signature);
    }
    let identifiers: Vec<[u8; 32]> = parties.iter().map(|party| party.identifier).collect();
    for ((party, share), point) in parties.iter().zip(&signature_shares).zip(&parsed) {
        let verifying = verifying
            .iter()
            .find(|(identifier, _)| identifier == &party.identifier)
            .ok_or(AggFail::Failed(Error::Unsupported))?;
        let ok = verify_share::<G>(
            group_public,
            parties,
            message,
            &party.identifier,
            &verifying.1,
            point,
            share,
            &identifiers,
        )
        .map_err(AggFail::Failed)?;
        if !ok {
            return Err(AggFail::InvalidShare(party.identifier));
        }
    }
    Err(AggFail::Failed(Error::BadSignature))
}

pub(super) fn verify<G: Group>(
    group_public: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<(), Error> {
    if signature.len() != G::ELEMENT_LEN + 32 {
        return Err(Error::WrongLength);
    }
    let (encoded_r, encoded_z) = signature.split_at(G::ELEMENT_LEN);
    let r = G::deserialize(encoded_r)?;
    let z = G::scalar_from_canonical(encoded_z.try_into().unwrap())
        .ok_or(KeyFormatError::ScalarOutOfRange)?;
    let pk = G::deserialize(group_public)?;
    let c = challenge::<G>(encoded_r, group_public, message)?;
    // [z]B = R + [c]PK. Ed25519's verifier checks the same equation.
    let left = G::base(&z);
    let right = sum::<G>(Some(r), G::mul(&pk, &c));
    if same::<G>(left, right) {
        Ok(())
    } else {
        Err(Error::BadSignature)
    }
}

fn shares_of<G: Group>(
    coefficients: &[G::Scalar],
    max_signers: u16,
) -> Result<Option<Dealt>, Error> {
    let mut shares = Wiped::with_capacity(
        usize::from(max_signers),
        ShareBytes {
            identifier: [0; 32],
            scalar: [0; 32],
            verifying: [0; 33],
        },
    );
    for identifier in 1..=max_signers {
        let x = G::scalar_from_u64(u64::from(identifier));
        let y = evaluate::<G>(&x, coefficients);
        // A zero share's public key is the identity, which cannot be sent.
        if G::scalar_is_zero(&y) {
            return Ok(None);
        }
        let verifying = write_point::<G>(G::base(&y))?;
        let mut id = [0u8; 32];
        id.copy_from_slice(&G::scalar_to_bytes(&x));
        // The verifying share is published. The signing share stays secret.
        ct::public_slice(&verifying);
        shares.push(ShareBytes {
            identifier: id,
            scalar: G::scalar_to_bytes(&y),
            verifying,
        });
    }
    let group = write_point::<G>(G::base(&coefficients[0]))?;
    ct::public_slice(&group);
    Ok(Some(Dealt { shares, group }))
}

/// Horner's method, highest coefficient first. `coefficients[0]` is `f(0)`.
fn evaluate<G: Group>(x: &G::Scalar, coefficients: &[G::Scalar]) -> G::Scalar {
    let mut value = G::scalar_from_u64(0);
    for coefficient in coefficients.iter().rev() {
        value = G::scalar_add(&G::scalar_mul(&value, x), coefficient);
    }
    value
}

fn commit_from_random<G: Group>(
    share: &G::Scalar,
    hiding_random: &[u8; 32],
    binding_random: &[u8; 32],
) -> Result<Option<NonceBytes>, Error> {
    let hiding = nonce::<G>(share, hiding_random)?;
    let binding = nonce::<G>(share, binding_random)?;
    if G::scalar_is_zero(&hiding) || G::scalar_is_zero(&binding) {
        return Ok(None);
    }
    let hiding_commitment = write_point::<G>(G::base(&hiding))?;
    let binding_commitment = write_point::<G>(G::base(&binding))?;
    // Commitments are sent to the coordinator. The nonces stay secret.
    ct::public_slice(&hiding_commitment);
    ct::public_slice(&binding_commitment);
    Ok(Some(NonceBytes {
        hiding: G::scalar_to_bytes(&hiding),
        binding: G::scalar_to_bytes(&binding),
        hiding_commitment,
        binding_commitment,
    }))
}

/// `H3(random_bytes || SerializeScalar(secret))`.
fn nonce<G: Group>(secret: &G::Scalar, random: &[u8; 32]) -> Result<G::Scalar, Error> {
    let mut input = [0u8; 64];
    input[..32].copy_from_slice(random);
    input[32..].copy_from_slice(&G::scalar_to_bytes(secret));
    G::h3(&input)
}

fn binding_factors<G: Group>(
    group_public: &[u8],
    parties: &[Party],
    message: &[u8],
) -> Result<Vec<G::Scalar>, Error> {
    let msg_hash = G::h4(message);
    let commitment_hash = G::h5(&encode_commitments::<G>(parties));
    let mut prefix = Vec::with_capacity(group_public.len() + G::HASH_LEN * 2);
    prefix.extend_from_slice(group_public);
    prefix.extend_from_slice(&msg_hash[..G::HASH_LEN]);
    prefix.extend_from_slice(&commitment_hash[..G::HASH_LEN]);
    let mut factors = Vec::with_capacity(parties.len());
    for party in parties {
        let mut input = prefix.clone();
        input.extend_from_slice(&party.identifier);
        factors.push(G::h1(&input)?);
    }
    Ok(factors)
}

fn encode_commitments<G: Group>(parties: &[Party]) -> Vec<u8> {
    let mut out = Vec::with_capacity(parties.len() * (32 + G::ELEMENT_LEN * 2));
    for party in parties {
        out.extend_from_slice(&party.identifier);
        out.extend_from_slice(&party.hiding[..G::ELEMENT_LEN]);
        out.extend_from_slice(&party.binding[..G::ELEMENT_LEN]);
    }
    out
}

fn group_commitment<G: Group>(
    parties: &[Parsed<G>],
    factors: &[G::Scalar],
) -> Result<[u8; 33], Error> {
    let mut acc = None;
    for (party, factor) in parties.iter().zip(factors) {
        acc = sum::<G>(acc, Some(party.hiding.clone()));
        acc = sum::<G>(acc, G::mul(&party.binding, factor));
    }
    write_point::<G>(acc)
}

fn challenge<G: Group>(
    group_commitment: &[u8],
    group_public: &[u8],
    message: &[u8],
) -> Result<G::Scalar, Error> {
    let mut input = Vec::with_capacity(group_commitment.len() + group_public.len() + message.len());
    input.extend_from_slice(group_commitment);
    input.extend_from_slice(group_public);
    input.extend_from_slice(message);
    G::h2(&input)
}

/// `derive_interpolating_value` at `identifier`, over `parties`' identifiers.
fn lagrange<G: Group>(parties: &[Party], identifier: &[u8; 32]) -> Result<G::Scalar, Error> {
    let x_i = scalar::<G>(identifier)?;
    let mut numerator = G::scalar_from_u64(1);
    let mut denominator = G::scalar_from_u64(1);
    for party in parties {
        if party.identifier == *identifier {
            continue;
        }
        let x_j = scalar::<G>(&party.identifier)?;
        numerator = G::scalar_mul(&numerator, &x_j);
        denominator = G::scalar_mul(&denominator, &G::scalar_sub(&x_j, &x_i));
    }
    let inverse = G::scalar_invert(&denominator).ok_or(Error::Fault)?;
    Ok(G::scalar_mul(&numerator, &inverse))
}

struct Parsed<G: Group> {
    hiding: G::Element,
    binding: G::Element,
}

fn parse_parties<G: Group>(parties: &[Party]) -> Result<Vec<Parsed<G>>, Error> {
    let mut parsed = Vec::with_capacity(parties.len());
    for party in parties {
        parsed.push(Parsed {
            hiding: G::deserialize(&party.hiding[..G::ELEMENT_LEN])?,
            binding: G::deserialize(&party.binding[..G::ELEMENT_LEN])?,
        });
    }
    Ok(parsed)
}

fn verify_share<G: Group>(
    group_public: &[u8],
    parties: &[Party],
    message: &[u8],
    identifier: &[u8; 32],
    verifying_share: &[u8],
    commitments: &Parsed<G>,
    share: &G::Scalar,
    identifiers: &[[u8; 32]],
) -> Result<bool, Error> {
    let _ = identifiers;
    let factors = binding_factors::<G>(group_public, parties, message)?;
    let rho = factors[mine_index(parties, identifier)?];
    let group_commitment = group_commitment::<G>(&parse_parties::<G>(parties)?, &factors)?;
    let challenge = challenge::<G>(&group_commitment[..G::ELEMENT_LEN], group_public, message)?;
    let lambda = lagrange::<G>(parties, identifier)?;
    if verifying_share.len() < G::ELEMENT_LEN {
        return Err(Error::WrongLength);
    }
    let pk = G::deserialize(&verifying_share[..G::ELEMENT_LEN])?;
    let comm = sum::<G>(
        Some(commitments.hiding.clone()),
        G::mul(&commitments.binding, &rho),
    );
    let right = sum::<G>(comm, G::mul(&pk, &G::scalar_mul(&challenge, &lambda)));
    Ok(same::<G>(G::base(share), right))
}

fn check_parties<G: Group>(
    parties: &[Party],
    min_signers: u16,
    max_signers: u16,
) -> Result<(), Error> {
    if parties.is_empty()
        || parties.len() < usize::from(min_signers)
        || parties.len() > usize::from(max_signers)
    {
        return Err(Error::Unsupported);
    }
    let mut previous: Option<&[u8; 32]> = None;
    for party in parties {
        let identifier = identifier_value::<G>(&party.identifier)?;
        if identifier == 0 || identifier > max_signers {
            return Err(KeyFormatError::ScalarOutOfRange.into());
        }
        if let Some(previous) = previous
            && cmp_identifiers::<G>(previous, &party.identifier) != Ordering::Less
        {
            return Err(Error::Unsupported);
        }
        previous = Some(&party.identifier);
        // Reject an element encoding before any secret is combined with it.
        G::deserialize(&party.hiding[..G::ELEMENT_LEN])?;
        G::deserialize(&party.binding[..G::ELEMENT_LEN])?;
    }
    Ok(())
}

pub(super) fn validate_party<G: Group>(party: &Party) -> Result<(), Error> {
    if identifier_value::<G>(&party.identifier)? == 0 {
        return Err(KeyFormatError::ScalarOutOfRange.into());
    }
    G::deserialize(&party.hiding[..G::ELEMENT_LEN])?;
    G::deserialize(&party.binding[..G::ELEMENT_LEN])?;
    Ok(())
}

fn identifier_value<G: Group>(bytes: &[u8; 32]) -> Result<u16, Error> {
    // Parsing also rejects a non-canonical scalar, including zero only when
    // the integer is zero.
    if G::scalar_from_canonical(bytes).is_none() {
        return Err(KeyFormatError::ScalarOutOfRange.into());
    }
    let value = if G::SCALAR_BE {
        if bytes[..30].iter().any(|byte| *byte != 0) {
            return Err(KeyFormatError::ScalarOutOfRange.into());
        }
        u16::from_be_bytes([bytes[30], bytes[31]])
    } else {
        if bytes[2..].iter().any(|byte| *byte != 0) {
            return Err(KeyFormatError::ScalarOutOfRange.into());
        }
        u16::from_le_bytes([bytes[0], bytes[1]])
    };
    Ok(value)
}

pub(super) fn cmp_identifiers<G: Group>(a: &[u8; 32], b: &[u8; 32]) -> Ordering {
    if G::SCALAR_BE {
        a.cmp(b)
    } else {
        a.iter().rev().cmp(b.iter().rev())
    }
}

fn mine_index(parties: &[Party], identifier: &[u8; 32]) -> Result<usize, Error> {
    parties
        .iter()
        .position(|party| party.identifier == *identifier)
        .ok_or(Error::Unsupported)
}

fn scalar<G: Group>(bytes: &[u8; 32]) -> Result<G::Scalar, Error> {
    G::scalar_from_canonical(bytes).ok_or(KeyFormatError::ScalarOutOfRange.into())
}

fn load_secret<G: Group>(bytes: &[u8; 32]) -> Result<G::Scalar, Error> {
    ct::secret_slice(bytes);
    scalar::<G>(bytes)
}

fn write_point<G: Group>(point: Option<G::Element>) -> Result<[u8; 33], Error> {
    match point {
        Some(point) => G::serialize(&point),
        None => Err(KeyFormatError::SmallOrder.into()),
    }
}

fn sum<G: Group>(left: Option<G::Element>, right: Option<G::Element>) -> Option<G::Element> {
    match (left, right) {
        (None, point) | (point, None) => point,
        (Some(left), Some(right)) => G::add(&left, &right),
    }
}

fn same<G: Group>(left: Option<G::Element>, right: Option<G::Element>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => G::equals(&left, &right),
        _ => false,
    }
}
