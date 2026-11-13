// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RFC 9497's VOPRF mode: the OPRF, with the server proving it evaluated
//! every blinded element in a batch with the key it published.

#[cfg(target_os = "none")]
use alloc::vec::Vec;
use core::fmt;

use super::{
    Bytes, ClientState, Group, Key, KeyInner, MAX_ELEMENT, MAX_OUTPUT, MAX_SCALAR, Mode, Output,
    P256, P384, P521, Pick, Ristretto255, ServerKeyBytes, Suite, SuiteId, decode, derive_scalar,
    dispatch, encode, hash_to_scalar, identity, len_prefix, scalar_bytes, scalar_from_key, suited,
    with_group,
};
use crate::error::Error;
use crate::low::{self, Entry, ct};
use crate::mid::hash_to_curve::Xmd;

/// The most elements one proof covers: RFC 9497 2.2.1 numbers them with
/// `I2OSP(i, 2)`.
const MAX_BATCH: usize = 1 << 16;

/// The longest proof, P-521's two scalars.
const MAX_PROOF: usize = 2 * MAX_SCALAR;

/// The server's public key `pkS`, held with its encoding.
pub(super) struct Public<G: Group> {
    element: G::Element,
    bytes: Bytes<MAX_ELEMENT>,
}

impl<G: Group> Public<G> {
    fn suite(&self) -> &'static Suite {
        G::suite()
    }

    /// The public key of the private key `k`, made public.
    fn of(k: &G::Scalar) -> Self {
        let element = ct::into_public(G::mul_base(k));
        Self {
            element,
            bytes: ct::into_public(encode::<G>(&element)),
        }
    }
}

impl<G: Group> Clone for Public<G> {
    fn clone(&self) -> Self {
        Self {
            element: self.element,
            bytes: self.bytes.clone(),
        }
    }
}

suited!(
    /// A server's public key, for one suite.
    #[derive(Clone)]
    pub(super) enum PublicInner(Public)
);

/// A client's state for the VOPRF: the OPRF's, and the blinded element the
/// server's proof covers.
pub(super) struct VerifiableState<G: Group> {
    state: ClientState<G>,
    blinded: G::Element,
    encoded: Bytes<MAX_ELEMENT>,
}

impl<G: Group> VerifiableState<G> {
    fn suite(&self) -> &'static Suite {
        G::suite()
    }
}

suited!(
    /// A client's state, for one suite.
    pub(super) enum BlindInner(VerifiableState)
);

/// The server's key in the VOPRF mode, which evaluates blinded elements
/// for clients and proves it used the key it published, wiped on drop
/// under the `wipe` feature.
///
/// It keeps its public key, computed once when it is generated or loaded.
/// Its outputs differ from an [`oprf::ServerKey`](super::ServerKey)'s with
/// the same scalar, as RFC 9497 separates the modes.
pub struct ServerKey {
    key: KeyInner,
    public: PublicKey,
}

impl ServerKey {
    /// Generates a key for `suite` from the system random source.
    pub fn generate(suite: &'static Suite) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        with_group!(suite, G => Ok(Self::new(Key::<G> { k: G::random_scalar()? })))
    }

    /// Derives a key for `suite` from `seed` and the public `info`, by RFC
    /// 9497 section 3.2.1's `DeriveKeyPair`.
    ///
    /// RFC 9497 calls for a 32-byte seed from a secure random source; RFC
    /// 9807's OPAQUE derives one per user. An `info` of `2^16 - 1` bytes or
    /// more is refused with [`Error::WrongLength`].
    pub fn derive(suite: &'static Suite, seed: &[u8], info: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        with_group!(suite, G => Ok(Self::new(Key::<G> {
            k: derive_scalar::<G>(Mode::Voprf, seed, info)?,
        })))
    }

    /// Loads a key for `suite` from its `SerializeScalar` encoding, refused
    /// unless it is from 1 to the group order less one.
    pub fn from_bytes(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        with_group!(suite, G => Ok(Self::new(Key::<G> { k: scalar_from_key::<G>(bytes)? })))
    }

    fn new<G: Group>(key: Key<G>) -> Self
    where
        KeyInner: From<Key<G>>,
        PublicInner: From<Public<G>>,
    {
        let public = PublicKey(Public::<G>::of(&key.k).into());
        Self {
            key: key.into(),
            public,
        }
    }

    /// Encodes the key as [`Self::from_bytes`] loads it.
    pub fn to_bytes(&self) -> ServerKeyBytes {
        dispatch!(KeyInner, &self.key, key => key.to_bytes())
    }

    /// Returns the key's public key, which clients verify proofs with.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }

    /// Returns the key's suite.
    pub fn suite(&self) -> &'static Suite {
        self.key.suite()
    }

    /// Evaluates a batch of blinded elements, one or more concatenated, by
    /// RFC 9497 3.3.2's `BlindEvaluate`, or its batched form in 3.3.2.1,
    /// returning the evaluated elements, concatenated in the same order,
    /// and one proof covering all of them.
    ///
    /// A batch that is empty, holds more than 65536 elements, or is not a
    /// whole number of elements is refused with [`Error::WrongLength`], and
    /// one with an element that does not decode, or is the identity, with
    /// [`Error::KeyRejected`].
    pub fn blind_evaluate(
        &self,
        blinded_elements: &[u8],
    ) -> Result<(EvaluatedElements, Proof), Error> {
        let _entry = Entry::new_secret();
        dispatch!(KeyInner, &self.key, key => key.blind_evaluate(&self.public.0, blinded_elements))
    }

    /// Computes the output for `input` directly, by RFC 9497's `Evaluate`,
    /// as a client that blinds `input` would finalize it.
    ///
    /// An `input` of `2^16 - 1` bytes or more is refused with
    /// [`Error::WrongLength`].
    pub fn evaluate(&self, input: &[u8]) -> Result<Output, Error> {
        let _entry = Entry::new_secret();
        dispatch!(KeyInner, &self.key, key => key.evaluate(Mode::Voprf, input))
    }
}

impl<G: Group> Key<G> {
    /// `BlindEvaluate`, proving with a random nonce.
    fn blind_evaluate(
        &self,
        public: &PublicInner,
        blinded_elements: &[u8],
    ) -> Result<(EvaluatedElements, Proof), Error>
    where
        PublicInner: Pick<Public<G>>,
    {
        let public = public
            .pick()
            .expect("a key keeps its own suite's public key");
        self.blind_evaluate_with(public, blinded_elements, G::random_scalar()?)
    }

    /// `BlindEvaluate`, proving with the nonce `r`.
    fn blind_evaluate_with(
        &self,
        public: &Public<G>,
        blinded_elements: &[u8],
        r: G::Scalar,
    ) -> Result<(EvaluatedElements, Proof), Error> {
        let blinded = decode_batch::<G>(blinded_elements)?;
        let mut evaluated = Vec::with_capacity(blinded.len());
        let mut encoded = Vec::with_capacity(blinded_elements.len());
        for element in &blinded {
            let element = ct::into_public(G::mul(element, &self.k));
            encoded.extend_from_slice(ct::into_public(encode::<G>(&element)).as_ref());
            evaluated.push(element);
        }
        let proof = prove::<G>(
            &self.k,
            public,
            &blinded,
            blinded_elements,
            &evaluated,
            &encoded,
            r,
        )?;
        Ok((EvaluatedElements(encoded), proof))
    }
}

impl Drop for ServerKey {
    fn drop(&mut self) {
        // The public key is not secret, but a key type wipes its whole value.
        low::zeroise_value(self);
    }
}

impl low::Zeroable for ServerKey {}

impl fmt::Debug for ServerKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ServerKey")
            .field("suite", self.suite())
            .field("public_key", &self.public)
            .finish_non_exhaustive()
    }
}

/// A server's public key, which clients verify its proofs with.
#[derive(Clone)]
pub struct PublicKey(PublicInner);

impl PublicKey {
    /// Parses a server's public key for `suite`, by RFC 9497's
    /// `DeserializeElement`.
    ///
    /// A key that does not decode, or is the identity, is refused with
    /// [`Error::KeyRejected`].
    pub fn new(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        with_group!(suite, G => {
            let element = decode::<G>(bytes)?;
            Ok(Self(Public::<G> { element, bytes: encode::<G>(&element) }.into()))
        })
    }

    /// Returns the key's suite.
    pub fn suite(&self) -> &'static Suite {
        self.0.suite()
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        dispatch!(PublicInner, &self.0, public => public.bytes.as_ref())
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PublicKey").field(&self.as_ref()).finish()
    }
}

/// A client's secret for one input in the VOPRF mode, which verifies the
/// server's proof and turns its evaluated element into the output, wiped
/// on drop under the `wipe` feature.
pub struct Blind(BlindInner);

impl Blind {
    /// Blinds `input` for `suite` by RFC 9497 3.3.1's `Blind`, returning the
    /// blind to keep and the blinded element to send the server.
    ///
    /// Blinded elements for one server can go in one batch, concatenated,
    /// which one proof covers.
    ///
    /// An `input` of `2^16 - 1` bytes or more is refused with
    /// [`Error::WrongLength`].
    pub fn new(
        suite: &'static Suite,
        input: &[u8],
    ) -> Result<(Self, super::BlindedElement), Error> {
        let _entry = Entry::new_secret();
        with_group!(suite, G => {
            let (blind, blinded) = VerifiableState::<G>::new(input, G::random_scalar()?)?;
            Ok((Self(blind.into()), blinded))
        })
    }

    /// Verifies the server's proof for its evaluated element, then finalizes
    /// it into the output for the blinded input, by RFC 9497 3.3.2's
    /// `Finalize`.
    ///
    /// A proof that does not verify against `public_key` is refused with
    /// [`Error::BadSignature`], an element that does not decode, or is the
    /// identity, with [`Error::KeyRejected`], and a public key for another
    /// suite with [`Error::Unsupported`]. The element is read as a batch of
    /// one, so one of the wrong length is refused as a batch of the wrong
    /// length, with [`Error::WrongLength`].
    pub fn finalize(
        self,
        evaluated_element: &[u8],
        proof: &[u8],
        public_key: &PublicKey,
    ) -> Result<Output, Error> {
        let mut outputs = Self::finalize_batch(vec![self], evaluated_element, proof, public_key)?;
        Ok(outputs.remove(0))
    }

    /// Verifies the server's one proof for a batch, then finalizes each
    /// evaluated element into its input's output, by RFC 9497 3.3.2.1's
    /// batched `Finalize`.
    ///
    /// `blinds` and the elements of `evaluated_elements` are in the order
    /// the blinded elements went to the server. A batch whose length does
    /// not match `blinds` is refused with [`Error::WrongLength`]; otherwise
    /// as [`Self::finalize`].
    pub fn finalize_batch(
        blinds: Vec<Self>,
        evaluated_elements: &[u8],
        proof: &[u8],
        public_key: &PublicKey,
    ) -> Result<Vec<Output>, Error> {
        let _entry = Entry::new_secret();
        dispatch!(PublicInner, &public_key.0, public => {
            finalize_batch(&blinds, evaluated_elements, proof, public)
        })
    }

    /// Returns the blind's suite.
    pub fn suite(&self) -> &'static Suite {
        self.0.suite()
    }
}

impl<G: Group> VerifiableState<G> {
    /// `Blind(input)` with the scalar `blind`.
    fn new(input: &[u8], blind: G::Scalar) -> Result<(Self, super::BlindedElement), Error> {
        let (state, blinded, encoded) = ClientState::<G>::blind(Mode::Voprf, input, blind)?;
        let element = super::BlindedElement(encoded.clone());
        Ok((
            Self {
                state,
                blinded,
                encoded,
            },
            element,
        ))
    }
}

/// The batched `Finalize`, for blinds of `public`'s suite.
fn finalize_batch<G: Group>(
    blinds: &[Blind],
    evaluated_elements: &[u8],
    proof: &[u8],
    public: &Public<G>,
) -> Result<Vec<Output>, Error>
where
    BlindInner: Pick<VerifiableState<G>>,
{
    let states = blinds
        .iter()
        .map(|blind| blind.0.pick().ok_or(Error::Unsupported))
        .collect::<Result<Vec<_>, _>>()?;
    // Refuse a wrong count before paying a decompression per element.
    if evaluated_elements.len() != states.len() * G::ELEMENT_LEN {
        return Err(Error::WrongLength);
    }
    let evaluated = decode_batch::<G>(evaluated_elements)?;
    let blinded = states.iter().map(|state| state.blinded).collect::<Vec<_>>();
    let mut blinded_bytes = Vec::with_capacity(evaluated_elements.len());
    for state in &states {
        blinded_bytes.extend_from_slice(state.encoded.as_ref());
    }
    verify::<G>(
        public,
        &blinded,
        &blinded_bytes,
        &evaluated,
        evaluated_elements,
        proof,
    )?;
    Ok(states
        .iter()
        .zip(&evaluated)
        .map(|(state, element)| state.state.finalize(element))
        .collect())
}

impl Drop for Blind {
    fn drop(&mut self) {
        // The hash holds the client's input.
        low::zeroise_value(self);
    }
}

impl low::Zeroable for Blind {}

impl fmt::Debug for Blind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Blind")
            .field("suite", self.suite())
            .finish_non_exhaustive()
    }
}

/// A batch of evaluated elements, concatenated, which the server returns to
/// the client with its proof.
#[derive(Clone)]
pub struct EvaluatedElements(Vec<u8>);

impl AsRef<[u8]> for EvaluatedElements {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for EvaluatedElements {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("EvaluatedElements")
            .field(&self.as_ref())
            .finish()
    }
}

/// A proof that the server evaluated a batch with its published key: the
/// challenge and response scalars, concatenated.
#[derive(Clone)]
pub struct Proof(Bytes<MAX_PROOF>);

impl AsRef<[u8]> for Proof {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Proof").field(&self.as_ref()).finish()
    }
}

/// Decodes a batch of 1 to [`MAX_BATCH`] concatenated elements.
fn decode_batch<G: Group>(bytes: &[u8]) -> Result<Vec<G::Element>, Error> {
    if bytes.is_empty()
        || !bytes.len().is_multiple_of(G::ELEMENT_LEN)
        || bytes.len() / G::ELEMENT_LEN > MAX_BATCH
    {
        return Err(Error::WrongLength);
    }
    // A loop over the count, not `chunks`, whose size hint divides by the
    // element length at run time, which `admin/ct-vartime` refuses.
    let count = bytes.len() / G::ELEMENT_LEN;
    let mut elements = Vec::with_capacity(count);
    for i in 0..count {
        elements.push(decode::<G>(
            &bytes[i * G::ELEMENT_LEN..(i + 1) * G::ELEMENT_LEN],
        )?);
    }
    Ok(elements)
}

/// RFC 9497 2.2.1's composite weights `d_i` for the blinded elements `C_i`
/// and evaluated elements `D_i`, concatenated in `blinded` and `evaluated`.
fn composite_weights<G: Group>(
    public: &Public<G>,
    blinded: &[u8],
    evaluated: &[u8],
) -> Result<Vec<G::Scalar>, Error> {
    let dst = super::Dst::new::<G>(b"Seed-", Mode::Voprf);
    let mut hash = G::Hash::new();
    let public = public.bytes.as_ref();
    hash.update(&len_prefix(public));
    hash.update(public);
    hash.update(&len_prefix(dst.as_ref()));
    hash.update(dst.as_ref());
    let mut seed = [0u8; MAX_OUTPUT];
    hash.finish_into(&mut seed);
    let seed = &seed[..G::Hash::OUTPUT];

    // As in `decode_batch`, a loop over the count rather than `chunks`.
    let count = blinded.len() / G::ELEMENT_LEN;
    (0..count)
        .map(|i| {
            let range = i * G::ELEMENT_LEN..(i + 1) * G::ELEMENT_LEN;
            let (c, d) = (&blinded[range.clone()], &evaluated[range]);
            // `decode_batch` bounds the batch at 2^16 elements.
            let i = (i as u16).to_be_bytes();
            hash_to_scalar::<G>(
                Mode::Voprf,
                &[
                    &len_prefix(seed),
                    seed,
                    &i,
                    &len_prefix(c),
                    c,
                    &len_prefix(d),
                    d,
                    b"Composite",
                ],
            )
        })
        .collect()
}

/// RFC 9497 2.2.1's challenge `c` over `M`, `Z`, `t2`, and `t3`.
fn challenge<G: Group>(
    public: &Public<G>,
    [m, z, t2, t3]: [&G::Element; 4],
) -> Result<G::Scalar, Error> {
    let public = public.bytes.as_ref();
    let [m, z, t2, t3] = [m, z, t2, t3].map(encode::<G>);
    let [m, z, t2, t3] = [m.as_ref(), z.as_ref(), t2.as_ref(), t3.as_ref()];
    hash_to_scalar::<G>(
        Mode::Voprf,
        &[
            &len_prefix(public),
            public,
            &len_prefix(m),
            m,
            &len_prefix(z),
            z,
            &len_prefix(t2),
            t2,
            &len_prefix(t3),
            t3,
            b"Challenge",
        ],
    )
}

/// RFC 9497 2.2.1's `GenerateProof` with the nonce `r`, for `D_i = k C_i`,
/// with `ComputeCompositesFast`.
///
/// The composite `M` comes from public elements, and is public; `Z = k M`,
/// `t2`, and `t3` run in constant time.
fn prove<G: Group>(
    k: &G::Scalar,
    public: &Public<G>,
    blinded: &[G::Element],
    blinded_bytes: &[u8],
    evaluated: &[G::Element],
    evaluated_bytes: &[u8],
    r: G::Scalar,
) -> Result<Proof, Error> {
    debug_assert_eq!(blinded.len(), evaluated.len());
    let weights = composite_weights::<G>(public, blinded_bytes, evaluated_bytes)?;
    // `M` is the identity with a chance of about 2^-252 for any batch.
    let m = G::public_mul_sum(blinded.iter().zip(&weights)).ok_or_else(identity)?;
    let z = G::mul(&m, k);
    let t2 = G::mul_base(&r);
    let t3 = G::mul(&m, &r);
    let c = challenge::<G>(public, [&m, &z, &t2, &t3])?;
    let s = G::mul_add(&G::neg(&c), k, &r);

    let mut proof = Bytes::zeroed(2 * G::SCALAR_LEN);
    let (c_bytes, s_bytes) = proof.as_mut().split_at_mut(G::SCALAR_LEN);
    G::scalar_to_bytes(&c, c_bytes);
    G::scalar_to_bytes(&s, s_bytes);
    Ok(Proof(ct::into_public(proof)))
}

/// RFC 9497 2.2.2's `VerifyProof` of `proof` for `D_i = k C_i`, with `k`
/// `public`'s private key. Every value is public, so this runs in variable
/// time.
fn verify<G: Group>(
    public: &Public<G>,
    blinded: &[G::Element],
    blinded_bytes: &[u8],
    evaluated: &[G::Element],
    evaluated_bytes: &[u8],
    proof: &[u8],
) -> Result<(), Error> {
    if proof.len() != 2 * G::SCALAR_LEN {
        return Err(Error::BadSignature);
    }
    let (c_bytes, s_bytes) = proof.split_at(G::SCALAR_LEN);
    let c = G::scalar_from_bytes(c_bytes).ok_or(Error::BadSignature)?;
    let s = G::scalar_from_bytes(s_bytes).ok_or(Error::BadSignature)?;

    let weights = composite_weights::<G>(public, blinded_bytes, evaluated_bytes)?;
    let m = G::public_mul_sum(blinded.iter().zip(&weights)).ok_or(Error::BadSignature)?;
    let z = G::public_mul_sum(evaluated.iter().zip(&weights)).ok_or(Error::BadSignature)?;
    let t2 = G::public_mul_base_add(&s, &public.element, &c).ok_or(Error::BadSignature)?;
    let t3 = G::public_mul_sum([(&m, &s), (&z, &c)]).ok_or(Error::BadSignature)?;
    let expected = challenge::<G>(public, [&m, &z, &t2, &t3])?;
    match scalar_bytes::<G>(&expected).as_ref() == c_bytes {
        true => Ok(()),
        false => Err(Error::BadSignature),
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests;
