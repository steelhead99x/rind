// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SPAKE2+ on P-256 (RFC 9383 and Matter's draft-01 key schedule).
//!
//! Every function here is `#[inline]`, and [`RFC9383`] and [`MATTER_PASE`] are
//! consts. At opt-level above zero an inlined function is a local copy, and a
//! const is not an object, so this module adds nothing for the compiler to
//! place in a codegen unit. A function that is not inlined, a derived method,
//! or a static would be its own object and the compiler would merge the
//! crate's units differently. That merge is what changed the code of AES-CBC
//! and P-256, which this module does not call.

use core::fmt;
use core::marker::PhantomData;

use super::{digest, hkdf, hmac};
use crate::error::Error;
use crate::low::{Entry, Zeroable, ct, ct_equal, zeroise_value};
use crate::mid::p256::{Affine, Scalar};
use crate::mid::rng::{RandomSource, SystemRandom};

/// How many bytes of context or identity one side may pass.
const MAX_LABEL: usize = 1024;

/// RFC 9383's P-256 point M, SEC1 compressed. The handshake uses the
/// uncompressed form; this is what the unit test checks that form against.
#[cfg(test)]
const M_COMPRESSED: [u8; 33] = [
    0x02, 0x88, 0x6e, 0x2f, 0x97, 0xac, 0xe4, 0x6e, 0x55, 0xba, 0x9d, 0xd7, 0x24, 0x25, 0x79, 0xf2,
    0x99, 0x3b, 0x64, 0xe1, 0x6e, 0xf3, 0xdc, 0xab, 0x95, 0xaf, 0xd4, 0x97, 0x33, 0x3d, 0x8f, 0xa1,
    0x2f,
];

/// RFC 9383's P-256 point N, SEC1 compressed.
#[cfg(test)]
const N_COMPRESSED: [u8; 33] = [
    0x03, 0xd8, 0xbb, 0xd6, 0xc6, 0x39, 0xc6, 0x29, 0x37, 0xb0, 0x4d, 0x99, 0x7f, 0x38, 0xc3, 0x77,
    0x07, 0x19, 0xc6, 0x29, 0xd7, 0x01, 0x4d, 0x49, 0xa2, 0x4b, 0x4f, 0x98, 0xba, 0xa1, 0x29, 0x2b,
    0x49,
];

/// M, uncompressed. Decompression is a square root; the handshake should not
/// repeat it.
const M_UNCOMPRESSED: [u8; 65] = [
    0x04, 0x88, 0x6e, 0x2f, 0x97, 0xac, 0xe4, 0x6e, 0x55, 0xba, 0x9d, 0xd7, 0x24, 0x25, 0x79, 0xf2,
    0x99, 0x3b, 0x64, 0xe1, 0x6e, 0xf3, 0xdc, 0xab, 0x95, 0xaf, 0xd4, 0x97, 0x33, 0x3d, 0x8f, 0xa1,
    0x2f, 0x5f, 0xf3, 0x55, 0x16, 0x3e, 0x43, 0xce, 0x22, 0x4e, 0x0b, 0x0e, 0x65, 0xff, 0x02, 0xac,
    0x8e, 0x5c, 0x7b, 0xe0, 0x94, 0x19, 0xc7, 0x85, 0xe0, 0xca, 0x54, 0x7d, 0x55, 0xa1, 0x2e, 0x2d,
    0x20,
];

/// N, uncompressed.
const N_UNCOMPRESSED: [u8; 65] = [
    0x04, 0xd8, 0xbb, 0xd6, 0xc6, 0x39, 0xc6, 0x29, 0x37, 0xb0, 0x4d, 0x99, 0x7f, 0x38, 0xc3, 0x77,
    0x07, 0x19, 0xc6, 0x29, 0xd7, 0x01, 0x4d, 0x49, 0xa2, 0x4b, 0x4f, 0x98, 0xba, 0xa1, 0x29, 0x2b,
    0x49, 0x07, 0xd6, 0x0a, 0xa6, 0xbf, 0xad, 0xe4, 0x50, 0x08, 0xa6, 0x36, 0x33, 0x7f, 0x51, 0x68,
    0xc6, 0x4d, 0x9b, 0xd3, 0x60, 0x34, 0x80, 0x8c, 0xd5, 0x64, 0x49, 0x0b, 0x1e, 0x65, 0x6e, 0xdb,
    0xe7,
];

/// Which key schedule a [`Suite`] runs. The transcript is the same for both.
#[derive(Copy)]
enum Schedule {
    /// RFC 9383: HKDF over the whole transcript hash.
    Rfc9383,
    /// draft-bar-cfrg-spake2plus-01: the transcript hash splits into Ka and Ke.
    Draft01,
}

// Not derived: see the module docs. `derivable_impls` wants `#[derive(Clone)]`,
// which would emit a separate object.
#[allow(clippy::derivable_impls)]
impl Clone for Schedule {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl fmt::Debug for Schedule {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Rfc9383 => "Rfc9383",
            Self::Draft01 => "Draft01",
        })
    }
}

/// Marker for [`RFC9383`]. A [`Share`] or [`Confirm`] of this suite is not a
/// [`MatterPase`] value, so a mixed handshake does not compile.
#[derive(Copy)]
pub struct Rfc9383;

/// Marker for [`MATTER_PASE`].
#[derive(Copy)]
pub struct MatterPase;

// Not derived: see the module docs.
#[allow(clippy::derivable_impls)]
impl Clone for Rfc9383 {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

#[allow(clippy::derivable_impls)]
impl PartialEq for Rfc9383 {
    #[inline]
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for Rfc9383 {}

impl fmt::Debug for Rfc9383 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Rfc9383")
    }
}

#[allow(clippy::derivable_impls)]
impl Clone for MatterPase {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

#[allow(clippy::derivable_impls)]
impl PartialEq for MatterPase {
    #[inline]
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for MatterPase {}

impl fmt::Debug for MatterPase {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("MatterPase")
    }
}

/// A SPAKE2+ ciphersuite. Only this module's constants build one.
///
/// `S` is [`Rfc9383`] or [`MatterPase`]. The two schedules do not share a
/// [`Share`] or a [`Confirm`].
///
/// ```compile_fail
/// use rind::spake2plus::{MATTER_PASE, ProverSecrets, RFC9383, VerifierRecord};
/// let w0 = [0x11; 40];
/// let w1 = [0x22; 40];
/// let (share_p, _) = ProverSecrets::new(&w0, &w1)
///     .unwrap()
///     .start(&RFC9383, b"app", b"a", b"b")
///     .unwrap();
/// let _ = VerifierRecord::from_w1(&w0, &w1)
///     .unwrap()
///     .start(&MATTER_PASE, b"app", b"a", b"b", &share_p);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Suite<S> {
    schedule: Schedule,
    _kind: PhantomData<fn() -> S>,
}

/// RFC 9383's P-256, SHA-256, HKDF-SHA256, HMAC-SHA256 suite.
pub const RFC9383: Suite<Rfc9383> = Suite {
    schedule: Schedule::Rfc9383,
    _kind: PhantomData,
};

/// Matter PASE: draft-bar-cfrg-spake2plus-01's P-256 SHA-256 suite.
///
/// The group operations, M, N, and the transcript match [`RFC9383`]. The key
/// schedule splits the transcript hash instead of feeding it to HKDF.
///
/// Matter's context is SHA-256 over "CHIP PAKE V1 Commissioning", the
/// PBKDFParamRequest, and the PBKDFParamResponse, and both identities are
/// empty.
pub const MATTER_PASE: Suite<MatterPase> = Suite {
    schedule: Schedule::Draft01,
    _kind: PhantomData,
};

/// A party's share, an uncompressed P-256 point of suite `S`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Share<S> {
    bytes: [u8; Affine::BYTES],
    _kind: PhantomData<fn() -> S>,
}

impl<S> Share<S> {
    /// The length of an uncompressed share, 65 bytes.
    pub const BYTES: usize = Affine::BYTES;

    /// Decodes `bytes` as an uncompressed point on the curve.
    ///
    /// Fails with [`Error::KeyRejected`] when `bytes` is not that encoding of
    /// a point on P-256.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        // The decoder refuses a coordinate at or above p, so each point has
        // one encoding and `bytes` is it.
        let point = Affine::from_uncompressed(bytes)?;
        Ok(Self {
            bytes: point.to_uncompressed(),
            _kind: PhantomData,
        })
    }
}

impl<S> AsRef<[u8]> for Share<S> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl<S> fmt::Debug for Share<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Share").field(&self.bytes).finish()
    }
}

/// A key-confirmation tag, the 32-byte HMAC-SHA256 of suite `S`.
///
/// Equality reads every byte and declassifies only whether the tags match,
/// as [`crate::constant_time::verify`] does.
#[derive(Clone, Copy, Eq)]
pub struct Confirm<S> {
    bytes: [u8; 32],
    _kind: PhantomData<fn() -> S>,
}

impl<S> Confirm<S> {
    /// The length of a confirmation tag, 32 bytes.
    pub const BYTES: usize = 32;

    /// Copies `bytes` when they are [`Self::BYTES`] long.
    ///
    /// Fails with [`Error::WrongLength`] otherwise.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        let bytes: [u8; 32] = bytes.try_into().map_err(|_| Error::WrongLength)?;
        Ok(Self {
            bytes,
            _kind: PhantomData,
        })
    }
}

impl<S> AsRef<[u8]> for Confirm<S> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl<S> PartialEq for Confirm<S> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        let _entry = Entry::new_secret();
        ct::into_public(ct_equal(self.as_ref(), other.as_ref()))
    }
}

impl<S> fmt::Debug for Confirm<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Confirm").finish_non_exhaustive()
    }
}

/// The shared key. RFC 9383's is 32 bytes. Matter's is 16.
pub struct SharedKey {
    bytes: [u8; 32],
    len: u8,
}

impl SharedKey {
    #[inline]
    fn new(bytes: &[u8]) -> Self {
        let mut stored = [0u8; 32];
        stored[..bytes.len()].copy_from_slice(bytes);
        Self {
            bytes: stored,
            len: bytes.len() as u8,
        }
    }
}

impl AsRef<[u8]> for SharedKey {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

impl fmt::Debug for SharedKey {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SharedKey")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

impl Drop for SharedKey {
    #[inline]
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for SharedKey {}

/// The prover's password scalars `w0` and `w1`, wiped on drop under `wipe`.
pub struct ProverSecrets {
    w0: Scalar,
    w1: Scalar,
    /// 1 when `w0` reduced to 0. Secret: a branch would publish the password.
    w0_zero: u64,
    /// 1 when `w1` reduced to 0.
    w1_zero: u64,
}

impl ProverSecrets {
    /// Reduces big-endian `w0` and `w1` mod the group order.
    ///
    /// Each is at most 128 bytes, so a stretch with 64 extra bits past the
    /// order fits. Fails with [`Error::WrongLength`] past that or when empty.
    /// A residue of zero is not an error from this function. The handshake
    /// treats it as the identity and [`ProverAwaiting::finish`] returns
    /// [`Error::BadSignature`] after the same work as a bad confirmation tag.
    /// Returning that from here would publish that the password is 0 mod n.
    #[inline]
    pub fn new(w0: &[u8], w1: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let (w0, w0_zero) = password_scalar(w0)?;
        let (w1, w1_zero) = password_scalar(w1)?;
        Ok(Self {
            w0,
            w1,
            w0_zero,
            w1_zero,
        })
    }

    /// Picks an ephemeral scalar and returns this prover's share.
    ///
    /// `context`, `id_prover`, and `id_verifier` go into the transcript under
    /// an 8-byte little-endian length, including when empty. Each is at most
    /// 1024 bytes. The secrets stay usable for another handshake.
    #[inline]
    pub fn start<S: 'static>(
        &self,
        suite: &'static Suite<S>,
        context: &[u8],
        id_prover: &[u8],
        id_verifier: &[u8],
    ) -> Result<(Share<S>, ProverAwaiting<S>), Error> {
        self.start_at(suite, context, id_prover, id_verifier, None)
    }

    #[inline]
    fn start_at<S: 'static>(
        &self,
        suite: &'static Suite<S>,
        context: &[u8],
        id_prover: &[u8],
        id_verifier: &[u8],
        scalar: Option<Scalar>,
    ) -> Result<(Share<S>, ProverAwaiting<S>), Error> {
        let _entry = Entry::new_secret();
        let labels = Labels::new(context, id_prover, id_verifier)?;
        let x = match scalar {
            Some(scalar) => scalar,
            None => random_scalar()?,
        };
        let (m, _) = points()?;
        // `0 * M` is the identity, so the share is `x * G`. The multiplication
        // is only called on a scalar in `1..n-1`.
        let share = publish(mul_or_identity(m, &self.w0, self.w0_zero).add(Affine::mul_base(&x)))?;
        let state = ProverAwaiting {
            schedule: suite.schedule,
            labels,
            w0: self.w0.copy(),
            w1: self.w1.copy(),
            w0_zero: self.w0_zero,
            w1_zero: self.w1_zero,
            x,
            share_p: share.bytes,
            _kind: PhantomData,
        };
        Ok((share, state))
    }
}

impl fmt::Debug for ProverSecrets {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProverSecrets").finish_non_exhaustive()
    }
}

impl Drop for ProverSecrets {
    #[inline]
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for ProverSecrets {}

/// The verifier's record, `w0` and `L = w1 * G`, wiped on drop under `wipe`.
pub struct VerifierRecord {
    w0: Scalar,
    /// 1 when `w0` reduced to 0. Secret, as on [`ProverSecrets`].
    w0_zero: u64,
    l: Affine,
    /// 1 when `w1` reduced to 0, which makes `l` the identity.
    l_zero: u64,
}

impl VerifierRecord {
    /// Builds a record from `w0` and `w1`, setting `L` to `w1` times the generator.
    ///
    /// The scalar rules are [`ProverSecrets::new`]'s. A zero `w1` stores the
    /// identity as `L`. [`Self::from_record`] rejects that encoding; this
    /// in-memory record still fails the handshake at confirmation.
    #[inline]
    pub fn from_w1(w0: &[u8], w1: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let (w0, w0_zero) = password_scalar(w0)?;
        let (w1, w1_zero) = password_scalar(w1)?;
        // The multiplication is checked on a scalar in `1..n-1`. A zero `w1`
        // then selects the identity. L is half the stored record and must be
        // kept from the prover's side as w0 is, but it is treated as public
        // for timing: `from_record` parses it on the public path. Declassify
        // the affine value itself, identity included.
        let l = ct::into_public(base_for_record(&w1, w1_zero)?);
        Ok(Self {
            w0,
            w0_zero,
            l,
            l_zero: w1_zero,
        })
    }

    /// `L`, uncompressed, which [`Self::from_record`] loads with `w0`.
    ///
    /// Store `L` as carefully as `w0`. It is half the stored record, and
    /// with Matter's short passcodes it is enough to recover the passcode
    /// offline.
    #[inline]
    pub fn l(&self) -> [u8; 65] {
        let _entry = Entry::new_public();
        self.l.to_uncompressed()
    }

    /// Loads a stored record: `w0`, reduced as [`ProverSecrets::new`]
    /// reduces it, and `l`, uncompressed, as [`Self::l`] returns it.
    ///
    /// Fails with [`Error::KeyRejected`] when `l` is not on the curve. A zero
    /// `w0` loads; the handshake then fails as [`ProverSecrets::new`] describes.
    /// The identity encoding of a zero `w1` is not a curve point, so it is
    /// rejected here rather than reloaded as some other scalar.
    #[inline]
    pub fn from_record(w0: &[u8], l: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let (w0, w0_zero) = password_scalar(w0)?;
        Ok(Self {
            w0,
            w0_zero,
            l: Affine::from_uncompressed(l)?,
            // A curve point is not the identity. `from_w1` keeps that case
            // in memory, where `l_zero` still rejects the handshake.
            l_zero: 0,
        })
    }

    /// Answers `prover`'s share with this verifier's share and confirmation.
    ///
    /// The labels are the same strings the prover passed to [`ProverSecrets::start`].
    /// The record stays usable for another handshake.
    #[inline]
    pub fn start<S: 'static>(
        &self,
        suite: &'static Suite<S>,
        context: &[u8],
        id_prover: &[u8],
        id_verifier: &[u8],
        prover: &Share<S>,
    ) -> VerifierStart<S> {
        self.start_at(suite, context, id_prover, id_verifier, prover, None)
    }

    #[inline]
    fn start_at<S: 'static>(
        &self,
        suite: &'static Suite<S>,
        context: &[u8],
        id_prover: &[u8],
        id_verifier: &[u8],
        prover: &Share<S>,
        scalar: Option<Scalar>,
    ) -> VerifierStart<S> {
        let _entry = Entry::new_secret();
        let labels = Labels::new(context, id_prover, id_verifier)?;
        let y = match scalar {
            Some(scalar) => scalar,
            None => random_scalar()?,
        };
        let (m, n) = points()?;
        let peer = Affine::from_uncompressed(prover.as_ref())?;
        let share_v =
            publish(mul_or_identity(n, &self.w0, self.w0_zero).add(Affine::mul_base(&y)))?;
        let diff = peer.add(mul_or_identity(m, &self.w0, self.w0_zero).negate());
        // X = w0*M makes the difference the identity. Its affine image is
        // (0, 0), which the scalar multiplication does not accept. Multiply
        // the generator instead, then reject. RFC 9383 allows that abort.
        // The bit is declassified once, after the same multiplication and
        // transcript work as a share that is not the identity.
        let (z_point, identity) = mul_defined(diff, &y);
        let z = secret_point(z_point)?;
        let v = encode_maybe_identity(mul_or_identity(self.l, &y, self.l_zero), self.l_zero)?;
        let keys = schedule_keys(
            suite.schedule,
            &transcript(
                &labels,
                prover.as_ref(),
                share_v.as_ref(),
                z.as_slice(),
                v.as_slice(),
                &self.w0,
            ),
        )?;
        let confirm_v: Confirm<S> = sent(mac(keys.verifier_key(), prover.as_ref()));
        let confirm_p: Confirm<S> = mac(keys.prover_key(), share_v.as_ref());
        let mut shared = [0u8; 32];
        shared[..keys.shared().len()].copy_from_slice(keys.shared());
        let state = VerifierAwaiting {
            confirm_p: confirm_p.bytes,
            shared,
            shared_len: keys.shared().len() as u8,
            rejected: self.w0_zero | self.l_zero,
            _kind: PhantomData,
        };
        if ct::into_public(identity) == 1 {
            return Err(Error::BadSignature);
        }
        Ok((share_v, confirm_v, state))
    }
}

impl fmt::Debug for VerifierRecord {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VerifierRecord").finish_non_exhaustive()
    }
}

impl Drop for VerifierRecord {
    #[inline]
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for VerifierRecord {}

type VerifierStart<S> = Result<(Share<S>, Confirm<S>, VerifierAwaiting<S>), Error>;

/// The prover, between its share and the verifier's confirmation.
pub struct ProverAwaiting<S> {
    schedule: Schedule,
    labels: Labels,
    w0: Scalar,
    w1: Scalar,
    w0_zero: u64,
    w1_zero: u64,
    x: Scalar,
    share_p: [u8; Affine::BYTES],
    _kind: PhantomData<fn() -> S>,
}

impl<S> ProverAwaiting<S> {
    /// Checks `confirm`, then returns this prover's confirmation and the shared key.
    ///
    /// Fails with [`Error::BadSignature`] when `confirm` is not the verifier's
    /// tag over this prover's share, when the verifier's share makes a derived
    /// point the identity, and when `w0` or `w1` reduced to zero. The shared
    /// key is not returned on failure.
    #[inline]
    pub fn finish(
        self,
        verifier: &Share<S>,
        confirm: &Confirm<S>,
    ) -> Result<(Confirm<S>, SharedKey), Error> {
        let _entry = Entry::new_secret();
        let (confirm_p, key, ok) = self.compute(verifier, confirm)?;
        // One declassification covers the tag, the identity, and a zero
        // password scalar. `ok` is a mask, not a `bool`: moving a secret
        // `bool` out of a `Result` makes rustc check that it is 0 or 1,
        // and that check branches on it. The tag this side sends is
        // declassified only when it is returned.
        match ct::into_public(ok) {
            1 => Ok((sent(confirm_p), key)),
            _ => Err(Error::BadSignature),
        }
    }

    #[inline]
    fn compute(
        &self,
        verifier: &Share<S>,
        confirm: &Confirm<S>,
    ) -> Result<(Confirm<S>, SharedKey, u64), Error> {
        let (_, n) = points()?;
        let peer = Affine::from_uncompressed(verifier.as_ref())?;
        let diff = peer.add(mul_or_identity(n, &self.w0, self.w0_zero).negate());
        // As the verifier's `mul_defined` does, but `base` also takes `w1`.
        let (base, identity) = defined(diff);
        let z = secret_point(base.mul(&self.x))?;
        let v = encode_maybe_identity(mul_or_identity(base, &self.w1, self.w1_zero), self.w1_zero)?;
        let keys = schedule_keys(
            self.schedule,
            &transcript(
                &self.labels,
                &self.share_p,
                verifier.as_ref(),
                z.as_slice(),
                v.as_slice(),
                &self.w0,
            ),
        )?;
        let expect: Confirm<S> = mac(keys.verifier_key(), &self.share_p);
        let confirm_p: Confirm<S> = mac(keys.prover_key(), verifier.as_ref());
        let key = SharedKey::new(keys.shared());
        // `identity` is 1 exactly when Y = w0*N. A zero password scalar is
        // rejected here too, so the result is the same error as a bad tag.
        // Each factor is 0 or 1. The product is 1 only when every check passes.
        let ok = u64::from(ct_equal(expect.as_ref(), confirm.as_ref()))
            & (identity ^ 1)
            & ((self.w0_zero | self.w1_zero) ^ 1);
        Ok((confirm_p, key, ok))
    }
}

impl<S> fmt::Debug for ProverAwaiting<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProverAwaiting").finish_non_exhaustive()
    }
}

impl<S> Drop for ProverAwaiting<S> {
    #[inline]
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl<S> Zeroable for ProverAwaiting<S> {}

/// The verifier, waiting for the prover's confirmation.
pub struct VerifierAwaiting<S> {
    confirm_p: [u8; 32],
    shared: [u8; 32],
    shared_len: u8,
    /// 1 when `w0` or `w1` reduced to 0. Combined with the tag check below.
    rejected: u64,
    _kind: PhantomData<fn() -> S>,
}

impl<S> VerifierAwaiting<S> {
    /// Returns the shared key when `confirm` is the prover's tag.
    ///
    /// Fails with [`Error::BadSignature`] when it is not, and when `w0` or
    /// `w1` reduced to zero. The key is wiped on failure.
    #[inline]
    pub fn finish(self, confirm: &Confirm<S>) -> Result<SharedKey, Error> {
        let _entry = Entry::new_secret();
        let key = SharedKey::new(&self.shared[..usize::from(self.shared_len)]);
        let ok = ct_equal(&self.confirm_p, confirm.as_ref()) & (self.rejected == 0);
        match ct::into_public(ok) {
            true => Ok(key),
            false => Err(Error::BadSignature),
        }
    }
}

impl<S> fmt::Debug for VerifierAwaiting<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VerifierAwaiting").finish_non_exhaustive()
    }
}

impl<S> Drop for VerifierAwaiting<S> {
    #[inline]
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl<S> Zeroable for VerifierAwaiting<S> {}

struct Label {
    bytes: [u8; MAX_LABEL],
    len: u16,
}

impl Label {
    #[inline]
    fn new(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() > MAX_LABEL {
            return Err(Error::WrongLength);
        }
        let mut stored = [0u8; MAX_LABEL];
        stored[..bytes.len()].copy_from_slice(bytes);
        Ok(Self {
            bytes: stored,
            len: bytes.len() as u16,
        })
    }

    #[inline]
    fn as_slice(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

struct Labels {
    context: Label,
    id_prover: Label,
    id_verifier: Label,
}

impl Labels {
    #[inline]
    fn new(context: &[u8], id_prover: &[u8], id_verifier: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            context: Label::new(context)?,
            id_prover: Label::new(id_prover)?,
            id_verifier: Label::new(id_verifier)?,
        })
    }
}

impl Zeroable for Label {}
impl Zeroable for Labels {}
impl Zeroable for Schedule {}
impl<S> Zeroable for Confirm<S> {}

/// Both confirmation keys and the shared key. Each is `len` bytes: 32 for
/// RFC 9383, 16 for draft-01.
struct Keys {
    prover: [u8; 32],
    verifier: [u8; 32],
    shared: [u8; 32],
    len: usize,
}

impl Keys {
    #[inline]
    fn prover_key(&self) -> &[u8] {
        &self.prover[..self.len]
    }

    #[inline]
    fn verifier_key(&self) -> &[u8] {
        &self.verifier[..self.len]
    }

    #[inline]
    fn shared(&self) -> &[u8] {
        &self.shared[..self.len]
    }
}

#[inline]
fn points() -> Result<(Affine, Affine), Error> {
    Ok((
        Affine::from_uncompressed(&M_UNCOMPRESSED)?,
        Affine::from_uncompressed(&N_UNCOMPRESSED)?,
    ))
}

/// `point`, with the generator standing in for the identity.
///
/// Returns the point to multiply and 1 when `point` was the identity.
/// `(0, 0)` is not a curve point, and the scalar multiplication is
/// unspecified on it. The mask stays secret.
#[inline]
fn defined(point: Affine) -> (Affine, u64) {
    let identity = point.identity_mask();
    (point.select(Affine::generator(), identity), identity)
}

/// `scalar * point`, with the generator standing in for the identity, as
/// [`defined`] picks it, and 1 when `point` was the identity.
#[inline]
fn mul_defined(point: Affine, scalar: &Scalar) -> (Affine, u64) {
    let (base, identity) = defined(point);
    (base.mul(scalar), identity)
}

/// Reduces `bytes` and reports whether the residue is zero.
///
/// The mask stays secret. [`Scalar::from_be_reduced`] does not branch on it.
#[inline]
fn password_scalar(bytes: &[u8]) -> Result<(Scalar, u64), Error> {
    let scalar = Scalar::from_be_reduced(bytes)?;
    let zero = scalar.zero_mask();
    Ok((scalar, zero))
}

/// `w1 * G` for a record, using a scalar in `1..n-1`.
///
/// A zero residue selects the identity after the multiplication. Off-curve
/// here is a fault in that routine: the scalar it sees is never zero, so the
/// check does not reveal the residue.
#[inline]
fn base_for_record(scalar: &Scalar, zero: u64) -> Result<Affine, Error> {
    let point = Affine::mul_base(&scalar.select(&Scalar::one(), zero));
    if !ct::into_public(point.on_curve()) {
        return Err(Error::Fault);
    }
    Ok(point.select(Affine::identity(), zero))
}

/// `scalar * point`, or the identity when `zero` is 1.
///
/// `0 * P` is the identity. The multiplication is specified for a curve
/// point and a scalar in `1..n-1`, so a zero scalar substitutes both and
/// the product is replaced. `point` itself may be the identity only when
/// `zero` is already 1, as a stored `L` from [`VerifierRecord::from_w1`].
#[inline]
fn mul_or_identity(point: Affine, scalar: &Scalar, zero: u64) -> Affine {
    let safe_point = point.select(Affine::generator(), zero);
    let safe_scalar = scalar.select(&Scalar::one(), zero);
    safe_point
        .mul(&safe_scalar)
        .select(Affine::identity(), zero)
}

/// Encodes `point`, which is the identity exactly when `identity_ok` is 1.
///
/// A normal product is on the curve and `identity_ok` is 0. The identity is
/// off the curve and `identity_ok` is 1. Both leave the fault bit clear, so
/// rejecting an unexpected off-curve point does not reveal a zero residue.
#[inline]
fn encode_maybe_identity(point: Affine, identity_ok: u64) -> Result<EncodedPoint, Error> {
    let bytes = point.to_uncompressed();
    let on_curve = u64::from(point.on_curve());
    let fault = (on_curve ^ 1) & (identity_ok ^ 1);
    if ct::into_public(fault) == 1 {
        return Err(Error::Fault);
    }
    Ok(EncodedPoint {
        bytes,
        len: Affine::BYTES as u8,
    })
}

#[inline]
fn random_scalar() -> Result<Scalar, Error> {
    let mut rng = SystemRandom;
    for _ in 0..64 {
        let mut bytes = [0u8; Scalar::BYTES];
        rng.fill(&mut bytes)?;
        ct::secret_slice(&bytes);
        if let Ok(scalar) = Scalar::from_bytes_checked(&bytes) {
            return Ok(ct::into_secret(scalar));
        }
    }
    Err(Error::RngFailed)
}

struct EncodedPoint {
    bytes: [u8; Affine::BYTES],
    len: u8,
}

impl EncodedPoint {
    #[inline]
    fn as_slice(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

/// Uncompressed SEC 1 encoding after a curve check. `public` declassifies
/// the bytes. Every point encoded here is computed from on-curve inputs (a
/// peer's share is checked when it is decoded), so an off-curve result is an
/// internal fault, as in [`VerifierRecord::from_w1`].
#[inline]
fn encode(point: Affine, public: bool) -> Result<EncodedPoint, Error> {
    let bytes = point.to_uncompressed();
    if !ct::into_public(point.on_curve()) {
        return Err(Error::Fault);
    }
    if public {
        ct::public_slice(&bytes);
    }
    Ok(EncodedPoint {
        bytes,
        len: Affine::BYTES as u8,
    })
}

/// Declassifies a tag this side sends to the peer.
///
/// Stays `#[inline]` so a normal build still adds no codegen-unit root.
/// Under ctgrind the client request takes the address as an integer, and an
/// inlined mark returns the unmarked tag `mac` wrote. `ct::defined_bytes`
/// copies that tag out after the request, and it exists only in that build.
#[inline]
fn sent<S>(confirm: Confirm<S>) -> Confirm<S> {
    #[cfg(feature = "__ctgrind")]
    {
        return Confirm {
            bytes: ct::defined_bytes(confirm.bytes),
            _kind: PhantomData,
        };
    }
    #[cfg(not(feature = "__ctgrind"))]
    {
        ct::public_slice(&confirm.bytes);
        confirm
    }
}

#[inline]
fn publish<S>(point: Affine) -> Result<Share<S>, Error> {
    let encoded = encode(point, true)?;
    Ok(Share {
        bytes: encoded.bytes,
        _kind: PhantomData,
    })
}

#[inline]
fn secret_point(point: Affine) -> Result<EncodedPoint, Error> {
    encode(point, false)
}

#[inline]
fn absorb(hash: &mut digest::Context, data: &[u8]) {
    hash.update(&(data.len() as u64).to_le_bytes());
    hash.update(data);
}

#[inline]
fn transcript(
    labels: &Labels,
    share_p: &[u8],
    share_v: &[u8],
    z: &[u8],
    v: &[u8],
    w0: &Scalar,
) -> [u8; 32] {
    let mut hash = digest::Context::new(&digest::SHA256);
    absorb(&mut hash, labels.context.as_slice());
    absorb(&mut hash, labels.id_prover.as_slice());
    absorb(&mut hash, labels.id_verifier.as_slice());
    // `m_and_n_match_their_compressed_form` checks these are M and N.
    absorb(&mut hash, &M_UNCOMPRESSED);
    absorb(&mut hash, &N_UNCOMPRESSED);
    absorb(&mut hash, share_p);
    absorb(&mut hash, share_v);
    absorb(&mut hash, z);
    absorb(&mut hash, v);
    absorb(&mut hash, &w0.as_bytes());
    let digest = hash.finish();
    let mut out = [0u8; 32];
    out.copy_from_slice(digest.as_ref());
    out
}

#[inline]
fn expand(prk: &hkdf::Prk, info: &[u8], out: &mut [u8]) -> Result<(), Error> {
    prk.expand(&[info], out.len())
        .fill(out)
        .map_err(|_| Error::Fault)
}

#[inline]
fn schedule_keys(schedule: Schedule, transcript_hash: &[u8; 32]) -> Result<Keys, Error> {
    let mut keys = Keys {
        prover: [0; 32],
        verifier: [0; 32],
        shared: [0; 32],
        len: 0,
    };
    match schedule {
        Schedule::Rfc9383 => {
            let prk = hkdf::Salt::new(&hkdf::HKDF_SHA256, b"").extract(transcript_hash);
            let mut confirm = [0u8; 64];
            expand(&prk, b"ConfirmationKeys", &mut confirm)?;
            keys.prover.copy_from_slice(&confirm[..32]);
            keys.verifier.copy_from_slice(&confirm[32..]);
            expand(&prk, b"SharedKey", &mut keys.shared)?;
            keys.len = 32;
        }
        Schedule::Draft01 => {
            // Appendix B's hash splits as Ka || Ke. Ka is 16 bytes.
            let prk = hkdf::Salt::new(&hkdf::HKDF_SHA256, b"").extract(&transcript_hash[..16]);
            let mut confirm = [0u8; 32];
            expand(&prk, b"ConfirmationKeys", &mut confirm)?;
            keys.prover[..16].copy_from_slice(&confirm[..16]);
            keys.verifier[..16].copy_from_slice(&confirm[16..]);
            keys.shared[..16].copy_from_slice(&transcript_hash[16..]);
            keys.len = 16;
        }
    }
    Ok(keys)
}

/// The tag stays secret. A tag this side sends is declassified by [`sent`];
/// one it only compares against the peer's stays secret through `ct_equal`.
#[inline]
fn mac<S>(key: &[u8], message: &[u8]) -> Confirm<S> {
    let tag = hmac::sign(&hmac::Key::new(&hmac::HMAC_SHA256, key), message);
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(tag.as_ref());
    Confirm {
        bytes,
        _kind: PhantomData,
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[inline]
    fn hex(s: &str) -> Vec<u8> {
        hex::decode(s).unwrap()
    }

    #[inline]
    fn scalar(s: &str) -> Scalar {
        Scalar::from_be_reduced(&hex(s)).unwrap()
    }

    struct Vector<S: 'static> {
        suite: &'static Suite<S>,
        context: &'static [u8],
        id_prover: &'static [u8],
        id_verifier: &'static [u8],
        w0: &'static str,
        w1: &'static str,
        l: &'static str,
        x: &'static str,
        y: &'static str,
        share_p: &'static str,
        share_v: &'static str,
        confirm_p: &'static str,
        confirm_v: &'static str,
        shared: &'static str,
    }

    #[inline]
    fn run<S: 'static>(vector: &Vector<S>) {
        let prover = ProverSecrets::new(&hex(vector.w0), &hex(vector.w1)).unwrap();
        let from_w1 = VerifierRecord::from_w1(&hex(vector.w0), &hex(vector.w1)).unwrap();
        let loaded = VerifierRecord::from_record(&hex(vector.w0), &hex(vector.l)).unwrap();
        assert_eq!(from_w1.l().as_slice(), hex(vector.l).as_slice());

        let (share_p, prover) = prover
            .start_at(
                vector.suite,
                vector.context,
                vector.id_prover,
                vector.id_verifier,
                Some(scalar(vector.x)),
            )
            .unwrap();
        assert_eq!(share_p.as_ref(), hex(vector.share_p).as_slice());

        let (share_v, confirm_v, _) = loaded
            .start_at(
                vector.suite,
                vector.context,
                vector.id_prover,
                vector.id_verifier,
                &share_p,
                Some(scalar(vector.y)),
            )
            .unwrap();
        assert_eq!(share_v.as_ref(), hex(vector.share_v).as_slice());
        assert_eq!(confirm_v.as_ref(), hex(vector.confirm_v).as_slice());

        let (confirm_p, key_p) = prover.finish(&share_v, &confirm_v).unwrap();
        assert_eq!(confirm_p.as_ref(), hex(vector.confirm_p).as_slice());
        // The shared key stays secret. The vector is public, so the check
        // declassifies the key before it compares.
        ct::public_slice(key_p.as_ref());
        assert_eq!(key_p.as_ref(), hex(vector.shared).as_slice());

        let (share_v, confirm_v, verifier) = from_w1
            .start_at(
                vector.suite,
                vector.context,
                vector.id_prover,
                vector.id_verifier,
                &share_p,
                Some(scalar(vector.y)),
            )
            .unwrap();
        let key_v = verifier.finish(&confirm_p).unwrap();
        assert_eq!(share_v.as_ref(), hex(vector.share_v).as_slice());
        assert_eq!(confirm_v.as_ref(), hex(vector.confirm_v).as_slice());
        ct::public_slice(key_v.as_ref());
        assert_eq!(key_v.as_ref(), key_p.as_ref());
    }

    #[test]
    #[inline]
    fn rfc9383() {
        run(&Vector {
            suite: &RFC9383,
            context: b"SPAKE2+-P256-SHA256-HKDF-SHA256-HMAC-SHA256 Test Vectors",
            id_prover: b"client",
            id_verifier: b"server",
            w0: "bb8e1bbcf3c48f62c08db243652ae55d3e5586053fca77102994f23ad95491b3",
            w1: "7e945f34d78785b8a3ef44d0df5a1a97d6b3b460409a345ca7830387a74b1dba",
            l: "04eb7c9db3d9a9eb1f8adab81b5794c1f13ae3e225efbe91ea487425854c7fc00f00bfedcbd09b2400142d40a14f2064ef31dfaa903b91d1faea7093d835966efd",
            x: "d1232c8e8693d02368976c174e2088851b8365d0d79a9eee709c6a05a2fad539",
            y: "717a72348a182085109c8d3917d6c43d59b224dc6a7fc4f0483232fa6516d8b3",
            share_p: "04ef3bd051bf78a2234ec0df197f7828060fe9856503579bb1733009042c15c0c1de127727f418b5966afadfdd95a6e4591d171056b333dab97a79c7193e341727",
            share_v: "04c0f65da0d11927bdf5d560c69e1d7d939a05b0e88291887d679fcadea75810fb5cc1ca7494db39e82ff2f50665255d76173e09986ab46742c798a9a68437b048",
            confirm_p: "926cc713504b9b4d76c9162ded04b5493e89109f6d89462cd33adc46fda27527",
            confirm_v: "9747bcc4f8fe9f63defee53ac9b07876d907d55047e6ff2def2e7529089d3e68",
            shared: "0c5f8ccd1413423a54f6c1fb26ff01534a87f893779c6e68666d772bfd91f3e7",
        });
    }

    #[test]
    #[inline]
    fn draft01() {
        run(&Vector {
            suite: &MATTER_PASE,
            context: b"SPAKE2+-P256-SHA256-HKDF draft-01",
            id_prover: b"client",
            id_verifier: b"server",
            w0: "e6887cf9bdfb7579c69bf47928a84514b5e355ac034863f7ffaf4390e67d798c",
            w1: "24b5ae4abda868ec9336ffc3b78ee31c5755bef1759227ef5372ca139b94e512",
            l: "0495645cfb74df6e58f9748bb83a86620bab7c82e107f57d6870da8cbcb2ff9f7063a14b6402c62f99afcb9706a4d1a143273259fe76f1c605a3639745a92154b9",
            x: "8b0f3f383905cf3a3bb955ef8fb62e24849dd349a05ca79aafb18041d30cbdb6",
            y: "2e0895b0e763d6d5a9564433e64ac3cac74ff897f6c3445247ba1bab40082a91",
            share_p: "04af09987a593d3bac8694b123839422c3cc87e37d6b41c1d630f000dd64980e537ae704bcede04ea3bec9b7475b32fa2ca3b684be14d11645e38ea6609eb39e7e",
            share_v: "04417592620aebf9fd203616bbb9f121b730c258b286f890c5f19fea833a9c900cbe9057bc549a3e19975be9927f0e7614f08d1f0a108eede5fd7eb5624584a4f4",
            confirm_p: "d4376f2da9c72226dd151b77c2919071155fc22a2068d90b5faa6c78c11e77dd",
            confirm_v: "0660a680663e8c5695956fb22dff298b1d07a526cf3cc591adfecd1f6ef6e02e",
            shared: "801db297654816eb4f02868129b9dc89",
        });
        // The same password with an empty verifier identity, appendix B's second vector.
        run(&Vector {
            suite: &MATTER_PASE,
            context: b"SPAKE2+-P256-SHA256-HKDF draft-01",
            id_prover: b"client",
            id_verifier: b"",
            w0: "e6887cf9bdfb7579c69bf47928a84514b5e355ac034863f7ffaf4390e67d798c",
            w1: "24b5ae4abda868ec9336ffc3b78ee31c5755bef1759227ef5372ca139b94e512",
            l: "0495645cfb74df6e58f9748bb83a86620bab7c82e107f57d6870da8cbcb2ff9f7063a14b6402c62f99afcb9706a4d1a143273259fe76f1c605a3639745a92154b9",
            x: "ec82d9258337f61239c9cd68e8e532a3a6b83d12d2b1ca5d543f44def17dfb8d",
            y: "eac3f7de4b198d5fe25c443c0cd4963807add767815dd02a6f0133b4bc2c9eb0",
            share_p: "04230779960824076d3666a7418e4d433e2fa15b06176eabdd572f43a32ecc79a192b243d2624310a7356273b86e5fd9bd627d3ade762baeff1a320d4ad7a4e47f",
            share_v: "044558642e71b616b248c9583bd6d7aa1b3952c6df6a9f7492a06035ca5d92522d84443de7aa20a59380fa4de6b7438d925dbfb7f1cfe60d79acf961ee33988c7d",
            confirm_p: "e1b9258807ba4750dae1d7f3c3c294f13dc4fa60cde346d5de7d200e2f8fd3fc",
            confirm_v: "b9c39dfa49c47757de778d9bedeaca2448b905be19a43b94ee24b770208135e3",
            shared: "6989d8f9177ef7df67da437987f07255",
        });
    }

    /// Every vector in connectedhomeip `src/crypto/tests/SPAKE2P_RFC_test_vectors.h`.
    ///
    /// That is the set Matter's PASE tests run. The first two are also
    /// draft-01 appendix B, covered by [`draft01`].
    #[test]
    #[inline]
    fn connectedhomeip() {
        let context: &[u8] = b"SPAKE2+-P256-SHA256-HKDF draft-01";
        let w0 = "e6887cf9bdfb7579c69bf47928a84514b5e355ac034863f7ffaf4390e67d798c";
        let w1 = "24b5ae4abda868ec9336ffc3b78ee31c5755bef1759227ef5372ca139b94e512";
        let l = "0495645cfb74df6e58f9748bb83a86620bab7c82e107f57d6870da8cbcb2ff9f7063a14b6402c62f99afcb9706a4d1a143273259fe76f1c605a3639745a92154b9";
        let cases = [
            (
                b"client".as_slice(),
                b"server".as_slice(),
                "8b0f3f383905cf3a3bb955ef8fb62e24849dd349a05ca79aafb18041d30cbdb6",
                "2e0895b0e763d6d5a9564433e64ac3cac74ff897f6c3445247ba1bab40082a91",
                "04af09987a593d3bac8694b123839422c3cc87e37d6b41c1d630f000dd64980e537ae704bcede04ea3bec9b7475b32fa2ca3b684be14d11645e38ea6609eb39e7e",
                "04417592620aebf9fd203616bbb9f121b730c258b286f890c5f19fea833a9c900cbe9057bc549a3e19975be9927f0e7614f08d1f0a108eede5fd7eb5624584a4f4",
                "d4376f2da9c72226dd151b77c2919071155fc22a2068d90b5faa6c78c11e77dd",
                "0660a680663e8c5695956fb22dff298b1d07a526cf3cc591adfecd1f6ef6e02e",
                "801db297654816eb4f02868129b9dc89",
            ),
            (
                b"client".as_slice(),
                b"".as_slice(),
                "ec82d9258337f61239c9cd68e8e532a3a6b83d12d2b1ca5d543f44def17dfb8d",
                "eac3f7de4b198d5fe25c443c0cd4963807add767815dd02a6f0133b4bc2c9eb0",
                "04230779960824076d3666a7418e4d433e2fa15b06176eabdd572f43a32ecc79a192b243d2624310a7356273b86e5fd9bd627d3ade762baeff1a320d4ad7a4e47f",
                "044558642e71b616b248c9583bd6d7aa1b3952c6df6a9f7492a06035ca5d92522d84443de7aa20a59380fa4de6b7438d925dbfb7f1cfe60d79acf961ee33988c7d",
                "e1b9258807ba4750dae1d7f3c3c294f13dc4fa60cde346d5de7d200e2f8fd3fc",
                "b9c39dfa49c47757de778d9bedeaca2448b905be19a43b94ee24b770208135e3",
                "6989d8f9177ef7df67da437987f07255",
            ),
            (
                b"".as_slice(),
                b"server".as_slice(),
                "ba0f0f5b78ef23fd07868e46aeca63b51fda519a3420501acbe23d53c2918748",
                "39397fbe6db47e9fbd1a263d79f5d0aaa44df26ce755f78e092644b434533a42",
                "04c14d28f4370fea20745106cea58bcfb60f2949fa4e131b9aff5ea13fd5aa79d507ae1d229e447e000f15eb78a9a32c2b88652e3411642043c1b2b7992cf2d4de",
                "04d1bee3120fd87e86fe189cb952dc688823080e62524dd2c08dffe3d22a0a8986aa64c9fe0191033cafbc9bcaefc8e2ba8ba860cd127af9efdd7f1c3a41920fe8",
                "e564c93b3015efb946dc16d642bbe7d1c8da5be164ed9fc3bae4e0ff86e1bd3c",
                "072a94d9a54edc201d8891534c2317cadf3ea3792827f479e873f93e90f21552",
                "2ea40e4badfa5452b5744dc5983e99ba",
            ),
            (
                b"".as_slice(),
                b"".as_slice(),
                "5b478619804f4938d361fbba3a20648725222f0a54cc4c876139efe7d9a21786",
                "766770dad8c8eecba936823c0aed044b8c3c4f7655e8beec44a15dcbcaf78e5e",
                "04a6db23d001723fb01fcfc9d08746c3c2a0a3feff8635d29cad2853e7358623425cf39712e928054561ba71e2dc11f300f1760e71eb177021a8f85e78689071cd",
                "04390d29bf185c3abf99f150ae7c13388c82b6be0c07b1b8d90d26853e84374bbdc82becdb978ca3792f472424106a2578012752c11938fcf60a41df75ff7cf947",
                "71d9412779b6c45a2c615c9df3f1fd93dc0aaf63104da8ece4aa1b5a3a415fea",
                "095dc0400355cc233fde7437811815b3c1524aae80fd4e6810cf531cf11d20e3",
                "ea3276d68334576097e04b19ee5a3a8b",
            ),
        ];
        for (id_prover, id_verifier, x, y, share_p, share_v, confirm_p, confirm_v, shared) in cases
        {
            run(&Vector {
                suite: &MATTER_PASE,
                context,
                id_prover,
                id_verifier,
                w0,
                w1,
                l,
                x,
                y,
                share_p,
                share_v,
                confirm_p,
                confirm_v,
                shared,
            });
        }
    }

    /// A handshake pakery-spake2plus has not published as a vector.
    #[test]
    #[cfg(not(any(miri, target_family = "wasm")))]
    #[inline]
    fn matches_pakery() {
        use p256::elliptic_curve::ff::PrimeField;
        use pakery_crypto::{
            HkdfSha256, HmacSha256, P256Group, SPAKE2_P256_M_COMPRESSED, SPAKE2_P256_N_COMPRESSED,
            Sha256Hash,
        };
        use pakery_spake2plus::registration::compute_verifier;
        use pakery_spake2plus::{Prover, Spake2PlusCiphersuite, Verifier};

        struct Pakery;
        impl Spake2PlusCiphersuite for Pakery {
            type Group = P256Group;
            type Hash = Sha256Hash;
            type Kdf = HkdfSha256;
            type Mac = HmacSha256;
            const NH: usize = 32;
            const M_BYTES: &'static [u8] = &SPAKE2_P256_M_COMPRESSED;
            const N_BYTES: &'static [u8] = &SPAKE2_P256_N_COMPRESSED;
        }

        #[inline]
        fn sc(bytes: &[u8; 32]) -> p256::Scalar {
            p256::Scalar::from_repr((*bytes).into()).unwrap()
        }

        let w0 = [0x42; 32];
        let w1 = [0x24; 32];
        let x = [0x07; 32];
        let y = [0x0b; 32];
        let context = b"not a published vector";
        let id_prover = b"prover";
        let id_verifier = b"";

        let (share_p, prover) = ProverSecrets::new(&w0, &w1)
            .unwrap()
            .start_at(
                &RFC9383,
                context,
                id_prover,
                id_verifier,
                Some(Scalar::from_be_reduced(&x).unwrap()),
            )
            .unwrap();
        let l = compute_verifier::<Pakery>(&sc(&w1));
        let (share_v, confirm_v, _) = VerifierRecord::from_record(&w0, &l)
            .unwrap()
            .start_at(
                &RFC9383,
                context,
                id_prover,
                id_verifier,
                &share_p,
                Some(Scalar::from_be_reduced(&y).unwrap()),
            )
            .unwrap();
        let (confirm_p, key) = prover.finish(&share_v, &confirm_v).unwrap();

        let (their_p, their_prover) = Prover::<Pakery>::start_with_scalar(
            &sc(&w0),
            &sc(&w1),
            &sc(&x),
            context,
            id_prover,
            id_verifier,
        )
        .unwrap();
        assert_eq!(share_p.as_ref(), their_p.as_slice());
        let (their_v, their_confirm_v, their_verifier) = Verifier::<Pakery>::start_with_scalar(
            &their_p,
            &sc(&w0),
            &l,
            &sc(&y),
            context,
            id_prover,
            id_verifier,
        )
        .unwrap();
        assert_eq!(share_v.as_ref(), their_v.as_slice());
        assert_eq!(confirm_v.as_ref(), their_confirm_v.as_slice());
        let their_out = their_prover.finish(&their_v, &their_confirm_v).unwrap();
        // pakery's tags are HMAC from the `sha2` crate. Memcheck follows an
        // uninitialized slot in that HMAC into the tag, so mark the public
        // outputs before the compares. pakery's own declassify is off here.
        ct::public_slice(their_out.confirm_p.as_slice());
        ct::public_slice(their_out.session_key.as_bytes());
        assert_eq!(confirm_p.as_ref(), their_out.confirm_p.as_slice());
        ct::public_slice(key.as_ref());
        assert_eq!(key.as_ref(), their_out.session_key.as_bytes());
        let their_key = their_verifier.finish(confirm_p.as_ref()).unwrap();
        ct::public_slice(their_key.session_key.as_bytes());
        assert_eq!(key.as_ref(), their_key.session_key.as_bytes());
    }

    /// A stored record, and the prover's secrets, serve more than one
    /// handshake, each with its own key.
    #[test]
    #[inline]
    fn a_record_serves_many_handshakes() {
        let w0 = [0x11; 40];
        let w1 = [0x22; 40];
        let prover = ProverSecrets::new(&w0, &w1).unwrap();
        let record =
            VerifierRecord::from_record(&w0, &VerifierRecord::from_w1(&w0, &w1).unwrap().l())
                .unwrap();
        let mut keys = Vec::new();
        let mut shares = Vec::new();
        for _ in 0..2 {
            let (share_p, prover) = prover.start(&RFC9383, b"ctx", b"a", b"b").unwrap();
            shares.push(share_p);
            let (share_v, confirm_v, verifier) = record
                .start(&RFC9383, b"ctx", b"a", b"b", &share_p)
                .unwrap();
            let (confirm_p, key) = prover.finish(&share_v, &confirm_v).unwrap();
            let other = verifier.finish(&confirm_p).unwrap();
            ct::public_slice(key.as_ref());
            ct::public_slice(other.as_ref());
            assert_eq!(key.as_ref(), other.as_ref());
            keys.push(key.as_ref().to_vec());
        }
        assert_ne!(keys[0], keys[1]);
        assert_ne!(shares[0], shares[1]);
    }

    #[test]
    #[inline]
    fn rejects_a_bad_confirmation_and_a_bad_share() {
        let w0 = [0x11; 40];
        let w1 = [0x22; 40];
        let prover = ProverSecrets::new(&w0, &w1).unwrap();
        let verifier = VerifierRecord::from_w1(&w0, &w1).unwrap();
        let (share_p, prover_state) = prover.start(&RFC9383, b"ctx", b"a", b"b").unwrap();
        let (share_v, confirm_v, _) = verifier
            .start(&RFC9383, b"ctx", b"a", b"b", &share_p)
            .unwrap();
        let mut bad = confirm_v.bytes;
        bad[0] ^= 1;
        assert_eq!(
            prover_state
                .finish(&share_v, &confirm_of::<Rfc9383>(bad))
                .err(),
            Some(Error::BadSignature)
        );

        let prover = ProverSecrets::new(&w0, &w1).unwrap();
        let verifier = VerifierRecord::from_w1(&w0, &w1).unwrap();
        let (share_p, prover_state) = prover.start(&RFC9383, b"ctx", b"a", b"b").unwrap();
        let (share_v, confirm_v, verifier_state) = verifier
            .start(&RFC9383, b"ctx", b"a", b"b", &share_p)
            .unwrap();
        let (confirm_p, _) = prover_state.finish(&share_v, &confirm_v).unwrap();
        let mut bad = confirm_p.bytes;
        bad[3] ^= 0x80;
        assert_eq!(
            verifier_state.finish(&confirm_of::<Rfc9383>(bad)).err(),
            Some(Error::BadSignature)
        );

        let mut off = share_p.bytes;
        off[10] ^= 1;
        assert!(Share::<Rfc9383>::from_bytes(&off).is_err());
        assert!(Share::<Rfc9383>::from_bytes(&off[..64]).is_err());
        assert!(Confirm::<Rfc9383>::from_bytes(&[0; 16]).is_err());
        assert!(ProverSecrets::new(&[], &w1).is_err());
        assert!(VerifierRecord::from_w1(&w0, &[0; 129]).is_err());
        let prover = ProverSecrets::new(&w0, &w1).unwrap();
        assert_eq!(
            prover.start(&RFC9383, &[0; MAX_LABEL + 1], b"", b"").err(),
            Some(Error::WrongLength)
        );
    }

    /// A share loads only as the uncompressed encoding of a point on P-256,
    /// and a label of exactly `MAX_LABEL` bytes is accepted.
    #[test]
    #[inline]
    fn share_and_label_edges() {
        let prover = ProverSecrets::new(&[0x11; 40], &[0x22; 40]).unwrap();
        let (share_p, _) = prover.start(&RFC9383, b"ctx", b"a", b"b").unwrap();
        let good = share_p.bytes;
        let rejected = |bytes: &[u8]| Share::<Rfc9383>::from_bytes(bytes).is_err();
        assert!(!rejected(&good));

        // P-256's field prime, big-endian.
        let mut p = [0u8; 32];
        p[..4].copy_from_slice(&[0xff; 4]);
        p[7] = 1;
        p[20..].copy_from_slice(&[0xff; 12]);
        // A coordinate at p or above is not canonical.
        for coordinate in [1..33, 33..65] {
            let mut at_p = good;
            at_p[coordinate.clone()].copy_from_slice(&p);
            assert!(rejected(&at_p));
            let mut above = good;
            above[coordinate].copy_from_slice(&[0xff; 32]);
            assert!(rejected(&above));
        }
        // Only the uncompressed tag, and not the compressed encoding.
        for tag in [0x00, 0x02, 0x03, 0x06, 0x07] {
            let mut tagged = good;
            tagged[0] = tag;
            assert!(rejected(&tagged));
        }
        let mut compressed = [0u8; 33];
        compressed[0] = 0x02 | (good[64] & 1);
        compressed[1..].copy_from_slice(&good[1..33]);
        assert!(rejected(&compressed));
        // (0, 0), the identity's affine image, and SEC1's identity byte.
        let mut zero = [0u8; 65];
        zero[0] = 0x04;
        assert!(rejected(&zero));
        assert!(rejected(&[0x00]));
        assert!(rejected(&[]));

        let max: &[u8] = &[0x61; MAX_LABEL];
        let over: &[u8] = &[0x61; MAX_LABEL + 1];
        let none: &[u8] = b"";
        for (context, id_p, id_v) in [(max, none, none), (none, max, max)] {
            assert!(prover.start(&RFC9383, context, id_p, id_v).is_ok());
        }
        for (context, id_p, id_v) in [(over, none, none), (none, over, none), (none, none, over)] {
            assert_eq!(
                prover.start(&RFC9383, context, id_p, id_v).err(),
                Some(Error::WrongLength)
            );
        }
        let verifier = VerifierRecord::from_w1(&[0x11; 40], &[0x22; 40]).unwrap();
        let (share_p, _) = prover.start(&RFC9383, max, max, max).unwrap();
        assert!(verifier.start(&RFC9383, max, max, max, &share_p).is_ok());
        assert_eq!(
            verifier.start(&RFC9383, over, none, none, &share_p).err(),
            Some(Error::WrongLength)
        );
    }

    /// A stored record loads only as uncompressed `L` on the curve.
    ///
    /// A zero `w0` is a residue, not a malformed encoding. `zero_residue_fails_closed`
    /// rejects it at confirmation.
    #[test]
    #[inline]
    fn from_record_rejects_a_malformed_record() {
        let w0 = [0x11; 40];
        let l = VerifierRecord::from_w1(&w0, &[0x22; 40]).unwrap().l();
        assert!(VerifierRecord::from_record(&w0, &l).is_ok());
        let rejected = |l: &[u8]| {
            matches!(
                VerifierRecord::from_record(&w0, l).err(),
                Some(Error::KeyRejected(_))
            )
        };
        let mut off = l;
        off[40] ^= 1;
        assert!(rejected(&off));
        let mut compressed = [0u8; 33];
        compressed[0] = 2 | (l[64] & 1);
        compressed[1..].copy_from_slice(&l[1..33]);
        assert!(rejected(&compressed));
        assert!(rejected(&l[..64]));
        assert!(rejected(&[]));
        let mut identity = [0u8; 65];
        identity[0] = 4;
        assert!(rejected(&identity));
    }

    /// A zero residue is not reported by reduction. Both sides still run the
    /// handshake, then fail with the same error as a bad tag, including when
    /// that tag would match. A zero scalar's messages are the identity's, so
    /// they are not the messages of scalar 1.
    #[test]
    #[inline]
    fn zero_residue_fails_closed() {
        let zero = [0u8; 40];
        let normal = [0x22u8; 40];
        let mut scalar_one = [0u8; 32];
        scalar_one[31] = 1;
        ct::secret_slice(&zero);
        ct::secret_slice(&normal);
        ct::secret_slice(&scalar_one);

        for (w0, w1) in [
            (zero.as_slice(), normal.as_slice()),
            (normal.as_slice(), zero.as_slice()),
            (zero.as_slice(), zero.as_slice()),
        ] {
            let prover = ProverSecrets::new(w0, w1).unwrap();
            let verifier = VerifierRecord::from_w1(w0, w1).unwrap();
            let (share_p, prover) = prover.start(&RFC9383, b"ctx", b"a", b"b").unwrap();
            let (share_v, confirm_v, verifier) = verifier
                .start(&RFC9383, b"ctx", b"a", b"b", &share_p)
                .unwrap();
            assert_eq!(
                prover.finish(&share_v, &confirm_v).err(),
                Some(Error::BadSignature)
            );
            // The stored tag matches itself. Failure is the zero residue.
            let expected = verifier.confirm_p;
            assert_eq!(
                verifier.finish(&confirm_of::<Rfc9383>(expected)).err(),
                Some(Error::BadSignature)
            );
        }

        let n = hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
        ct::secret_slice(&n);
        let prover = ProverSecrets::new(&n, &normal).unwrap();
        let verifier = VerifierRecord::from_w1(&n, &normal).unwrap();
        let (share_p, prover) = prover.start(&RFC9383, b"ctx", b"a", b"b").unwrap();
        let (share_v, confirm_v, _) = verifier
            .start(&RFC9383, b"ctx", b"a", b"b", &share_p)
            .unwrap();
        assert_eq!(
            prover.finish(&share_v, &confirm_v).err(),
            Some(Error::BadSignature)
        );

        let x = scalar("0000000000000000000000000000000000000000000000000000000000000007");
        let y = scalar("000000000000000000000000000000000000000000000000000000000000000b");
        let (share_p, _) = ProverSecrets::new(&zero, &normal)
            .unwrap()
            .start_at(&RFC9383, b"ctx", b"a", b"b", Some(x.copy()))
            .unwrap();
        let expect = Affine::mul_base(&x).to_uncompressed();
        ct::public_slice(&expect);
        ct::public_slice(share_p.as_ref());
        assert_eq!(share_p.as_ref(), &expect);
        let (share_v, _, _) = VerifierRecord::from_w1(&zero, &normal)
            .unwrap()
            .start_at(&RFC9383, b"ctx", b"a", b"b", &share_p, Some(y.copy()))
            .unwrap();
        let expect_v = Affine::mul_base(&y).to_uncompressed();
        ct::public_slice(&expect_v);
        ct::public_slice(share_v.as_ref());
        assert_eq!(share_v.as_ref(), &expect_v);

        // The tags are the identity's: `0 * P` contributes nothing, and a
        // zero `w1` contributes the identity encoding. The mask is what
        // rejects them. A substitute of scalar 1 would not match.
        // Honest shares cancel `w0`, so `Z` is `x*y*G` whether or not `w0`
        // is zero. A zero `w1` puts the identity encoding in `V`.
        let w1s = Scalar::from_be_reduced(&normal).unwrap();
        let z = Affine::mul_base(&x).mul(&y).to_uncompressed();
        let v = Affine::mul_base(&w1s).mul(&y).to_uncompressed();
        let identity = identity_point();
        tags_match_transcript(&zero, &normal, &x, &y, &z, &v);
        tags_match_transcript(&normal, &zero, &x, &y, &z, &identity);
        tags_match_transcript(&zero, &zero, &x, &y, &z, &identity);

        refuses_alias(&zero, &normal, &scalar_one, &normal, &x, &y);
        refuses_alias(&normal, &zero, &normal, &scalar_one, &x, &y);

        let l = VerifierRecord::from_w1(&normal, &normal).unwrap().l();
        let loaded = VerifierRecord::from_record(&zero, &l).unwrap();
        let (share_p, prover) = ProverSecrets::new(&zero, &normal)
            .unwrap()
            .start(&RFC9383, b"ctx", b"a", b"b")
            .unwrap();
        let (share_v, confirm_v, verifier) = loaded
            .start(&RFC9383, b"ctx", b"a", b"b", &share_p)
            .unwrap();
        assert_eq!(
            prover.finish(&share_v, &confirm_v).err(),
            Some(Error::BadSignature)
        );
        let expected = verifier.confirm_p;
        assert_eq!(
            verifier.finish(&confirm_of::<Rfc9383>(expected)).err(),
            Some(Error::BadSignature)
        );

        let identity_l = VerifierRecord::from_w1(&normal, &zero).unwrap().l();
        let mut identity = [0u8; 65];
        identity[0] = 4;
        assert_eq!(identity_l, identity);
    }

    #[inline]
    fn identity_point() -> [u8; 65] {
        let mut bytes = [0u8; 65];
        bytes[0] = 4;
        bytes
    }

    /// Both sides' tags match a transcript built with `z` and `v`, and the
    /// handshake still fails. `z` and `v` are the identity arithmetic, so a
    /// wrong product (scalar 1, or a negation of `(0, 0)` that is not the
    /// identity) fails this before the mask does.
    #[inline]
    fn tags_match_transcript(w0: &[u8], w1: &[u8], x: &Scalar, y: &Scalar, z: &[u8], v: &[u8]) {
        let (share_p, prover) = ProverSecrets::new(w0, w1)
            .unwrap()
            .start_at(&RFC9383, b"ctx", b"a", b"b", Some(x.copy()))
            .unwrap();
        let (share_v, confirm_v, verifier) = VerifierRecord::from_w1(w0, w1)
            .unwrap()
            .start_at(&RFC9383, b"ctx", b"a", b"b", &share_p, Some(y.copy()))
            .unwrap();
        let reduced = Scalar::from_be_reduced(w0).unwrap();
        let labels = Labels::new(b"ctx", b"a", b"b").unwrap();
        let tt = transcript(&labels, share_p.as_ref(), share_v.as_ref(), z, v, &reduced);
        let keys = schedule_keys(Schedule::Rfc9383, &tt).unwrap();
        let expect_v = mac::<Rfc9383>(keys.verifier_key(), share_p.as_ref());
        assert!(ct::into_public(ct_equal(
            confirm_v.as_ref(),
            expect_v.as_ref()
        )));
        let (confirm_p, _key, ok) = prover.compute(&share_v, &confirm_v).unwrap();
        let expect_p = mac::<Rfc9383>(keys.prover_key(), share_v.as_ref());
        assert!(ct::into_public(ct_equal(
            confirm_p.as_ref(),
            expect_p.as_ref()
        )));
        assert_eq!(ct::into_public(ok), 0);
        assert_eq!(verifier.finish(&confirm_p).err(), Some(Error::BadSignature));
    }

    #[inline]
    fn refuses_alias(pw0: &[u8], pw1: &[u8], vw0: &[u8], vw1: &[u8], x: &Scalar, y: &Scalar) {
        let (share_p, prover) = ProverSecrets::new(pw0, pw1)
            .unwrap()
            .start_at(&RFC9383, b"ctx", b"a", b"b", Some(x.copy()))
            .unwrap();
        let (share_v, confirm_v, verifier) = VerifierRecord::from_w1(vw0, vw1)
            .unwrap()
            .start_at(&RFC9383, b"ctx", b"a", b"b", &share_p, Some(y.copy()))
            .unwrap();
        let (confirm_p, _key, ok) = prover.compute(&share_v, &confirm_v).unwrap();
        assert_eq!(ct::into_public(ok), 0);
        assert_eq!(verifier.finish(&confirm_p).err(), Some(Error::BadSignature));
    }

    /// `X = -w0*M` is a doubling and still confirms. `X = w0*M` makes the
    /// difference the identity; that is rejected after the same multiplication
    /// rather than encoded, and `(0, 0)` is not a scalar-multiplication input.
    /// `Y = w0*N` is the prover's matching case. The tags are those of the
    /// generator standing in for that difference, and a tag that matches them
    /// is still refused.
    #[test]
    #[inline]
    fn exceptional_peer_share_follows_rfc9383() {
        let w0 = [0x31u8; 40];
        let w1 = [0x41u8; 40];
        let w0s = Scalar::from_be_reduced(&w0).unwrap();
        let w1s = Scalar::from_be_reduced(&w1).unwrap();
        let y = scalar("000000000000000000000000000000000000000000000000000000000000000b");
        let x = scalar("0000000000000000000000000000000000000000000000000000000000000007");
        let two = Scalar::from_be_reduced(&[2]).unwrap();
        let (m, n) = points().unwrap();
        let labels = Labels::new(b"ctx", b"client", b"").unwrap();

        let negated = m.mul(&w0s).negate();
        let share_x = point_share::<Rfc9383>(negated.to_uncompressed());
        let share_v =
            point_share::<Rfc9383>(n.mul(&w0s).add(Affine::mul_base(&y)).to_uncompressed());
        let z = negated.mul(&two).mul(&y);
        let v = Affine::mul_base(&w1s).mul(&y);
        let tt = transcript(
            &labels,
            share_x.as_ref(),
            share_v.as_ref(),
            &z.to_uncompressed(),
            &v.to_uncompressed(),
            &w0s,
        );
        let keys = schedule_keys(Schedule::Rfc9383, &tt).unwrap();
        let verifier = VerifierRecord::from_w1(&w0, &w1).unwrap();
        let (got_share, got_confirm, state) = verifier
            .start_at(&RFC9383, b"ctx", b"client", b"", &share_x, Some(y.copy()))
            .unwrap();
        assert_eq!(got_share.as_ref(), share_v.as_ref());
        assert_eq!(
            got_confirm.as_ref(),
            sent(mac::<Rfc9383>(keys.verifier_key(), share_x.as_ref())).as_ref()
        );
        let key = state
            .finish(&sent(mac::<Rfc9383>(keys.prover_key(), share_v.as_ref())))
            .unwrap();
        ct::public_slice(key.as_ref());
        ct::public_slice(keys.shared());
        assert_eq!(key.as_ref(), keys.shared());

        // X = w0*M makes the difference the identity. The verifier rejects it.
        let share_x = point_share::<Rfc9383>(m.mul(&w0s).to_uncompressed());
        let verifier = VerifierRecord::from_w1(&w0, &w1).unwrap();
        assert_eq!(
            verifier
                .start_at(&RFC9383, b"ctx", b"client", b"", &share_x, Some(y.copy()))
                .err(),
            Some(Error::BadSignature)
        );

        // The prover's subtraction, Y = -w0*N.
        let prover = ProverSecrets::new(&w0, &w1).unwrap();
        let (share_p, prover) = prover
            .start_at(&RFC9383, b"ctx", b"client", b"", Some(x.copy()))
            .unwrap();
        let negated = n.mul(&w0s).negate();
        let share_y = point_share::<Rfc9383>(negated.to_uncompressed());
        let diff = negated.mul(&two);
        let z = diff.mul(&x);
        let v = diff.mul(&w1s);
        let tt = transcript(
            &labels,
            share_p.as_ref(),
            share_y.as_ref(),
            &z.to_uncompressed(),
            &v.to_uncompressed(),
            &w0s,
        );
        let keys = schedule_keys(Schedule::Rfc9383, &tt).unwrap();
        let (confirm_p, key) = prover
            .finish(
                &share_y,
                &sent(mac::<Rfc9383>(keys.verifier_key(), share_p.as_ref())),
            )
            .unwrap();
        assert_eq!(
            confirm_p.as_ref(),
            sent(mac::<Rfc9383>(keys.prover_key(), share_y.as_ref())).as_ref()
        );
        ct::public_slice(key.as_ref());
        ct::public_slice(keys.shared());
        assert_eq!(key.as_ref(), keys.shared());

        // Y = w0*N makes the prover's difference the identity. Multiplication
        // uses the generator, so Z is x*G and V is w1*G. A confirmation that
        // matches that transcript is still rejected: the identity mask fails,
        // not a mismatched tag.
        let z = Affine::mul_base(&x).to_uncompressed();
        let v = Affine::mul_base(&w1s).to_uncompressed();
        let (share_p, prover) = ProverSecrets::new(&w0, &w1)
            .unwrap()
            .start_at(&RFC9383, b"ctx", b"client", b"", Some(x.copy()))
            .unwrap();
        let share_y = point_share::<Rfc9383>(n.mul(&w0s).to_uncompressed());
        let tt = transcript(&labels, share_p.as_ref(), share_y.as_ref(), &z, &v, &w0s);
        let keys = schedule_keys(Schedule::Rfc9383, &tt).unwrap();
        let confirm_v = mac::<Rfc9383>(keys.verifier_key(), share_p.as_ref());
        let (confirm_p, _key, ok) = prover.compute(&share_y, &confirm_v).unwrap();
        assert!(ct::into_public(ct_equal(
            confirm_p.as_ref(),
            mac::<Rfc9383>(keys.prover_key(), share_y.as_ref()).as_ref(),
        )));
        assert_eq!(ct::into_public(ok), 0);
        let (_, prover) = ProverSecrets::new(&w0, &w1)
            .unwrap()
            .start_at(&RFC9383, b"ctx", b"client", b"", Some(x))
            .unwrap();
        assert_eq!(
            prover.finish(&share_y, &confirm_v).err(),
            Some(Error::BadSignature)
        );
    }

    /// Hostile share and record encodings are refused: SEC 1's identity,
    /// `(0, 0)`, compressed and hybrid forms, wrong lengths, an off-curve
    /// point, and coordinates at or above p. So are `w0` and `w1` values
    /// that are empty or past 128 bytes. A `w0` or `w1` that is zero mod n
    /// still loads; `zero_residue_fails_closed` covers its handshake.
    #[test]
    #[inline]
    fn refuses_malformed_encodings() {
        const P: &str = "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff";
        const N: &str = "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551";
        let g = hex(
            "046b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c2964fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
        );
        let p = hex(P);
        let with = |at: usize, bytes: &[u8]| {
            let mut out = g.clone();
            out[at..at + bytes.len()].copy_from_slice(bytes);
            out
        };
        let mut off_curve = g.clone();
        off_curve[64] ^= 1;
        let bad: Vec<Vec<u8>> = vec![
            vec![],
            vec![0x00],
            [&[0x00][..], &[0; 64]].concat(),
            [&[0x04][..], &[0; 64]].concat(),
            [&[0x02][..], &g[1..33]].concat(),
            [&[0x03][..], &g[1..33]].concat(),
            with(0, &[0x06]),
            with(0, &[0x07]),
            g[..64].to_vec(),
            [&g[..], &[0][..]].concat(),
            off_curve,
            with(1, &p),
            with(33, &p),
            with(1, &[0xff; 32]),
            with(33, &[0xff; 32]),
        ];
        for bytes in &bad {
            assert!(Share::<Rfc9383>::from_bytes(bytes).is_err(), "{bytes:02x?}");
            assert!(
                Share::<MatterPase>::from_bytes(bytes).is_err(),
                "{bytes:02x?}"
            );
            assert!(
                VerifierRecord::from_record(&[0x11; 32], bytes).is_err(),
                "{bytes:02x?}"
            );
        }

        let n = hex(N);
        let wide_n = [&[0u8; 8][..], &n].concat();
        for w in [&[][..], &[0x11; 129][..]] {
            assert!(ProverSecrets::new(w, &[0x22; 32]).is_err());
            assert!(ProverSecrets::new(&[0x22; 32], w).is_err());
            assert!(VerifierRecord::from_w1(w, &[0x22; 32]).is_err());
            assert!(VerifierRecord::from_w1(&[0x22; 32], w).is_err());
            assert!(VerifierRecord::from_record(w, &g).is_err());
        }
        // A zero residue is not an encoding error: it loads, and the
        // handshake fails closed, as `zero_residue_fails_closed` checks.
        for w in [&[0; 32][..], &n, &wide_n] {
            assert!(ProverSecrets::new(w, &[0x22; 32]).is_ok());
            assert!(ProverSecrets::new(&[0x22; 32], w).is_ok());
            assert!(VerifierRecord::from_w1(w, &[0x22; 32]).is_ok());
            assert!(VerifierRecord::from_w1(&[0x22; 32], w).is_ok());
            assert!(VerifierRecord::from_record(w, &g).is_ok());
        }

        // The stored form round-trips: `l` is a point `from_record` loads.
        let record = VerifierRecord::from_w1(&[0x11; 40], &[0x22; 40]).unwrap();
        let l = record.l();
        let loaded = VerifierRecord::from_record(&[0x11; 40], &l).unwrap();
        assert_eq!(loaded.l(), l);
    }

    #[test]
    #[inline]
    fn m_and_n_match_their_compressed_form() {
        let _entry = Entry::new_public();
        assert_eq!(
            Affine::from_compressed(&M_COMPRESSED)
                .unwrap()
                .to_uncompressed(),
            M_UNCOMPRESSED
        );
        assert_eq!(
            Affine::from_compressed(&N_COMPRESSED)
                .unwrap()
                .to_uncompressed(),
            N_UNCOMPRESSED
        );
    }

    #[inline]
    fn point_share<S>(bytes: [u8; 65]) -> Share<S> {
        // Built from secret scalars, then parsed as a public share. The
        // encoding check branches; the bytes are public by the time it runs.
        ct::public_slice(&bytes);
        Share {
            bytes,
            _kind: PhantomData,
        }
    }

    #[inline]
    fn confirm_of<S>(bytes: [u8; 32]) -> Confirm<S> {
        Confirm {
            bytes,
            _kind: PhantomData,
        }
    }

    #[test]
    #[inline]
    fn suites_do_not_agree() {
        let w0 = [0x31; 32];
        let w1 = [0x41; 32];
        let x = scalar("0000000000000000000000000000000000000000000000000000000000000007");
        let y = scalar("000000000000000000000000000000000000000000000000000000000000000b");
        #[inline]
        fn exchange<S: 'static>(
            suite: &'static Suite<S>,
            w0: &[u8],
            w1: &[u8],
            x: &Scalar,
            y: &Scalar,
        ) -> Vec<u8> {
            let prover = ProverSecrets::new(w0, w1).unwrap();
            let verifier = VerifierRecord::from_w1(w0, w1).unwrap();
            let (share_p, prover) = prover
                .start_at(suite, b"ctx", b"client", b"", Some(x.copy()))
                .unwrap();
            let (share_v, confirm_v, verifier) = verifier
                .start_at(suite, b"ctx", b"client", b"", &share_p, Some(y.copy()))
                .unwrap();
            let (confirm_p, key) = prover.finish(&share_v, &confirm_v).unwrap();
            let other = verifier.finish(&confirm_p).unwrap();
            ct::public_slice(key.as_ref());
            ct::public_slice(other.as_ref());
            assert_eq!(key.as_ref(), other.as_ref());
            key.as_ref().to_vec()
        }
        assert_ne!(
            exchange(&RFC9383, &w0, &w1, &x, &y),
            exchange(&MATTER_PASE, &w0, &w1, &x, &y)
        );
    }

    /// Matter PASE, through `matter-crypto` 0.5.1's public state machine with
    /// its test scalars. The context is SHA-256 of "CHIP PAKE V1 Commissioning",
    /// and both identities are empty.
    #[test]
    #[cfg(not(any(miri, target_family = "wasm")))]
    #[inline]
    fn matches_matter_crypto() {
        use core::num::NonZeroU32;

        let pin = 202_021u32;
        let salt = [0x42u8; 16];
        let mut stretched = [0u8; 80];
        crate::pbkdf2::Secret::new(&crate::pbkdf2::PBKDF2_HMAC_SHA256, &pin.to_le_bytes())
            .derive(NonZeroU32::new(1000).unwrap(), &salt, &mut stretched)
            .unwrap();
        let (w0, w1) = stretched.split_at(40);
        let verifier_blob = matter_crypto::pake_passcode_verifier(pin, &salt, 1000).unwrap();
        let record = VerifierRecord::from_w1(w0, w1).unwrap();
        let w0_reduced = Scalar::from_be_reduced(w0).unwrap().as_bytes();
        // matter-crypto's verifier blob is public. Declassify the reduced
        // scalar before comparing it.
        ct::public_slice(&w0_reduced);
        assert_eq!(&verifier_blob[..32], w0_reduced.as_slice());
        assert_eq!(&verifier_blob[32..], record.l.to_uncompressed().as_slice());

        let mut x_bytes = [0u8; 32];
        x_bytes[31] = 7;
        let mut y_bytes = [0u8; 32];
        y_bytes[31] = 11;
        let params = matter_crypto::PasePbkdfParams {
            iterations: 1000,
            salt: salt.to_vec(),
        };
        let mut their_prover =
            matter_crypto::test_support::prover_with_scalar(pin, params.clone(), x_bytes).unwrap();
        let w0_be: [u8; 32] = verifier_blob[..32].try_into().unwrap();
        let l: [u8; 65] = verifier_blob[32..].try_into().unwrap();
        let mut their_verifier =
            matter_crypto::test_support::verifier_with_scalar(w0_be, l, params, y_bytes).unwrap();
        let pake1 = their_prover.start().unwrap();
        their_verifier.handle_pake1(&pake1).unwrap();
        let pake2 = their_verifier.next_message().unwrap();
        their_prover.handle_pake2(&pake2).unwrap();
        let pake3 = their_prover.next_message().unwrap();
        their_verifier.handle_pake3(&pake3).unwrap();
        let their_key = their_prover.finish().unwrap();
        assert_eq!(their_key.ke, their_verifier.finish().unwrap().ke);

        let mut ctx = digest::Context::new(&digest::SHA256);
        ctx.update(b"CHIP PAKE V1 Commissioning");
        let context = ctx.finish();
        let prover = ProverSecrets::new(w0, w1).unwrap();
        let verifier = VerifierRecord::from_record(w0, &l).unwrap();
        let (share_p, prover) = prover
            .start_at(
                &MATTER_PASE,
                context.as_ref(),
                b"",
                b"",
                Some(Scalar::from_be_reduced(&x_bytes).unwrap()),
            )
            .unwrap();
        let (share_v, confirm_v, verifier) = verifier
            .start_at(
                &MATTER_PASE,
                context.as_ref(),
                b"",
                b"",
                &share_p,
                Some(Scalar::from_be_reduced(&y_bytes).unwrap()),
            )
            .unwrap();
        let (confirm_p, key) = prover.finish(&share_v, &confirm_v).unwrap();
        let key_v = verifier.finish(&confirm_p).unwrap();
        ct::public_slice(key.as_ref());
        ct::public_slice(key_v.as_ref());
        assert_eq!(key.as_ref(), key_v.as_ref());
        assert_eq!(key.as_ref(), their_key.ke.as_slice());
    }

    #[test]
    #[inline]
    fn secrets_stay_secret() {
        // Under `admin/ctgrind`, nothing may branch on w0, w1, or the
        // ephemeral scalars until the confirmation tags and, in this test,
        // the shared key are declassified. `from_record` loads that same
        // secret `w0`; the stored point `L` is public. A residue of zero is
        // `zero_residue_fails_closed`: it stays secret until that same check.
        let w0 = [0x5a; 40];
        let w1 = [0xa5; 40];
        ct::secret_slice(&w0);
        ct::secret_slice(&w1);
        #[inline]
        fn one<S: 'static>(suite: &'static Suite<S>, w0: &[u8], w1: &[u8]) {
            let verifier = VerifierRecord::from_w1(w0, w1).unwrap();
            let l = verifier.l();
            ct::public_slice(&l);
            exchange(suite, ProverSecrets::new(w0, w1).unwrap(), verifier);
            exchange(
                suite,
                ProverSecrets::new(w0, w1).unwrap(),
                VerifierRecord::from_record(w0, &l).unwrap(),
            );
        }
        #[inline]
        fn exchange<S: 'static>(
            suite: &'static Suite<S>,
            prover: ProverSecrets,
            verifier: VerifierRecord,
        ) {
            let (share_p, prover) = prover
                .start(suite, b"CHIP", b"commissionee", b"commissioner")
                .unwrap();
            let (share_v, confirm_v, verifier) = verifier
                .start(suite, b"CHIP", b"commissionee", b"commissioner", &share_p)
                .unwrap();
            let (confirm_p, key_p) = prover.finish(&share_v, &confirm_v).unwrap();
            let key_v = verifier.finish(&confirm_p).unwrap();
            ct::public_slice(key_p.as_ref());
            ct::public_slice(key_v.as_ref());
            assert_eq!(key_p.as_ref(), key_v.as_ref());
            // `finish` declassified the tag it sends. Mark it secret again so `==` is
            // checked the same way as the password scalars.
            ct::secret_slice(confirm_p.as_ref());
            assert_eq!(confirm_p, confirm_of::<S>(confirm_p.bytes));
            let mut flipped = confirm_p.bytes;
            flipped[0] ^= 1;
            ct::secret_slice(&flipped);
            assert_ne!(confirm_p, confirm_of::<S>(flipped));
        }
        one(&RFC9383, &w0, &w1);
        one(&MATTER_PASE, &w0, &w1);
    }
}
