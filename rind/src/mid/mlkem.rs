// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-KEM as standardised by FIPS-203, at each of its parameter sets.

use core::fmt;
use core::marker::PhantomData;
use core::panic::{RefUnwindSafe, UnwindSafe};

use crate::error::{Error, KeyFormatError};
use crate::low;
use crate::{
    low::{ct_copy, ct_equal, ct_select_i16},
    mid::{
        rng::{RandomSource, SystemRandom},
        sha3,
    },
};

mod sample_ntt;

/// ML-KEM-512, as standardised by FIPS-203.
#[derive(Debug)]
pub enum MlKem512 {}

/// ML-KEM-768, as standardised by FIPS-203.
#[derive(Debug)]
pub enum MlKem768 {}

/// ML-KEM-1024, as standardised by FIPS-203.
#[derive(Debug)]
pub enum MlKem1024 {}

/// A FIPS-203 parameter set: its rank `K`, noise `ETA1`, and compression
/// widths `DU` and `DV`, with the arrays they size, which stable Rust cannot
/// compute from the constants.
///
/// Its bounds, like [`Array`]'s, let a generic caller rely on the auto
/// traits every key and ciphertext has.
pub trait Params: fmt::Debug + Send + Sync + Unpin + UnwindSafe + RefUnwindSafe + 'static {
    #[doc(hidden)]
    const K: usize;
    #[doc(hidden)]
    const ETA1: usize;
    #[doc(hidden)]
    const DU: usize;
    #[doc(hidden)]
    const DV: usize;
    /// `K` polynomials.
    #[doc(hidden)]
    type Vector: Vector;
    /// `K * K` polynomials, row by row.
    #[doc(hidden)]
    type Matrix: Array<Poly>;
    /// An encoded encapsulation key: `384 * K + 32` bytes.
    #[doc(hidden)]
    type EncapKeyBytes: Array<u8>;
    /// A ciphertext: `32 * (DU * K + DV)` bytes.
    #[doc(hidden)]
    type CiphertextBytes: Array<u8>;
    /// An expanded decapsulation key: `768 * K + 96` bytes.
    #[cfg(test)]
    type DecapKeyBytes: Array<u8>;
    /// FIPS-203's name for the set.
    #[cfg(test)]
    const NAME: &'static str;
}

impl Params for MlKem512 {
    const K: usize = 2;
    const ETA1: usize = 3;
    const DU: usize = 10;
    const DV: usize = 4;
    type Vector = [Poly; 2];
    type Matrix = [Poly; 4];
    type EncapKeyBytes = [u8; 800];
    type CiphertextBytes = [u8; 768];
    #[cfg(test)]
    type DecapKeyBytes = [u8; 1632];
    #[cfg(test)]
    const NAME: &'static str = "ML-KEM-512";
}

impl Params for MlKem768 {
    const K: usize = 3;
    const ETA1: usize = 2;
    const DU: usize = 10;
    const DV: usize = 4;
    type Vector = [Poly; 3];
    type Matrix = [Poly; 9];
    type EncapKeyBytes = [u8; 1184];
    type CiphertextBytes = [u8; 1088];
    #[cfg(test)]
    type DecapKeyBytes = [u8; 2400];
    #[cfg(test)]
    const NAME: &'static str = "ML-KEM-768";
}

impl Params for MlKem1024 {
    const K: usize = 4;
    const ETA1: usize = 2;
    const DU: usize = 11;
    const DV: usize = 5;
    type Vector = [Poly; 4];
    type Matrix = [Poly; 16];
    type EncapKeyBytes = [u8; 1568];
    type CiphertextBytes = [u8; 1568];
    #[cfg(test)]
    type DecapKeyBytes = [u8; 3168];
    #[cfg(test)]
    const NAME: &'static str = "ML-KEM-1024";
}

/// A fixed-size array, of a length a [`Params`] picks.
pub trait Array<T>:
    Clone
    + fmt::Debug
    + AsRef<[T]>
    + AsMut<[T]>
    + Send
    + Sync
    + Unpin
    + UnwindSafe
    + RefUnwindSafe
    + 'static
{
    /// Every element `value`.
    #[doc(hidden)]
    fn filled(value: T) -> Self;

    /// `slice`, if it is this array's length.
    #[doc(hidden)]
    fn from_slice(slice: &[T]) -> Option<Self>;
}

impl<T, const L: usize> Array<T> for [T; L]
where
    T: Copy + fmt::Debug + Send + Sync + Unpin + UnwindSafe + RefUnwindSafe + 'static,
{
    fn filled(value: T) -> Self {
        [value; L]
    }

    fn from_slice(slice: &[T]) -> Option<Self> {
        slice.try_into().ok()
    }
}

/// `K` polynomials, with the arrays of their mulcaches and encodings.
pub trait Vector: Array<Poly> {
    /// `K` mulcaches.
    #[doc(hidden)]
    type MulCache: Array<[i16; N / 2]>;
    /// `K` encoded polynomials.
    #[doc(hidden)]
    type Encoded: Array<[u8; 384]>;
}

impl Vector for [Poly; 2] {
    type MulCache = [[i16; N / 2]; 2];
    type Encoded = [[u8; 384]; 2];
}

impl Vector for [Poly; 3] {
    type MulCache = [[i16; N / 2]; 3];
    type Encoded = [[u8; 384]; 3];
}

impl Vector for [Poly; 4] {
    type MulCache = [[i16; N / 2]; 4];
    type Encoded = [[u8; 384]; 4];
}

/// A parameter set's `K` encoded polynomials.
type Encoded<P> = <<P as Params>::Vector as Vector>::Encoded;

/// An ML-KEM decapsulation key.
pub(crate) struct DecapKey<P: Params> {
    ek_pke: EncapKey<P>,
    dk_pke: Encoded<P>,
    z: [u8; 32],
}

impl<P: Params> DecapKey<P> {
    /// Generate a random [`DecapKey`] (which contains the corresponding [`EncapKey`]).
    ///
    /// This fails only if random material generation fails.
    pub(crate) fn generate() -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        let mut seed = [0u8; 64];
        SystemRandom.fill(&mut seed)?;
        Ok(Self::keygen_internal(&seed))
    }

    /// Decapsulate ciphertext `c`, yielding a [`SharedSecret`].
    pub(crate) fn decaps(&self, c: &Ciphertext<P>) -> SharedSecret {
        let _entry = low::Entry::new_secret();
        self.decaps_internal(c)
    }

    /// Return the corresponding [`EncapKey`].
    pub(crate) fn encapsulation_key(&self) -> EncapKey<P> {
        let _entry = low::Entry::new_public();
        self.ek_pke.clone()
    }

    /// Encode the key as bytes.
    ///
    /// This is used for testing.
    #[cfg(test)]
    pub(crate) fn as_bytes(&self) -> P::DecapKeyBytes {
        let _entry = low::Entry::new_secret();
        let mut out = P::DecapKeyBytes::filled(0);
        let (dk_pke, rest) = out.as_mut().split_at_mut(P::K * 384);
        let (ek, rest) = rest.split_at_mut(P::K * 384 + 32);
        let (h_ek, z) = rest.split_at_mut(32);
        dk_pke.copy_from_slice(self.dk_pke.as_ref().as_flattened());
        ek.copy_from_slice(self.ek_pke.as_bytes().as_ref());
        h_ek.copy_from_slice(&self.ek_pke.h_ek);
        z.copy_from_slice(&self.z);
        out
    }

    /// Decode a key encoded as [`Self::as_bytes()`] encodes it, or `None` if
    /// its `H(ek)` is not that of its encapsulation key.
    ///
    /// This is used for testing: rind generates keys only from seeds.
    #[cfg(test)]
    pub(crate) fn from_bytes(dk: &P::DecapKeyBytes) -> Option<Self> {
        let (dk_pke, rest) = dk.as_ref().split_at(P::K * 384);
        let (ek, rest) = rest.split_at(P::K * 384 + 32);
        let (h_ek, z) = rest.split_at(32);
        let ek_pke = EncapKey::from_bytes(&P::EncapKeyBytes::from_slice(ek).unwrap()).ok()?;
        let mut encoded = Encoded::<P>::filled([0; 384]);
        encoded.as_mut().as_flattened_mut().copy_from_slice(dk_pke);
        (ek_pke.h_ek == h_ek).then(|| Self {
            ek_pke,
            dk_pke: encoded,
            z: z.try_into().unwrap(),
        })
    }

    pub(crate) fn keygen_internal(seed: &[u8; 64]) -> Self {
        // Preliminaries: split seed into d and z.
        let (d, z) = seed.split_at(32);
        let d = low::ct::into_secret(d.try_into().unwrap());

        // 1. (ekPKE, dkPKE) <- K-PKE.KeyGen(d)
        // 2. ek <- ekPKE
        let (ek_pke, dk_pke) = Self::kpke_keygen(&d);

        // 3. dk <- (dkPKE || ek || H(ek) || z)
        // 4. return (ek, dk)
        Self {
            dk_pke,
            ek_pke,
            z: low::ct::into_secret(z.try_into().unwrap()),
        }
    }

    fn decaps_internal(&self, c: &Ciphertext<P>) -> SharedSecret {
        // Steps 1. - 4. are not relevant for us.
        // 5. m' <- K-PKE.Decrypt(dkPKE, c)
        let m_prime = self.kpke_decrypt(c);

        // 6. (K', r') <- G(m' || h)
        let mut g = sha3::Sha3_512Context::new();
        g.update(&m_prime.0);
        g.update(&self.ek_pke.h_ek);
        let kr_prime = g.finish();
        let (k_prime, r_prime) = kr_prime.split_at(32);
        let mut k_prime = SharedSecret(k_prime.try_into().unwrap());
        let r_prime = KpkeRandomness(r_prime.try_into().unwrap());

        // 7. K‾ <- J(z || c)
        let mut k_bar = SharedSecret([0u8; 32]);
        let mut j = sha3::Shake256Sponge::new();
        j.absorb(&self.z);
        j.absorb(c.0.as_ref());
        j.finish().squeeze(&mut k_bar.0);

        // 8. c' <- K-PKE.Encrypt(ekPKE, m', r')
        let c_prime = self.ek_pke.kpke_encrypt(m_prime, r_prime);

        // 9. - 11. if c != c' then K' <- K‾
        // 12. return K'
        ct_copy(
            ct_equal(c.0.as_ref(), c_prime.0.as_ref()),
            &mut k_prime.0,
            &k_bar.0,
        );
        k_prime
    }

    /// This is Algorithm 13: K-PKE.KeyGen(d) -> (ek_PKE, dk_PKE)
    fn kpke_keygen(d: &[u8; 32]) -> (EncapKey<P>, Encoded<P>) {
        // 1. (𝜌, 𝜎) <- G(d || k)
        let mut g = sha3::Sha3_512Context::new();
        g.update(d);
        g.update(&[P::K as u8]);
        let g = g.finish();
        let (rho, sigma) = g.split_at(32);
        // rho seeds the public matrix, so it is public.
        let rho: [u8; 32] = low::ct::into_public(rho.try_into().unwrap());
        let sigma = KpkeRandomness(sigma.try_into().unwrap());

        // 3. - 7.
        let a_hat = Coeffs::<P::Matrix, Ntt>::sample(&rho, false);

        // 8. - 15.
        let mut s = Coeffs::<P::Vector, Normal>::zero();
        let mut e = Coeffs::<P::Vector, Normal>::zero();
        sample_poly_cbd(P::ETA1, &sigma.0, 0, s.polys_mut().chain(e.polys_mut()));

        // 16. ŝ <- NTT(s)
        let mut s_hat = s.ntt();

        // 17. ê <- NTT(e)
        let e_hat = e.ntt();

        // 18. t^ = A^ ∘ ŝ + ê
        let t_hat = a_hat.mul_add(&s_hat, &e_hat);

        // H(ek), for ML-KEM.KeyGen's step 3.
        let t_hat = Coeffs(low::ct::into_public(t_hat.0), PhantomData);
        let encap = EncapKey::new(t_hat, rho, a_hat.transpose(), None);

        s_hat.reduce_in_place();
        let decap = s_hat.to_bytes();

        (encap, decap)
    }

    /// This is Algorithm 15: K-PKE.Decrypt(dk_PKE, c)
    fn kpke_decrypt(&self, c: &Ciphertext<P>) -> Message {
        // 1. c_1 <- c[0 ∶ 32 * du * k]
        // 2. c_2 <- c[32 * du * k ∶ 32 * (du * k + dv)]
        let (c_1, c_2) = c.0.as_ref().split_at(32 * P::DU * P::K);

        // 3. u' <- Decompress_du(ByteDecode_du(c1))
        let mut u_prime = Coeffs::<P::Vector, Normal>::zero();
        let polys = u_prime.polys_mut();
        match P::DU {
            10 => polys
                .zip(c_1.as_chunks::<320>().0)
                .for_each(|(poly, bytes)| decompress::<10>(bytes, poly)),
            11 => polys
                .zip(c_1.as_chunks::<352>().0)
                .for_each(|(poly, bytes)| decompress::<11>(bytes, poly)),
            _ => unreachable!(),
        }

        // 4. v' <- Decompress_dv(ByteDecode_dv(c2))
        let mut v_prime = Coeffs::<Poly, Normal>::zero();
        match P::DV {
            4 => decompress::<4>(c_2, &mut v_prime.0),
            5 => decompress::<5>(c_2, &mut v_prime.0),
            _ => unreachable!(),
        }

        // 5. s^ <- ByteDecode_12(dk_PKE)
        let s_hat = Coeffs::<P::Vector, Ntt>::from_bytes(&self.dk_pke);

        // 6. w <- v' - NTT-1(transpose(s^) * NTT(u'))
        let u_hat = u_prime.ntt();
        let w = v_prime.sub(&s_hat.dot_and_inverse_ntt(&u_hat, &u_hat.mul_cache()));

        // 7. m <- ByteEncode_1(Compress_1(w))
        w.to_message_bits()
    }
}

// Wiped whole, so no byte of the key survives, padding included. The boxed
// matrix goes first, since the whole-value wipe nulls its pointer.
impl<P: Params> Drop for DecapKey<P> {
    fn drop(&mut self) {
        if let Some(mut transpose_a_hat) = self.ek_pke.transpose_a_hat.take() {
            low::zeroise(transpose_a_hat.0.as_mut().as_flattened_mut());
        }
        low::zeroise_value(self);
    }
}

impl<P: Params> low::Zeroable for DecapKey<P> {}

/// An ML-KEM encapsulation key.
pub(crate) struct EncapKey<P: Params> {
    /// `H(ek)`, which both encapsulation and decapsulation hash in.
    h_ek: [u8; 32],
    rho: [u8; 32],
    /// `t_hat` decoded, which the modulus check computes anyway. No encoded
    /// copy is kept: only `as_bytes` needs one, and it re-encodes.
    t_hat_coeffs: Coeffs<P::Vector, Ntt>,
    /// The transposed matrix, which encryption multiplies by. Boxed, as
    /// ML-KEM-1024's is 8 KiB, so moving a key copies little; `None` only
    /// once a [`DecapKey`] holding it is wiped.
    transpose_a_hat: Option<Box<Coeffs<P::Matrix, Ntt>>>,
}

impl<P: Params> Clone for EncapKey<P> {
    fn clone(&self) -> Self {
        Self {
            h_ek: self.h_ek,
            rho: self.rho,
            t_hat_coeffs: self.t_hat_coeffs.clone(),
            transpose_a_hat: self.transpose_a_hat.clone(),
        }
    }
}

impl<P: Params> EncapKey<P> {
    /// Assemble a key from its decoded parts, hashing `encoded`, its
    /// encoding, if the caller has it, or else re-encoding.
    fn new(
        t_hat_coeffs: Coeffs<P::Vector, Ntt>,
        rho: [u8; 32],
        transpose_a_hat: Coeffs<P::Matrix, Ntt>,
        encoded: Option<&P::EncapKeyBytes>,
    ) -> Self {
        let mut h = sha3::Sha3_256Context::new();
        match encoded {
            Some(encoded) => h.update(encoded.as_ref()),
            None => {
                h.update(t_hat_coeffs.to_bytes().as_ref().as_flattened());
                h.update(&rho);
            }
        }
        Self {
            h_ek: h.finish(),
            rho,
            t_hat_coeffs,
            transpose_a_hat: Some(Box::new(transpose_a_hat)),
        }
    }

    /// Create a new [`EncapKey`] from bytes.
    pub(crate) fn from_bytes(input: &P::EncapKeyBytes) -> Result<Self, Error> {
        let _entry = low::Entry::new_public();
        let (t_hat, rho) = input.as_ref().split_at(P::K * 384);

        // 2. (Modulus check) Perform the computation
        //
        //   test <- ByteEncode_12(ByteDecode_12(ek[0 ∶ 384k]))
        //
        // If test != ek[0 ∶ 384k], then input checking failed.
        let mut encoded = Encoded::<P>::filled([0; 384]);
        encoded.as_mut().as_flattened_mut().copy_from_slice(t_hat);
        let t_hat_coeffs = Coeffs::<P::Vector, Ntt>::from_bytes(&encoded);
        if t_hat != t_hat_coeffs.to_bytes().as_ref().as_flattened() {
            return Err(KeyFormatError::MlKemModulus.into());
        }

        let rho = rho.try_into().unwrap();
        let transpose_a_hat = Coeffs::sample(&rho, true);
        Ok(Self::new(t_hat_coeffs, rho, transpose_a_hat, Some(input)))
    }

    /// Encapsulate a random shared secret, returning the shared secret and a ciphertext.
    ///
    /// The ciphertext can be returned to the holder of the [`DecapKey`] who can then
    /// derive the same [`SharedSecret`].
    pub(crate) fn encaps(&self) -> Result<(SharedSecret, Ciphertext<P>), Error> {
        let _entry = low::Entry::new_secret();
        let mut m = Message([0; 32]);
        SystemRandom.fill(&mut m.0)?;
        Ok(self.encaps_internal(m))
    }

    /// Encode the [`EncapKey`] as bytes.
    pub(crate) fn as_bytes(&self) -> P::EncapKeyBytes {
        let _entry = low::Entry::new_public();
        let mut out = P::EncapKeyBytes::filled(0);
        let (t_hat, rho) = out.as_mut().split_at_mut(P::K * 384);
        t_hat.copy_from_slice(self.t_hat_coeffs.to_bytes().as_ref().as_flattened());
        rho.copy_from_slice(&self.rho);
        out
    }

    pub(crate) fn encaps_internal(&self, m: Message) -> (SharedSecret, Ciphertext<P>) {
        low::ct::secret_slice(&m.0);

        // 1. (K, r) <- G(m || H(ek))
        let mut g = sha3::Sha3_512Context::new();
        g.update(&m.0);
        g.update(&self.h_ek);
        let kr = g.finish();
        let (k, r) = kr.split_at(32);
        let k = SharedSecret(k.try_into().unwrap());
        let r = KpkeRandomness(r.try_into().unwrap());

        // 2. c <- K-PKE.Encrypt(ek, m, r)
        let c = self.kpke_encrypt(m, r);
        (k, Ciphertext(low::ct::into_public(c.0)))
    }

    fn kpke_encrypt(&self, m: Message, r: KpkeRandomness) -> Ciphertext<P> {
        // 2. t^ <- ByteDecode12(ekPKE[0 ∶ 384k])
        //  - already decoded, as self.t_hat_coeffs.
        // 3. 𝜌 <- ekPKE[384k ∶ 384k + 32]
        //  - only required for a_hat expansion
        // 4. - 8. rolled into self.transpose_a_hat.
        let transpose_a_hat = self.transpose_a_hat.as_deref().expect("wiped only on drop");

        // 9. - 12. y_i <- SamplePolyCBD_eta1(PRF(r, N))
        let mut y = Coeffs::<P::Vector, Normal>::zero();
        sample_poly_cbd(P::ETA1, &r.0, 0, y.polys_mut());

        // 13. - 16. e_1 <- SamplePolyCBD_eta2(PRF(r, N))
        // 17. e_2 <- SamplePolyCBD_eta2(PRF(r, N))
        let mut e_1 = Coeffs::<P::Vector, Normal>::zero();
        let mut e_2 = Coeffs::<Poly, Normal>::zero();
        sample_poly_cbd(
            ETA2,
            &r.0,
            P::K as u8,
            e_1.polys_mut().chain(core::iter::once(&mut e_2.0)),
        );

        // 18. y^ <- NTT(y)
        let y_hat = y.ntt();
        let y_cache = y_hat.mul_cache();

        // 19. u <- NTT^-1(transpose(A^) ∘ y^) + e_1
        let mut u = transpose_a_hat
            .mul_and_inverse_ntt(&y_hat, &y_cache)
            .add(&e_1);
        u.reduce_in_place();

        // 20. µ <- Decompress_1(ByteDecode_1(m))
        let mu = Coeffs::from_message_bits(m);

        // 21. v <- NTT^-1(transpose(t^) ∘ y^) + e_2 + µ
        //
        // The inverse NTT's output is below 8Q in magnitude, so the sums fit
        // an i16 and one reduction serves.
        let mut v = self
            .t_hat_coeffs
            .dot_and_inverse_ntt(&y_hat, &y_cache)
            .add(&e_2)
            .add(&mu);
        low::mlkem_reduce(&mut v.0);

        let mut c = P::CiphertextBytes::filled(0);
        let (c_1, c_2) = c.as_mut().split_at_mut(32 * P::DU * P::K);

        // 22. c_1 <- ByteEncode_du(Compress_du(u))
        let polys = u.0.as_ref().iter();
        match P::DU {
            10 => polys
                .zip(c_1.as_chunks_mut::<320>().0)
                .for_each(|(poly, out)| low::mlkem_compress_d10(out, poly)),
            11 => polys
                .zip(c_1.as_chunks_mut::<352>().0)
                .for_each(|(poly, out)| low::mlkem_compress_d11(out, poly)),
            _ => unreachable!(),
        }

        // 23. c_2 <- ByteEncode_dv(Compress_dv(v))
        match P::DV {
            4 => low::mlkem_compress_d4(c_2.try_into().unwrap(), &v.0),
            5 => low::mlkem_compress_d5(c_2.try_into().unwrap(), &v.0),
            _ => unreachable!(),
        }

        // 24. return c <- (c_1 || c_2)
        Ciphertext(c)
    }
}

/// The rank of a square matrix of `len` polynomials, found without the
/// division `isqrt` compiles to, which the variable-time scan refuses.
fn rank(len: usize) -> usize {
    match len {
        4 => 2,
        9 => 3,
        16 => 4,
        _ => unreachable!(),
    }
}

/// An ML-KEM ciphertext.
pub(crate) struct Ciphertext<P: Params>(P::CiphertextBytes);

impl<P: Params> Ciphertext<P> {
    /// The ciphertext `bytes`, if they are the parameter set's length.
    pub(crate) fn from_slice(bytes: &[u8]) -> Option<Self> {
        P::CiphertextBytes::from_slice(bytes).map(Self)
    }
}

impl<P: Params> Clone for Ciphertext<P> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<P: Params> fmt::Debug for Ciphertext<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Ciphertext").field(&self.0).finish()
    }
}

impl<P: Params> AsRef<[u8]> for Ciphertext<P> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

/// A K-PKE message.
pub(crate) struct Message(pub(crate) [u8; 32]);

/// K-PKE randomness input: `sigma` for key generation, `r` for encryption.
struct KpkeRandomness([u8; 32]);

/// An ML-KEM shared secret.
pub(crate) struct SharedSecret([u8; 32]);

impl AsRef<[u8; 32]> for SharedSecret {
    fn as_ref(&self) -> &[u8; 32] {
        &self.0
    }
}

impl fmt::Debug for SharedSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SharedSecret").finish_non_exhaustive()
    }
}

impl Drop for SharedSecret {
    fn drop(&mut self) {
        low::zeroise(&mut self.0);
    }
}

/// One polynomial's coefficients.
type Poly = [i16; N];

/// Tracks what the values in a `Coeffs` mean.
trait Domain {}

/// Coefficients in normal domain.
struct Normal;
impl Domain for Normal {}

/// Coefficients in NTT domain.
struct Ntt;
impl Domain for Ntt {}

/// Multiplication cache values.
struct MulCache;
impl Domain for MulCache {}

/// Polynomial coefficients: one polynomial, or an array of them, aligned for
/// the AVX2 routines' aligned loads.
///
/// Arithmetic on coefficients, here and in the compression and sampling
/// helpers, wraps: their bounds rule out overflow, and a debug build's
/// overflow check would branch on secret values.
#[repr(align(32))]
struct Coeffs<V, D: Domain>(V, PhantomData<D>);

impl<V: Clone, D: Domain> Clone for Coeffs<V, D> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<V: Array<Poly>, D: Domain> Coeffs<V, D> {
    fn zero() -> Self {
        Self(V::filled([0; N]), PhantomData)
    }

    /// Each polynomial's coefficients.
    fn polys_mut(&mut self) -> impl Iterator<Item = &mut Poly> {
        self.0.as_mut().iter_mut()
    }

    /// Reduce coefficients into [0, Q)
    fn reduce_in_place(&mut self) {
        for k in self.polys_mut() {
            low::mlkem_reduce(k);
        }
    }
}

impl<D: Domain> Coeffs<Poly, D> {
    fn zero() -> Self {
        Self([0; N], PhantomData)
    }
}

impl<M: Array<Poly>> Coeffs<M, Ntt> {
    /// FIPS-203's `SampleNTT` of the matrix `A^` from `rho`, or of its
    /// transpose.
    fn sample(rho: &[u8; 32], transposed: bool) -> Self {
        let mut r = Self(M::filled([0; N]), PhantomData);
        sample_ntt::sample_ntt(rho, transposed, r.0.as_mut());
        for poly in r.polys_mut() {
            low::mlkem_unpack(poly);
        }
        r
    }

    fn rows(&self) -> impl Iterator<Item = &[Poly]> {
        let polys = self.0.as_ref();
        let k = rank(polys.len());
        polys.chunks_exact(k)
    }

    // a * s + e
    fn mul_add<V: Vector>(&self, s: &Coeffs<V, Ntt>, e: &Coeffs<V, Ntt>) -> Coeffs<V, Ntt> {
        let mut r = e.clone();

        let s_precomp = s.mul_cache();

        let mut term = Coeffs::<Poly, Ntt>::zero();

        for (aa, rr) in self.rows().zip(r.polys_mut()) {
            basemul(&mut term.0, aa, s.0.as_ref(), s_precomp.0.as_ref());
            low::mlkem_tomont(&mut term.0);

            for (r, t) in rr.iter_mut().zip(term.0.iter()) {
                *r = r.wrapping_add(*t);
            }
        }

        r.reduce_in_place();
        r
    }

    fn transpose(mut self) -> Self {
        let polys = self.0.as_mut();
        let k = rank(polys.len());

        for i in 0..k {
            for j in 0..i {
                polys.swap(i * k + j, j * k + i);
            }
        }

        self
    }

    /// This is `NTT-1(self * y)`, given `y`'s mulcache `y_cache`.
    ///
    /// The inverse NTT takes any `i16`, so the products go in unreduced.
    fn mul_and_inverse_ntt<V: Vector>(
        &self,
        y: &Coeffs<V, Ntt>,
        y_cache: &Coeffs<V::MulCache, MulCache>,
    ) -> Coeffs<V, Normal> {
        let mut r = Coeffs::<V, Ntt>::zero();

        for (aa, rr) in self.rows().zip(r.polys_mut()) {
            basemul(rr, aa, y.0.as_ref(), y_cache.0.as_ref());
        }

        r.inverse_ntt()
    }
}

impl<V: Vector> Coeffs<V, Ntt> {
    /// This is `ByteDecode_12(bytes)`.
    fn from_bytes(bytes: &V::Encoded) -> Self {
        let mut r = Self::zero();

        for (rr, bb) in r.polys_mut().zip(bytes.as_ref()) {
            low::mlkem_frombytes(rr, bb);
            low::mlkem_reduce(rr);
        }

        r
    }

    /// This is `ByteEncode_12(self)`
    fn to_bytes(&self) -> V::Encoded {
        let mut r = V::Encoded::filled([0; 384]);

        for (rr, cc) in r.as_mut().iter_mut().zip(self.0.as_ref()) {
            low::mlkem_tobytes(rr, cc);
        }

        r
    }

    /// This is `NTT-1(self * s)`, given `s`'s mulcache `s_cache`.
    fn dot_and_inverse_ntt(
        &self,
        s: &Self,
        s_cache: &Coeffs<V::MulCache, MulCache>,
    ) -> Coeffs<Poly, Normal> {
        let mut r = Coeffs::<Poly, Ntt>::zero();

        basemul(&mut r.0, self.0.as_ref(), s.0.as_ref(), s_cache.0.as_ref());
        // nb. no need for a tomont here, as `inverse_ntt` incorporates that

        r.inverse_ntt()
    }

    fn mul_cache(&self) -> Coeffs<V::MulCache, MulCache> {
        let mut r = Coeffs(V::MulCache::filled([0; N / 2]), PhantomData);

        for (rr, m) in r.0.as_mut().iter_mut().zip(self.0.as_ref()) {
            low::mlkem_mulcache_compute(rr, m);
        }

        r
    }

    fn inverse_ntt(mut self) -> Coeffs<V, Normal> {
        for ch in self.polys_mut() {
            low::mlkem_intt(ch);
        }
        Coeffs(self.0, PhantomData)
    }
}

impl Coeffs<Poly, Ntt> {
    fn inverse_ntt(mut self) -> Coeffs<Poly, Normal> {
        low::mlkem_intt(&mut self.0);
        Coeffs(self.0, PhantomData)
    }
}

/// The scalar product of the vectors `a` and `b`, given `b`'s mulcache `bt`,
/// in the NTT domain.
fn basemul(r: &mut Poly, a: &[Poly], b: &[Poly], bt: &[[i16; N / 2]]) {
    let (a, b, bt) = (a.as_flattened(), b.as_flattened(), bt.as_flattened());
    match bt.len() / (N / 2) {
        2 => low::mlkem_basemul_k2(
            r,
            a.try_into().unwrap(),
            b.try_into().unwrap(),
            bt.try_into().unwrap(),
        ),
        3 => low::mlkem_basemul_k3(
            r,
            a.try_into().unwrap(),
            b.try_into().unwrap(),
            bt.try_into().unwrap(),
        ),
        4 => low::mlkem_basemul_k4(
            r,
            a.try_into().unwrap(),
            b.try_into().unwrap(),
            bt.try_into().unwrap(),
        ),
        _ => unreachable!(),
    }
}

/// `Decompress_D(ByteDecode_D(bytes))` into `out`: each `D` bytes yield
/// eight `D`-bit values, little-endian bit order, and each value `y` becomes
/// `round((q / 2^D) * y)`.
fn decompress<const D: usize>(bytes: &[u8], out: &mut Poly) {
    let (in_chunks, _) = bytes.as_chunks::<D>();
    let (octets, _) = out.as_chunks_mut::<8>();
    debug_assert_eq!(in_chunks.len(), octets.len());

    for (inp, octet) in in_chunks.iter().zip(octets.iter_mut()) {
        let mut bits = [0u8; 16];
        bits[..D].copy_from_slice(inp);
        let bits = u128::from_le_bytes(bits);
        for (i, coeff) in octet.iter_mut().enumerate() {
            let y = ((bits >> (D * i)) as u32) & ((1 << D) - 1);
            *coeff = ((y * Q as u32 + (1 << (D - 1))) >> D) as i16;
        }
    }
}

/// `Compress_1(x)` for eight coefficients in `[0, Q)`
fn compress_1_x8(coeffs: &[i16; 8]) -> u8 {
    let mut r = 0;

    for (i, x) in coeffs.iter().enumerate() {
        debug_assert!((0..Q).contains(&low::ct::into_public(*x)));
        let x = (*x as u64) << 1;
        let x = x.wrapping_add(Q_HALF as u64);
        let x = x.wrapping_mul(80635);
        let x = x >> 28;
        r |= ((x & 1) as u8) << i;
    }

    r
}

impl<V: Array<Poly>> Coeffs<V, Normal> {
    /// K-wise NTT
    fn ntt(mut self) -> Coeffs<V, Ntt> {
        for ch in self.polys_mut() {
            low::mlkem_ntt(ch);
        }
        Coeffs(self.0, PhantomData)
    }
}

impl Coeffs<Poly, Normal> {
    /// This is `Decompress_1(ByteDecode_1(m))`
    ///
    /// `ByteDecode_1` is just `BytesToBits`.
    /// `Decompress_1` maps set bits to Q/2.
    fn from_message_bits(m: Message) -> Self {
        let mut r = Self::zero();

        for (i, byte) in m.0.iter().enumerate() {
            for bit in 0..8 {
                r.0[i * 8 + bit] = ct_select_i16(byte >> bit & 1, Q_HALF, 0);
            }
        }

        r
    }

    /// This is `ByteEncode_1(Compress_1(m))`
    fn to_message_bits(&self) -> Message {
        let mut r = Message([0; 32]);

        for (i, r) in r.0.iter_mut().enumerate() {
            *r = compress_1_x8(&self.0[i * 8..(i + 1) * 8].try_into().unwrap());
        }

        r
    }
}

impl Coeffs<Poly, Normal> {
    /// Simple addition, leaving the sum unreduced
    fn add(mut self, term: &Self) -> Self {
        for (ss, tt) in self.0.iter_mut().zip(term.0.iter()) {
            *ss = ss.wrapping_add(*tt);
        }
        self
    }

    /// Simple subtraction
    fn sub(mut self, term: &Self) -> Self {
        for (ss, tt) in self.0.iter_mut().zip(term.0.iter()) {
            *ss = ss.wrapping_sub(*tt);
        }
        low::mlkem_reduce(&mut self.0);
        self
    }
}

impl<V: Array<Poly>> Coeffs<V, Normal> {
    /// Simple addition, leaving the sum unreduced
    fn add(mut self, term: &Self) -> Self {
        for (ss, tt) in self.0.as_mut().iter_mut().zip(term.0.as_ref()) {
            for (s, t) in ss.iter_mut().zip(tt) {
                *s = s.wrapping_add(*t);
            }
        }
        self
    }
}

/// `SamplePolyCBD_eta(PRF_eta(sigma, n))` into each of `polys`, with `n`
/// counting from `first`.
fn sample_poly_cbd<'a>(
    eta: usize,
    sigma: &[u8; 32],
    first: u8,
    polys: impl Iterator<Item = &'a mut Poly>,
) {
    match eta {
        2 => sample_poly_cbd2(sigma, first, polys),
        3 => sample_poly_cbd3(sigma, first, polys),
        _ => unreachable!(),
    }
}

/// [`sample_poly_cbd`] for `eta = 2`, four polynomials at a time.
fn sample_poly_cbd2<'a>(
    sigma: &[u8; 32],
    mut n: u8,
    mut polys: impl Iterator<Item = &'a mut Poly>,
) {
    loop {
        let batch: [Option<&mut Poly>; 4] = core::array::from_fn(|_| polys.next());
        let count = batch.iter().take_while(|p| p.is_some()).count();
        if count == 0 {
            return;
        }

        let mut bufs = [[0; 40]; 4];
        for buf in &mut bufs[..count] {
            buf[..32].copy_from_slice(sigma);
            buf[32] = n;
            buf[33] = sha3::SHAKE_PAD_BYTE;
            n += 1;
        }

        let mut samples = [[0; 128]; 4];
        match count {
            1 => shake256_batch_of::<1>(&bufs, &mut samples),
            2 => shake256_batch_of::<2>(&bufs, &mut samples),
            3 => shake256_batch_of::<3>(&bufs, &mut samples),
            _ => sha3::shake256_batch(&bufs, &mut samples),
        }

        for (sample, poly) in samples.iter().zip(batch.into_iter().flatten()) {
            sample_cbd2(sample, poly);
        }
    }
}

/// [`sha3::shake256_batch`] of the first `P` of four inputs.
fn shake256_batch_of<const P: usize>(inputs: &[[u8; 40]; 4], outputs: &mut [[u8; 128]; 4]) {
    sha3::shake256_batch::<P>(
        inputs.first_chunk().unwrap(),
        outputs.first_chunk_mut().unwrap(),
    );
}

/// [`sample_poly_cbd`] for `eta = 3`, four polynomials at a time.
fn sample_poly_cbd3<'a>(
    sigma: &[u8; 32],
    mut n: u8,
    mut polys: impl Iterator<Item = &'a mut Poly>,
) {
    loop {
        let batch: [Option<&mut Poly>; 4] = core::array::from_fn(|_| polys.next());
        let count = batch.iter().take_while(|p| p.is_some()).count();
        if count == 0 {
            return;
        }

        let mut inputs = [[0; 33]; 4];
        for input in &mut inputs[..count] {
            input[..32].copy_from_slice(sigma);
            input[32] = n;
            n += 1;
        }

        // The 192 bytes each polynomial takes span two blocks.
        let mut samples = [[0; 2 * sha3::SHAKE_256_R_BYTES]; 4];
        sha3::Shake256x4::new(&inputs[..count]).squeeze(&mut samples);

        for (sample, poly) in samples.iter().zip(batch.into_iter().flatten()) {
            sample_cbd3(sample.first_chunk().unwrap(), poly);
        }
    }
}

fn sample_cbd2(buf: &[u8; 128], out: &mut Poly) {
    let (buf_chunks, _) = buf.as_chunks::<4>();
    let (out_chunks, _) = out.as_chunks_mut::<8>();
    for (in_bytes, out_coeffs) in buf_chunks.iter().zip(out_chunks.iter_mut()) {
        let t = u32::from_le_bytes(*in_bytes);
        let d = (t & 0x5555_5555).wrapping_add((t >> 1) & 0x5555_5555);

        for (j, coeff) in out_coeffs.iter_mut().enumerate() {
            let a = ((d >> (4 * j)) & 0x3) as i16;
            let b = ((d >> (4 * j + 2)) & 0x3) as i16;
            *coeff = a.wrapping_sub(b);
        }
    }
}

fn sample_cbd3(buf: &[u8; 192], out: &mut Poly) {
    let (buf_chunks, _) = buf.as_chunks::<3>();
    let (out_chunks, _) = out.as_chunks_mut::<4>();
    for (in_bytes, out_coeffs) in buf_chunks.iter().zip(out_chunks.iter_mut()) {
        let t = u32::from_le_bytes([in_bytes[0], in_bytes[1], in_bytes[2], 0]);
        let d = (t & 0x0024_9249)
            .wrapping_add((t >> 1) & 0x0024_9249)
            .wrapping_add((t >> 2) & 0x0024_9249);

        for (j, coeff) in out_coeffs.iter_mut().enumerate() {
            let a = ((d >> (6 * j)) & 0x7) as i16;
            let b = ((d >> (6 * j + 3)) & 0x7) as i16;
            *coeff = a.wrapping_sub(b);
        }
    }
}

/// Every parameter set's noise for `e_1` and `e_2`.
const ETA2: usize = 2;

const Q: i16 = 3329;
const Q_HALF: i16 = (Q + 1) / 2;
const N: usize = 256;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test::{Acvp, acvp};

    fn acvp_seed(test: &serde_json::Value) -> [u8; 64] {
        [test.hex("d"), test.hex("z")].concat().try_into().unwrap()
    }

    #[test]
    fn acvp_key_gen() {
        fn check<P: Params>(group: &serde_json::Value) {
            for test in group.tests() {
                let dk = DecapKey::<P>::keygen_internal(&acvp_seed(test));
                assert_eq!(
                    dk.encapsulation_key().as_bytes().as_ref(),
                    &test.hex("ek")[..]
                );
                assert_eq!(
                    low::ct::into_public(dk.as_bytes()).as_ref(),
                    &test.hex("dk")[..]
                );
            }
        }

        let mut sets = Vec::new();
        for group in acvp("ML-KEM-keyGen-FIPS203") {
            let set = group.str("parameterSet");
            match set {
                "ML-KEM-512" => check::<MlKem512>(&group),
                "ML-KEM-768" => check::<MlKem768>(&group),
                "ML-KEM-1024" => check::<MlKem1024>(&group),
                other => panic!("unexpected parameter set {other}"),
            }
            sets.push(set.to_string());
        }
        sets.sort();
        sets.dedup();
        assert_eq!(sets, ["ML-KEM-1024", "ML-KEM-512", "ML-KEM-768"]);
    }

    #[test]
    fn acvp_encap_decap() {
        fn check<P: Params>(group: &serde_json::Value) {
            for test in group.tests() {
                let ek = || {
                    EncapKey::<P>::from_bytes(
                        &P::EncapKeyBytes::from_slice(&test.hex("ek")).unwrap(),
                    )
                };
                let dk = || {
                    DecapKey::<P>::from_bytes(
                        &P::DecapKeyBytes::from_slice(&test.hex("dk")).unwrap(),
                    )
                };
                let ciphertext = || Ciphertext::<P>::from_slice(&test.hex("c")).unwrap();
                match (group.str("function"), group.str("keyFormat")) {
                    ("encapsulation", "none") => {
                        let m = Message(test.hex("m").try_into().unwrap());
                        let (k, c) = ek().unwrap().encaps_internal(m);
                        assert_eq!(low::ct::into_public(*k.as_ref()), &test.hex("k")[..]);
                        assert_eq!(c.as_ref(), &test.hex("c")[..]);
                    }
                    ("decapsulation", "seed") => {
                        let dk = DecapKey::<P>::keygen_internal(&acvp_seed(test));
                        assert_eq!(
                            low::ct::into_public(dk.as_bytes()).as_ref(),
                            &test.hex("dk")[..]
                        );
                        assert_eq!(
                            low::ct::into_public(*dk.decaps(&ciphertext()).as_ref()),
                            &test.hex("k")[..]
                        );
                    }
                    ("decapsulation", "expanded") => {
                        let k = dk().unwrap().decaps(&ciphertext());
                        assert_eq!(low::ct::into_public(*k.as_ref()), &test.hex("k")[..]);
                    }
                    ("decapsulationKeyCheck", "expanded") => {
                        assert_eq!(
                            dk().is_some(),
                            test.flag("testPassed"),
                            "{}",
                            test.str("reason")
                        );
                    }
                    ("encapsulationKeyCheck", "none") => {
                        assert_eq!(
                            ek().is_ok(),
                            test.flag("testPassed"),
                            "{}",
                            test.str("reason")
                        );
                    }
                    other => panic!("unexpected function {other:?}"),
                }
            }
        }

        let mut sets = Vec::new();
        for group in acvp("ML-KEM-encapDecap-FIPS203-tr1") {
            let set = group.str("parameterSet");
            match set {
                "ML-KEM-512" => check::<MlKem512>(&group),
                "ML-KEM-768" => check::<MlKem768>(&group),
                "ML-KEM-1024" => check::<MlKem1024>(&group),
                other => panic!("unexpected parameter set {other}"),
            }
            sets.push(set.to_string());
        }
        sets.sort();
        sets.dedup();
        assert_eq!(sets, ["ML-KEM-1024", "ML-KEM-512", "ML-KEM-768"]);
    }

    #[test]
    fn shared_secret_debug() {
        assert_eq!(format!("{:?}", SharedSecret([0u8; 32])), "SharedSecret(..)");
    }

    #[test]
    fn pairwise() {
        fn check<P: Params>() {
            let d = DecapKey::<P>::generate().unwrap();
            let (ess, ct) = d.encapsulation_key().encaps().unwrap();
            let dss = d.decaps(&ct);
            assert_eq!(low::ct::into_public(ess.0), low::ct::into_public(dss.0));
        }
        check::<MlKem512>();
        check::<MlKem768>();
        check::<MlKem1024>();
    }

    #[test]
    fn encaps_modulus_test() {
        fn check<P: Params>() {
            assert_eq!(
                EncapKey::<P>::from_bytes(&P::EncapKeyBytes::filled(0xff)).err(),
                Some(KeyFormatError::MlKemModulus.into())
            );
        }
        check::<MlKem512>();
        check::<MlKem768>();
        check::<MlKem1024>();
    }

    // Each width's decompression undoes compression to within FIPS-203's
    // bound, `round(q / 2^(D + 1))`, and recompresses to the same bits.
    #[test]
    fn decompress_inverts_compress() {
        fn check<const D: usize>(compress: fn(&mut [u8], &Poly)) {
            for start in (0..Q as usize + 7).step_by(N - 7) {
                let poly = Coeffs::<Poly, Normal>(
                    core::array::from_fn(|i| ((start + i) % Q as usize) as i16),
                    PhantomData,
                );
                let mut bytes = [0; 32 * 11];
                compress(&mut bytes[..32 * D], &poly.0);
                let mut out = [0; N];
                decompress::<D>(&bytes[..32 * D], &mut out);
                let mut again = [0; 32 * 11];
                compress(&mut again[..32 * D], &out);
                assert_eq!(bytes, again, "d{D}, from {start}");
                for (x, y) in poly.0.iter().zip(out.iter()) {
                    let diff = (x - y).rem_euclid(Q);
                    let diff = diff.min(Q - diff);
                    assert!(
                        diff <= (Q as i32 + (1 << D)) as i16 / (2 << D),
                        "d{D}, {x} {y}"
                    );
                }
            }
        }
        // `compress` wants an aligned input, which a copy into `Coeffs` gives.
        fn aligned(poly: &Poly) -> Coeffs<Poly, Normal> {
            Coeffs(*poly, PhantomData)
        }
        check::<4>(|r, a| low::mlkem_compress_d4(r.try_into().unwrap(), &aligned(a).0));
        check::<5>(|r, a| low::mlkem_compress_d5(r.try_into().unwrap(), &aligned(a).0));
        check::<10>(|r, a| low::mlkem_compress_d10(r.try_into().unwrap(), &aligned(a).0));
        check::<11>(|r, a| low::mlkem_compress_d11(r.try_into().unwrap(), &aligned(a).0));
    }

    // The two-block noise of ML-KEM-512's `eta1 = 3` matches the bitwise
    // definition of `SamplePolyCBD`.
    #[test]
    fn cbd3_matches_definition() {
        let buf: [u8; 192] = core::array::from_fn(|i| (i as u8).wrapping_mul(167) ^ 0x5a);
        let mut got = [0; N];
        sample_cbd3(&buf, &mut got);
        let bit = |i: usize| ((buf[i / 8] >> (i % 8)) & 1) as i16;
        for (i, coeff) in got.iter().enumerate() {
            let x: i16 = (0..3).map(|j| bit(6 * i + j)).sum();
            let y: i16 = (0..3).map(|j| bit(6 * i + 3 + j)).sum();
            assert_eq!(*coeff, x - y, "{i}");
        }
    }

    // Valgrind hides SHA3, so `admin/ctgrind` never reaches the Keccak
    // kernels aarch64 runs with it; `admin/ct-qemu` traces them here instead,
    // under qemu-aarch64's `max` CPU. Encapsulating a secret message takes
    // the one-, two-, and four-way kernels, and decapsulation runs them on
    // the secret key, for a ciphertext it accepts and one it rejects. The key
    // is fixed between runs, so the public matrix is too. A second key then
    // shares that public key but takes its implicit-rejection secret `z` from
    // the seed, and decapsulates fixed ciphertexts, so only `z` varies. Every
    // parameter set runs, for ML-KEM-512's two-block noise.
    #[cfg(rind_backend = "aarch64")]
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_mlkem() {
        use crate::low::ct_qemu;

        fn check<P: Params>(seed: &[u8]) {
            let dk = DecapKey::<P>::keygen_internal(&[0x5a; 64]);
            let m = Message(core::array::from_fn(|i| seed[i % seed.len()]));
            let (_, c) = ct_qemu::traced(|| dk.ek_pke.encaps_internal(m));
            ct_qemu::traced(|| dk.decaps(&c));
            let mut c = c.0;
            c.as_mut()[0] ^= 1;
            ct_qemu::traced(|| dk.decaps(&Ciphertext(c.clone())));

            let dk = DecapKey::<P>::keygen_internal(&core::array::from_fn(|i| match i {
                ..32 => 0x5a,
                _ => seed[i % seed.len()],
            }));
            let (_, c) = dk.ek_pke.encaps_internal(Message([0xa5; 32]));
            ct_qemu::traced(|| dk.decaps(&c));
            let mut c = c.0;
            c.as_mut()[0] ^= 1;
            ct_qemu::traced(|| dk.decaps(&Ciphertext(c.clone())));
        }

        assert!(std::arch::is_aarch64_feature_detected!("sha3"), "SHA3");
        let seed = ct_qemu::seed().to_le_bytes();
        check::<MlKem512>(&seed);
        check::<MlKem768>(&seed);
        check::<MlKem1024>(&seed);
    }
}
