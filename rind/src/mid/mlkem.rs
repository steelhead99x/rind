// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-KEM as standardised by FIPS-203, at each of its parameter sets.

use alloc::boxed::Box;
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
pub trait Params:
    fmt::Debug + Sized + Send + Sync + Unpin + UnwindSafe + RefUnwindSafe + 'static
{
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
    #[doc(hidden)]
    type DecapKeyBytes: Array<u8>;
    /// FIPS-203's name for the set.
    #[cfg(test)]
    const NAME: &'static str;

    // The algorithms at this parameter set. As methods of each set's impl,
    // they compile in rind, not in each generic caller, so `admin/ct-vartime`
    // sees them, and the MXCSR mitigation they hold, from what rind exports.
    // Each takes an `Internal`, which only rind can make.
    #[doc(hidden)]
    fn keygen(_: Internal, seed: &[u8; 64]) -> DecapKey<Self>;
    #[doc(hidden)]
    fn decaps(_: Internal, key: &DecapKey<Self>, c: &Ciphertext<Self>) -> SharedSecret;
    #[doc(hidden)]
    fn parse(_: Internal, input: &Self::EncapKeyBytes) -> Result<EncapKey<Self>, Error>;
    #[doc(hidden)]
    fn encaps(_: Internal, key: &EncapKey<Self>, m: Message) -> (SharedSecret, Ciphertext<Self>);
}

/// Proof that a call to a [`Params`] method comes from rind: no other crate
/// can make one, though a generic caller can name the methods.
#[doc(hidden)]
#[derive(Clone, Copy)]
pub struct Internal(());

// Each set's `Params` methods, each holding Intel's MXCSR mitigation over the
// arithmetic it runs.
macro_rules! algorithms {
    () => {
        #[inline(never)]
        fn keygen(_: Internal, seed: &[u8; 64]) -> DecapKey<Self> {
            let _mcdt = low::Mcdt::enter();
            DecapKey::keygen_mitigated(seed)
        }

        #[inline(never)]
        fn decaps(_: Internal, key: &DecapKey<Self>, c: &Ciphertext<Self>) -> SharedSecret {
            let _mcdt = low::Mcdt::enter();
            key.decaps_mitigated(c)
        }

        #[inline(never)]
        fn parse(_: Internal, input: &Self::EncapKeyBytes) -> Result<EncapKey<Self>, Error> {
            let _mcdt = low::Mcdt::enter();
            EncapKey::parse_mitigated(input)
        }

        #[inline(never)]
        fn encaps(
            _: Internal,
            key: &EncapKey<Self>,
            m: Message,
        ) -> (SharedSecret, Ciphertext<Self>) {
            let _mcdt = low::Mcdt::enter();
            key.encaps_mitigated(m)
        }
    };
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
    type DecapKeyBytes = [u8; 1632];
    #[cfg(test)]
    const NAME: &'static str = "ML-KEM-512";
    algorithms!();
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
    type DecapKeyBytes = [u8; 2400];
    #[cfg(test)]
    const NAME: &'static str = "ML-KEM-768";
    algorithms!();
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
    type DecapKeyBytes = [u8; 3168];
    #[cfg(test)]
    const NAME: &'static str = "ML-KEM-1024";
    algorithms!();
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

/// pyca/verified-garbage's encapsulation, for ML-KEM-768 where it runs.
///
/// It measured faster than rind's at every tier it runs on, parsing the key
/// included: see `low::mlkem768_vg`.
fn vg_encaps<P: Params>() -> Option<low::mlkem768_vg::Encaps> {
    match P::K {
        3 => low::mlkem768_vg::Encaps::check(),
        _ => None,
    }
}

/// pyca/verified-garbage's key generation and decapsulation, for ML-KEM-768
/// where they run.
fn vg_key_pair<P: Params>() -> Option<low::mlkem768_vg::KeyPair> {
    match P::K {
        3 => low::mlkem768_vg::KeyPair::check(),
        _ => None,
    }
}

/// `bytes` as the array of ML-KEM-768's size that VG's routines take, which
/// it is whenever [`vg_encaps`] or [`vg_key_pair`] gave a routine.
fn vg_array<const L: usize>(bytes: &[u8]) -> &[u8; L] {
    bytes
        .try_into()
        .expect("only ML-KEM-768 runs VG's routines")
}

/// A VG routine's result, or `None`, as when the routine reached its
/// `SampleNTT` bound, in a test that forces rind's fallback.
fn vg_ran<T>(result: Option<T>) -> Option<T> {
    #[cfg(test)]
    if tests::FORCE_FALLBACK.get() {
        return None;
    }
    result
}

/// An ML-KEM decapsulation key: the fields of FIPS 203's encoding,
/// `dkPKE || ek || H(ek) || z`.
///
/// One from rind's key generation decapsulates with rind's arithmetic, and
/// its encapsulation key holds its decoded form. One from VG's, where it
/// runs, decapsulates with VG's routine, and its encapsulation key holds
/// none.
#[doc(hidden)]
pub struct DecapKey<P: Params> {
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
        P::decaps(Internal(()), self, c)
    }

    /// Return the corresponding [`EncapKey`]: without its decoded form where
    /// VG encapsulates, which needs none.
    pub(crate) fn encapsulation_key(&self) -> EncapKey<P> {
        let _entry = low::Entry::new_public();
        match vg_encaps::<P>() {
            Some(_) => EncapKey {
                bytes: self.ek_pke.bytes.clone(),
                h_ek: self.ek_pke.h_ek,
                hashed: self.ek_pke.hashed,
                decoded: None,
            },
            None => self.ek_pke.clone(),
        }
    }

    /// FIPS 203's encoding of the key, `dkPKE || ek || H(ek) || z`, as VG's
    /// decapsulation takes it.
    fn encode(&self) -> P::DecapKeyBytes {
        let mut out = P::DecapKeyBytes::filled(0);
        let (dk_pke, rest) = out.as_mut().split_at_mut(P::K * 384);
        let (ek, rest) = rest.split_at_mut(P::K * 384 + 32);
        let (h_ek, z) = rest.split_at_mut(32);
        dk_pke.copy_from_slice(self.dk_pke.as_ref().as_flattened());
        ek.copy_from_slice(self.ek_pke.bytes.as_ref());
        h_ek.copy_from_slice(&self.ek_pke.h_ek);
        z.copy_from_slice(&self.z);
        out
    }

    /// The fields of FIPS 203's encoding `dk`, with the encapsulation key's
    /// decoded form if `decode`, trusting the `H(ek)` it holds.
    fn decode(dk: &P::DecapKeyBytes, decode: bool) -> Self {
        let (dk_pke, rest) = dk.as_ref().split_at(P::K * 384);
        let (ek, rest) = rest.split_at(P::K * 384 + 32);
        let (h_ek, z) = rest.split_at(32);
        let mut encoded = Encoded::<P>::filled([0; 384]);
        encoded.as_mut().as_flattened_mut().copy_from_slice(dk_pke);
        let bytes = P::EncapKeyBytes::from_slice(ek).unwrap();
        Self {
            ek_pke: EncapKey {
                decoded: decode.then(|| Box::new(Decoded::new(&bytes))),
                bytes,
                h_ek: h_ek.try_into().unwrap(),
                hashed: true,
            },
            dk_pke: encoded,
            z: z.try_into().unwrap(),
        }
    }

    /// Encode the key as bytes.
    ///
    /// This is used for testing, and by the FIPS module's self-test.
    #[cfg(any(test, rind_fips))]
    pub(crate) fn as_bytes(&self) -> P::DecapKeyBytes {
        let _entry = low::Entry::new_secret();
        self.encode()
    }

    /// Decode a key encoded as [`Self::as_bytes()`] encodes it, or `None` if
    /// its `H(ek)` is not that of its encapsulation key. Like FIPS 203's
    /// decapsulation input check (section 7.3), it checks nothing else: an
    /// embedded encapsulation key that fails its modulus check decodes
    /// reduced mod q. It decapsulates with rind's arithmetic, since VG's
    /// takes only a key VG generated.
    ///
    /// This is used for testing, and by the FIPS module's ACVP build: rind
    /// generates keys only from seeds.
    #[cfg(any(test, rind_fips))]
    pub(crate) fn from_bytes(dk: &P::DecapKeyBytes) -> Option<Self> {
        let _entry = low::Entry::new_public();
        // Its arithmetic runs multiplies Intel's MXCSR mitigation covers.
        let _mcdt = low::Mcdt::enter();
        let key = Self::decode(dk, true);
        let mut h = sha3::Sha3_256Context::new();
        h.update(key.ek_pke.bytes.as_ref());
        (h.finish() == key.ek_pke.h_ek).then_some(key)
    }

    pub(crate) fn keygen_internal(seed: &[u8; 64]) -> Self {
        P::keygen(Internal(()), seed)
    }

    /// [`Self::keygen_internal`], under the caller's MXCSR mitigation.
    fn keygen_mitigated(seed: &[u8; 64]) -> Self {
        if let Some(vg) = vg_key_pair::<P>() {
            low::ct::secret_slice(seed);
            // `None` with probability below 2^-261: rind's arithmetic then
            // computes the same key.
            if let Some(dk) = vg_ran(vg.keygen(seed)) {
                // The encapsulation key and its hash are public.
                low::ct::public_slice(&dk[P::K * 384..P::K * 768 + 64]);
                return Self::decode(&P::DecapKeyBytes::from_slice(&dk).unwrap(), false);
            }
        }

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

    /// [`Self::decaps`], under the caller's MXCSR mitigation.
    fn decaps_mitigated(&self, c: &Ciphertext<P>) -> SharedSecret {
        if self.ek_pke.decoded.is_some() {
            return self.decaps_rind(c);
        }
        // A key VG generated, which VG's routine decapsulates where it runs.
        let dk = self.encode();
        if let Some(vg) = vg_key_pair::<P>() {
            // Never `None`: VG's key generation sampled the same matrix
            // without reaching its bound. rind's arithmetic would compute the
            // same secret.
            if let Some(k) = vg_ran(vg.decaps(vg_array(dk.as_ref()), vg_array(c.0.as_ref()))) {
                return SharedSecret(k);
            }
        }
        Self::decode(&dk, true).decaps_rind(c)
    }

    /// FIPS 203's `ML-KEM.Decaps_internal`, on rind's arithmetic: the
    /// encapsulation key holds its decoded form.
    fn decaps_rind(&self, c: &Ciphertext<P>) -> SharedSecret {
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
        let c_prime = self
            .ek_pke
            .decoded
            .as_deref()
            .expect("rind decapsulates only a decoded key")
            .kpke_encrypt(m_prime, r_prime);

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
        sample_poly_cbd(
            P::ETA1,
            P::K,
            &sigma.0,
            0,
            s.polys_mut().chain(e.polys_mut()),
        );

        // 16. ŝ <- NTT(s)
        let mut s_hat = s.ntt();

        // 17. ê <- NTT(e)
        let e_hat = e.ntt();

        // 18. t^ = A^ ∘ ŝ + ê
        let t_hat = a_hat.mul_add(&s_hat, &e_hat);

        // 19. ekPKE <- ByteEncode_12(t^) || 𝜌, which is public.
        let t_hat = Coeffs(low::ct::into_public(t_hat.0), PhantomData);
        let mut bytes = P::EncapKeyBytes::filled(0);
        let (t_hat_bytes, rho_bytes) = bytes.as_mut().split_at_mut(P::K * 384);
        t_hat_bytes.copy_from_slice(t_hat.to_bytes().as_ref().as_flattened());
        rho_bytes.copy_from_slice(&rho);
        let encap = EncapKey::new(
            bytes,
            Decoded {
                t_hat_coeffs: t_hat,
                transpose_a_hat: a_hat.transpose(),
            },
        );

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
                .for_each(|(poly, bytes)| decompress::<10, 320>(bytes, poly)),
            11 => polys
                .zip(c_1.as_chunks::<352>().0)
                .for_each(|(poly, bytes)| decompress::<11, 352>(bytes, poly)),
            _ => unreachable!(),
        }

        // 4. v' <- Decompress_dv(ByteDecode_dv(c2))
        let mut v_prime = Coeffs::<Poly, Normal>::zero();
        match P::DV {
            4 => decompress::<4, 128>(c_2.try_into().unwrap(), &mut v_prime.0),
            5 => decompress::<5, 160>(c_2.try_into().unwrap(), &mut v_prime.0),
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
// decoded form goes first, since the whole-value wipe nulls its pointer.
impl<P: Params> Drop for DecapKey<P> {
    fn drop(&mut self) {
        self.ek_pke.free_decoded();
        low::zeroise_value(self);
    }
}

impl<P: Params> low::Zeroable for DecapKey<P> {}

/// An ML-KEM encapsulation key.
#[doc(hidden)]
pub struct EncapKey<P: Params> {
    /// The key as FIPS 203 encodes it, `ByteEncode_12(t^) || 𝜌`.
    bytes: P::EncapKeyBytes,
    /// `H(ek)`, which both encapsulation and decapsulation hash in, if
    /// `hashed`.
    h_ek: [u8; 32],
    /// Whether `h_ek` holds the hash: false only for a key VG parsed, whose
    /// encapsulation hashes it. A flag, not an `Option`, so that the
    /// all-zero value a wipe leaves is a valid one.
    hashed: bool,
    /// What rind's encryption multiplies by: `None` where VG encapsulates,
    /// and once a key pair holding it is wiped. Boxed, as ML-KEM-1024's is
    /// 10 KiB, so moving a key copies little.
    decoded: Option<Box<Decoded<P>>>,
}

/// An encapsulation key decoded for rind's arithmetic.
struct Decoded<P: Params> {
    /// `t_hat` decoded, which the modulus check computes anyway.
    t_hat_coeffs: Coeffs<P::Vector, Ntt>,
    /// The transposed matrix, sampled from `𝜌`.
    transpose_a_hat: Coeffs<P::Matrix, Ntt>,
}

impl<P: Params> Clone for Decoded<P> {
    fn clone(&self) -> Self {
        Self {
            t_hat_coeffs: self.t_hat_coeffs.clone(),
            transpose_a_hat: self.transpose_a_hat.clone(),
        }
    }
}

impl<P: Params> Decoded<P> {
    /// `bytes` decoded, each coefficient reduced mod q, and its matrix
    /// sampled.
    fn new(bytes: &P::EncapKeyBytes) -> Self {
        let (t_hat, rho) = bytes.as_ref().split_at(P::K * 384);
        let mut encoded = Encoded::<P>::filled([0; 384]);
        encoded.as_mut().as_flattened_mut().copy_from_slice(t_hat);
        Self {
            t_hat_coeffs: Coeffs::<P::Vector, Ntt>::from_bytes(&encoded),
            transpose_a_hat: Coeffs::sample(rho.try_into().unwrap(), true),
        }
    }

    fn kpke_encrypt(&self, m: Message, r: KpkeRandomness) -> Ciphertext<P> {
        // 2. t^ <- ByteDecode12(ekPKE[0 ∶ 384k])
        //  - already decoded, as self.t_hat_coeffs.
        // 3. 𝜌 <- ekPKE[384k ∶ 384k + 32]
        //  - only required for a_hat expansion
        // 4. - 8. rolled into self.transpose_a_hat.

        // 9. - 12. y_i <- SamplePolyCBD_eta1(PRF(r, N))
        // 13. - 16. e_1 <- SamplePolyCBD_eta2(PRF(r, N))
        // 17. e_2 <- SamplePolyCBD_eta2(PRF(r, N))
        //
        // N counts on from y's into e_1's and e_2's, so where eta1 is eta2
        // one call samples all three, and hashes them in fewer batches.
        let mut y = Coeffs::<P::Vector, Normal>::zero();
        let mut e_1 = Coeffs::<P::Vector, Normal>::zero();
        let mut e_2 = Coeffs::<Poly, Normal>::zero();
        let errors = e_1.polys_mut().chain(core::iter::once(&mut e_2.0));
        match P::ETA1 == ETA2 {
            true => sample_poly_cbd(ETA2, P::K, &r.0, 0, y.polys_mut().chain(errors)),
            false => {
                sample_poly_cbd(P::ETA1, P::K, &r.0, 0, y.polys_mut());
                sample_poly_cbd(ETA2, P::K, &r.0, P::K as u8, errors);
            }
        }

        // 18. y^ <- NTT(y)
        let y_hat = y.ntt();
        let y_cache = y_hat.mul_cache();

        // 19. u <- NTT^-1(transpose(A^) ∘ y^) + e_1
        let mut u = self
            .transpose_a_hat
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

impl<P: Params> EncapKey<P> {
    /// Wipes and frees the decoded form, so that a key pair's drop can wipe
    /// the rest of the key's value.
    pub(crate) fn free_decoded(&mut self) {
        if let Some(mut decoded) = self.decoded.take() {
            low::zeroise(decoded.t_hat_coeffs.0.as_mut().as_flattened_mut());
            low::zeroise(decoded.transpose_a_hat.0.as_mut().as_flattened_mut());
        }
    }
}

impl<P: Params> Clone for EncapKey<P> {
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
            h_ek: self.h_ek,
            hashed: self.hashed,
            decoded: self.decoded.clone(),
        }
    }
}

impl<P: Params> EncapKey<P> {
    /// A key decoded for rind's arithmetic, from its encoding `bytes`, which
    /// it hashes.
    fn new(bytes: P::EncapKeyBytes, decoded: Decoded<P>) -> Self {
        let mut h = sha3::Sha3_256Context::new();
        h.update(bytes.as_ref());
        Self {
            h_ek: h.finish(),
            hashed: true,
            bytes,
            decoded: Some(Box::new(decoded)),
        }
    }

    /// Create a new [`EncapKey`] from bytes.
    pub(crate) fn from_bytes(input: &P::EncapKeyBytes) -> Result<Self, Error> {
        let _entry = low::Entry::new_public();
        P::parse(Internal(()), input)
    }

    /// [`Self::from_bytes`], under the caller's MXCSR mitigation.
    fn parse_mitigated(input: &P::EncapKeyBytes) -> Result<Self, Error> {
        // 2. (Modulus check) Perform the computation
        //
        //   test <- ByteEncode_12(ByteDecode_12(ek[0 ∶ 384k]))
        //
        // If test != ek[0 ∶ 384k], then input checking failed.
        if let Some(vg) = vg_encaps::<P>() {
            // VG's encapsulation hashes the key itself, almost for free.
            return match vg.check_ek(vg_array(input.as_ref())) {
                true => Ok(Self {
                    bytes: input.clone(),
                    h_ek: [0; 32],
                    hashed: false,
                    decoded: None,
                }),
                false => Err(KeyFormatError::MlKemModulus.into()),
            };
        }
        let decoded = Decoded::new(input);
        let t_hat = &input.as_ref()[..P::K * 384];
        let encoded: Encoded<P> = decoded.t_hat_coeffs.to_bytes();
        if t_hat != encoded.as_ref().as_flattened() {
            return Err(KeyFormatError::MlKemModulus.into());
        }
        Ok(Self::new(input.clone(), decoded))
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

    /// The [`EncapKey`] as FIPS 203 encodes it.
    pub(crate) fn as_bytes(&self) -> &P::EncapKeyBytes {
        &self.bytes
    }

    pub(crate) fn encaps_internal(&self, m: Message) -> (SharedSecret, Ciphertext<P>) {
        P::encaps(Internal(()), self, m)
    }

    /// [`Self::encaps_internal`], under the caller's MXCSR mitigation.
    fn encaps_mitigated(&self, m: Message) -> (SharedSecret, Ciphertext<P>) {
        low::ct::secret_slice(&m.0);

        if let Some(decoded) = &self.decoded {
            return self.encaps_rind(decoded, m);
        }
        // A key VG parsed, or a key pair's where VG encapsulates.
        if let Some(vg) = vg_encaps::<P>() {
            let h_ek = self.hashed.then_some(&self.h_ek);
            // `None` with probability below 2^-261: rind's arithmetic then
            // computes the same secret.
            if let Some((k, c)) = vg_ran(vg.encaps(vg_array(self.bytes.as_ref()), h_ek, &m.0)) {
                let c = P::CiphertextBytes::from_slice(&c).unwrap();
                return (SharedSecret(k), Ciphertext(low::ct::into_public(c)));
            }
        }
        let decoded = Decoded::new(&self.bytes);
        Self::new(self.bytes.clone(), decoded.clone()).encaps_rind(&decoded, m)
    }

    /// FIPS 203's `ML-KEM.Encaps_internal`, on rind's arithmetic over
    /// `decoded`, this key's decoded form, with its hash known.
    fn encaps_rind(&self, decoded: &Decoded<P>, m: Message) -> (SharedSecret, Ciphertext<P>) {
        // 1. (K, r) <- G(m || H(ek))
        let mut g = sha3::Sha3_512Context::new();
        g.update(&m.0);
        g.update(&self.h_ek);
        let kr = g.finish();
        let (k, r) = kr.split_at(32);
        let k = SharedSecret(k.try_into().unwrap());
        let r = KpkeRandomness(r.try_into().unwrap());

        // 2. c <- K-PKE.Encrypt(ek, m, r)
        let c = decoded.kpke_encrypt(m, r);
        (k, Ciphertext(low::ct::into_public(c.0)))
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
#[doc(hidden)]
pub struct Ciphertext<P: Params>(P::CiphertextBytes);

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
#[doc(hidden)]
pub struct Message(pub(crate) [u8; 32]);

/// K-PKE randomness input: `sigma` for key generation, `r` for encryption.
struct KpkeRandomness([u8; 32]);

/// An ML-KEM shared secret.
#[doc(hidden)]
pub struct SharedSecret([u8; 32]);

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

/// `Decompress_D(ByteDecode_D(bytes))` into `out`, for `bytes` of `L = 32 * D`
/// bytes: each `D` bytes yield eight `D`-bit values, little-endian bit order,
/// and each value `y` becomes `round((q / 2^D) * y)`.
///
/// The loops here and in the helpers below count indices, rather than zip
/// iterators, since their proof is about Aeneas's translation, which takes
/// no iterator adapter.
fn decompress<const D: usize, const L: usize>(bytes: &[u8; L], out: &mut Poly) {
    debug_assert_eq!(L, 32 * D);
    for i in 0..N / 8 {
        let mut bits = [0u8; 16];
        bits[..D].copy_from_slice(&bytes[D * i..D * i + D]);
        let bits = u128::from_le_bytes(bits);
        for j in 0..8 {
            let y = ((bits >> (D * j)) as u32) & ((1 << D) - 1);
            out[8 * i + j] = ((y * Q as u32 + (1 << (D - 1))) >> D) as i16;
        }
    }
}

/// `Compress_1(x)`, for `x` in `[0, Q)`.
#[expect(
    clippy::manual_range_contains,
    reason = "Aeneas's library has no `Range::contains`"
)]
fn compress_1(x: i16) -> u8 {
    let public = low::ct::into_public(x);
    debug_assert!(0 <= public && public < Q);
    let x = (x as u64) << 1;
    let x = x.wrapping_add(Q_HALF as u64);
    let x = x.wrapping_mul(80635);
    let x = x >> 28;
    (x & 1) as u8
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

        for i in 0..32 {
            for bit in 0..8 {
                r.0[i * 8 + bit] = ct_select_i16(m.0[i] >> bit & 1, Q_HALF, 0);
            }
        }

        r
    }

    /// This is `ByteEncode_1(Compress_1(m))`
    fn to_message_bits(&self) -> Message {
        let mut r = Message([0; 32]);

        for i in 0..32 {
            let mut byte = 0;
            for bit in 0..8 {
                byte |= compress_1(self.0[i * 8 + bit]) << bit;
            }
            r.0[i] = byte;
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
/// counting from `first`, for the parameter set of rank `k`.
fn sample_poly_cbd<'a>(
    eta: usize,
    k: usize,
    sigma: &[u8; 32],
    first: u8,
    polys: impl Iterator<Item = &'a mut Poly>,
) {
    match eta {
        2 => sample_poly_cbd2(k, sigma, first, polys),
        3 => sample_poly_cbd3(sigma, first, polys),
        _ => unreachable!(),
    }
}

/// [`sample_poly_cbd`] for `eta = 2`, eight polynomials at a time, which
/// x86_64 CPUs with AVX-512 hash at once (but for ML-KEM-768) and others four
/// at a time.
fn sample_poly_cbd2<'a>(
    k: usize,
    sigma: &[u8; 32],
    mut n: u8,
    mut polys: impl Iterator<Item = &'a mut Poly>,
) {
    loop {
        let batch: [Option<&mut Poly>; 8] = core::array::from_fn(|_| polys.next());
        let count = batch.iter().take_while(|p| p.is_some()).count();
        if count == 0 {
            return;
        }

        let mut bufs = [[0; 40]; 8];
        for buf in &mut bufs[..count] {
            buf[..32].copy_from_slice(sigma);
            buf[32] = n;
            buf[33] = sha3::SHAKE_PAD_BYTE;
            n += 1;
        }

        // ML-KEM-768 never hashes eight at a time: it takes its six or
        // seven four at a time, over the verified four-way Keccak-f, so
        // Graviola's unproven eight-way Keccak is off its path, as in
        // `sample_ntt`. Where that would run, ML-KEM-768 runs
        // pyca/verified-garbage's routines instead.
        let mut samples = [[0; 128]; 8];
        match (k, count) {
            (3, _) | (_, 1..=4) => shake256_fours(&bufs, &mut samples, count),
            _ => low::mlkem_shake256_8x(&bufs, &mut samples, count, shake256_fours),
        }

        for (sample, poly) in samples.iter().zip(batch.into_iter().flatten()) {
            sample_cbd2(sample, poly);
        }
    }
}

/// [`sha3::shake256_batch`] of the first `count` of eight inputs, four at a
/// time.
fn shake256_fours(inputs: &[[u8; 40]; 8], outputs: &mut [[u8; 128]; 8], count: usize) {
    let (inputs, _) = inputs.as_chunks::<4>();
    let (outputs, _) = outputs.as_chunks_mut::<4>();
    for (i, (inputs, outputs)) in inputs.iter().zip(outputs).enumerate() {
        match count.saturating_sub(i * 4) {
            0 => {}
            1 => shake256_batch_of::<1>(inputs, outputs),
            2 => shake256_batch_of::<2>(inputs, outputs),
            3 => shake256_batch_of::<3>(inputs, outputs),
            _ => sha3::shake256_batch(inputs, outputs),
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
    for i in 0..N / 8 {
        let t = u32::from_le_bytes([buf[4 * i], buf[4 * i + 1], buf[4 * i + 2], buf[4 * i + 3]]);
        let d = (t & 0x5555_5555).wrapping_add((t >> 1) & 0x5555_5555);

        for j in 0..8 {
            let a = ((d >> (4 * j)) & 0x3) as i16;
            let b = ((d >> (4 * j + 2)) & 0x3) as i16;
            out[8 * i + j] = a.wrapping_sub(b);
        }
    }
}

fn sample_cbd3(buf: &[u8; 192], out: &mut Poly) {
    for i in 0..N / 4 {
        let t = u32::from_le_bytes([buf[3 * i], buf[3 * i + 1], buf[3 * i + 2], 0]);
        let d = (t & 0x0024_9249)
            .wrapping_add((t >> 1) & 0x0024_9249)
            .wrapping_add((t >> 2) & 0x0024_9249);

        for j in 0..4 {
            let a = ((d >> (6 * j)) & 0x7) as i16;
            let b = ((d >> (6 * j + 3)) & 0x7) as i16;
            out[4 * i + j] = a.wrapping_sub(b);
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

    std::thread_local! {
        /// Whether [`vg_ran`] discards this thread's VG results.
        pub(super) static FORCE_FALLBACK: core::cell::Cell<bool> = const { core::cell::Cell::new(false) };
    }

    // Where a VG routine reaches its `SampleNTT` bound, rind's arithmetic
    // computes the same key, ciphertext, and secret: for a key pair VG or
    // rind generated, an encapsulation key with its hash, and one VG parsed,
    // which has none. Where VG runs no routine, both sides are rind's, so it
    // asserts that VG generated and parsed the keys wherever it runs.
    #[test]
    fn fallback_matches_vg() {
        let seed = core::array::from_fn(|i| i as u8);
        let m = || Message([0xa5; 32]);
        let secret = |k: SharedSecret| low::ct::into_public(*k.as_ref());
        let dk = DecapKey::<MlKem768>::keygen_internal(&seed);
        let ek = dk.encapsulation_key();
        let parsed = EncapKey::<MlKem768>::from_bytes(ek.as_bytes()).unwrap();
        // Only VG's routines leave a key without its decoded form.
        assert_eq!(
            dk.ek_pke.decoded.is_none(),
            vg_key_pair::<MlKem768>().is_some()
        );
        assert_eq!(parsed.decoded.is_none(), vg_encaps::<MlKem768>().is_some());
        let (k, c) = ek.encaps_internal(m());
        let k = secret(k);
        assert_eq!(secret(dk.decaps(&c)), k);

        FORCE_FALLBACK.set(true);
        let rind = DecapKey::<MlKem768>::keygen_internal(&seed);
        assert!(rind.ek_pke.decoded.is_some());
        assert_eq!(
            low::ct::into_public(rind.as_bytes()),
            low::ct::into_public(dk.as_bytes())
        );
        assert_eq!(rind.encapsulation_key().as_bytes(), ek.as_bytes());
        for ek in [&ek, &parsed] {
            let (k_ek, c_ek) = ek.encaps_internal(m());
            assert_eq!((secret(k_ek), c_ek.as_ref()), (k, c.as_ref()));
        }
        assert_eq!(secret(dk.decaps(&c)), k);
        assert_eq!(secret(rind.decaps(&c)), k);
        FORCE_FALLBACK.set(false);
    }

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

    #[test]
    fn decaps_input_check_skips_the_modulus_check() {
        // A decapsulation key whose embedded encapsulation key holds the
        // coefficient q, with that key's hash: FIPS 203's section 7.3 checks
        // only the hash, and ByteDecode_12 reduces q to 0.
        fn check<P: Params>() {
            let mut dk = DecapKey::<P>::keygen_internal(&[0x5a; 64]).as_bytes();
            let dk = dk.as_mut();
            dk[P::K * 384] = 0x01;
            dk[P::K * 384 + 1] = (dk[P::K * 384 + 1] & 0xf0) | 0x0d;
            let ek = P::EncapKeyBytes::from_slice(&dk[P::K * 384..P::K * 768 + 32]).unwrap();
            assert!(EncapKey::<P>::from_bytes(&ek).is_err());
            let mut h = sha3::Sha3_256Context::new();
            h.update(ek.as_ref());
            let h = h.finish();
            dk[P::K * 768 + 32..P::K * 768 + 64].copy_from_slice(&h);
            let key =
                DecapKey::<P>::from_bytes(&P::DecapKeyBytes::from_slice(dk).unwrap()).unwrap();
            assert_eq!(key.ek_pke.h_ek, h);
            assert_eq!(
                key.ek_pke.decoded.as_ref().unwrap().t_hat_coeffs.0.as_ref()[0][0],
                0
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
        fn check<const D: usize, const L: usize>(compress: fn(&mut [u8], &Poly)) {
            for start in (0..Q as usize + 7).step_by(N - 7) {
                let poly = Coeffs::<Poly, Normal>(
                    core::array::from_fn(|i| ((start + i) % Q as usize) as i16),
                    PhantomData,
                );
                let mut bytes = [0; 32 * 11];
                compress(&mut bytes[..32 * D], &poly.0);
                let mut out = [0; N];
                decompress::<D, L>(bytes[..32 * D].try_into().unwrap(), &mut out);
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
        check::<4, 128>(|r, a| low::mlkem_compress_d4(r.try_into().unwrap(), &aligned(a).0));
        check::<5, 160>(|r, a| low::mlkem_compress_d5(r.try_into().unwrap(), &aligned(a).0));
        check::<10, 320>(|r, a| low::mlkem_compress_d10(r.try_into().unwrap(), &aligned(a).0));
        check::<11, 352>(|r, a| low::mlkem_compress_d11(r.try_into().unwrap(), &aligned(a).0));
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

        // pyca/verified-garbage's ML-KEM-768 encapsulation, which runs with
        // SHA3, to a key pair's public key, with its hash, and to a parsed
        // one, without.
        assert!(vg_encaps::<MlKem768>().is_some());
        let dk = DecapKey::<MlKem768>::keygen_internal(&[0x5a; 64]);
        let m = || Message(core::array::from_fn(|i| seed[i % seed.len()]));
        let ek = dk.encapsulation_key();
        ct_qemu::traced(|| ek.encaps_internal(m()));
        let ek = EncapKey::<MlKem768>::from_bytes(ek.as_bytes()).unwrap();
        ct_qemu::traced(|| ek.encaps_internal(m()));
    }

    // Valgrind runs no AVX-512, so `admin/ctgrind` never reaches
    // pyca/verified-garbage's ML-KEM-768 key generation and decapsulation,
    // nor its AVX-512 encapsulation; `admin/ct-sde` traces them here, under
    // Sapphire Rapids, as `ct_qemu_mlkem` traces aarch64's. Encapsulating a
    // secret message to a fixed key, with the key's hash and without, then
    // decapsulating the ciphertext and a tampered copy. A second key then
    // takes its implicit-rejection secret `z` from the seed, as its
    // generation is traced: `𝜌` comes from the rest, so it stays fixed.
    // Fixing `d` also fixes the secret vectors it derives, and key generation
    // cannot vary them without varying `𝜌`, so the last key decapsulates
    // with the fixed key's `ek` but the `dkPKE` of a key generated from a
    // seeded `d`. VG's contract asks for a whole key its key generation
    // wrote, and none varies `dkPKE` with `𝜌` fixed; each field here is one
    // VG's key generation wrote, so every coefficient is in range.
    #[cfg(rind_backend = "x86_64")]
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_mlkem768() {
        use crate::low::ct_sde;

        assert!(vg_key_pair::<MlKem768>().is_some(), "AVX-512 F, BW, and VL");
        let seed = ct_sde::seed().to_le_bytes();
        let m = || Message(core::array::from_fn(|i| seed[i % seed.len()]));
        let dk = DecapKey::<MlKem768>::keygen_internal(&[0x5a; 64]);
        let ek = dk.encapsulation_key();
        let (_, c) = ct_sde::traced(|| ek.encaps_internal(m()));
        let ek = EncapKey::<MlKem768>::from_bytes(ek.as_bytes()).unwrap();
        ct_sde::traced(|| ek.encaps_internal(m()));
        ct_sde::traced(|| dk.decaps(&c));
        let mut c = c.0;
        c[0] ^= 1;
        ct_sde::traced(|| dk.decaps(&Ciphertext(c)));

        let dk = ct_sde::traced(|| {
            DecapKey::<MlKem768>::keygen_internal(&core::array::from_fn(|i| match i {
                ..32 => 0x5a,
                _ => seed[i % seed.len()],
            }))
        });
        let (_, c) = dk.encapsulation_key().encaps_internal(Message([0xa5; 32]));
        ct_sde::traced(|| dk.decaps(&c));
        let mut c = c.0;
        c[0] ^= 1;
        ct_sde::traced(|| dk.decaps(&Ciphertext(c)));

        let fixed = DecapKey::<MlKem768>::keygen_internal(&[0x5a; 64]).encode();
        let seeded = DecapKey::<MlKem768>::keygen_internal(&core::array::from_fn(|i| {
            seed[i % seed.len()] ^ i as u8
        }))
        .encode();
        let mut spliced = fixed;
        spliced[..3 * 384].copy_from_slice(&seeded[..3 * 384]);
        let dk = DecapKey::<MlKem768>::decode(&spliced, false);
        let (_, c) = dk.encapsulation_key().encaps_internal(Message([0xa5; 32]));
        ct_sde::traced(|| dk.decaps(&c));
    }
}
