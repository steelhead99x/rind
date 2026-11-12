// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-KEM-768 as standardised by FIPS-203.

use core::fmt;
use core::marker::PhantomData;

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

/// An ML-KEM-768 decapsulation key.
pub(crate) struct DecapKey {
    ek_pke: EncapKey,
    dk_pke: [u8; K * 384],
    z: [u8; 32],
}

impl DecapKey {
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
    pub(crate) fn decaps(&self, c: &Ciphertext) -> SharedSecret {
        let _entry = low::Entry::new_secret();
        self.decaps_internal(c)
    }

    /// Return the corresponding [`EncapKey`].
    pub(crate) fn encapsulation_key(&self) -> EncapKey {
        let _entry = low::Entry::new_public();
        self.ek_pke.clone()
    }

    /// Encode the key as bytes.
    ///
    /// Used by tests and by `rind-acvp`, which answers NIST's seeded key
    /// generation. rind's own callers generate from the system RNG.
    #[cfg(any(test, feature = "acvp"))]
    pub(crate) fn as_bytes(&self) -> [u8; K * 768 + 96] {
        let _entry = low::Entry::new_secret();
        let mut out = [0u8; K * 768 + 96];
        out[..K * 384].copy_from_slice(&self.dk_pke);
        out[K * 384..K * 768].copy_from_slice(&self.ek_pke.t_hat_coeffs.to_bytes());
        out[K * 768..K * 768 + 32].copy_from_slice(&self.ek_pke.rho);
        out[K * 768 + 32..K * 768 + 64].copy_from_slice(&self.ek_pke.h_ek);
        out[K * 768 + 64..].copy_from_slice(&self.z);
        out
    }

    /// Decode a key encoded as [`Self::as_bytes()`] encodes it, or `None` if
    /// its `H(ek)` is not that of its encapsulation key.
    ///
    /// This is used for testing and `rind-acvp`: rind generates keys only from seeds.
    #[cfg(any(test, feature = "acvp"))]
    pub(crate) fn from_bytes(dk: &[u8; K * 768 + 96]) -> Option<Self> {
        let (dk_pke, rest) = dk.split_at(K * 384);
        let (ek, rest) = rest.split_at(K * 384 + 32);
        let (h_ek, z) = rest.split_at(32);
        let ek_pke = EncapKey::from_bytes(ek.try_into().unwrap()).ok()?;
        (ek_pke.h_ek == h_ek).then(|| Self {
            ek_pke,
            dk_pke: dk_pke.try_into().unwrap(),
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

    fn decaps_internal(&self, c: &Ciphertext) -> SharedSecret {
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
        j.absorb(&c.0);
        j.finish().squeeze(&mut k_bar.0);

        // 8. c' <- K-PKE.Encrypt(ekPKE, m', r')
        let c_prime = self.ek_pke.kpke_encrypt(m_prime, r_prime);

        // 9. - 11. if c != c' then K' <- K‾
        // 12. return K'
        ct_copy(ct_equal(&c.0, &c_prime.0), &mut k_prime.0, &k_bar.0);
        k_prime
    }

    /// This is Algorithm 13: K-PKE.KeyGen(d) -> (ek_PKE, dk_PKE)
    fn kpke_keygen(d: &[u8; 32]) -> (EncapKey, [u8; K * 384]) {
        // 1. (𝜌, 𝜎) <- G(d || k)
        let mut g = sha3::Sha3_512Context::new();
        g.update(d);
        g.update(&[K_BYTE]);
        let g = g.finish();
        let (rho, sigma) = g.split_at(32);
        // rho seeds the public matrix, so it is public.
        let rho: [u8; 32] = low::ct::into_public(rho.try_into().unwrap());
        let sigma = KpkeRandomness(sigma.try_into().unwrap());

        // 3. - 7.
        let a_hat = Coeffs::sample_poly(&rho);

        // 8. - 15.
        let mut s = Coeffs::zero();
        let mut e = Coeffs::zero();
        sample_poly_cbd::<{ 2 * K }>(&sigma.0, s.polys_mut().chain(e.polys_mut()));

        // 16. ŝ <- NTT(s)
        let mut s_hat = s.ntt();

        // 17. ê <- NTT(e)
        let e_hat = e.ntt();

        // 18. t^ = A^ ∘ ŝ + ê
        let t_hat = a_hat.mul_add(&s_hat, &e_hat);

        // H(ek), for ML-KEM.KeyGen's step 3.
        let mut h = sha3::Sha3_256Context::new();
        h.update(&low::ct::into_public(t_hat.to_bytes()));
        h.update(&rho);
        let encap = EncapKey {
            h_ek: h.finish(),
            rho,
            t_hat_coeffs: Coeffs(low::ct::into_public(t_hat.0), PhantomData),
            transpose_a_hat: a_hat.transpose(),
        };

        s_hat.reduce_in_place();
        let decap = s_hat.to_bytes();

        (encap, decap)
    }

    /// This is Algorithm 15: K-PKE.Decrypt(dk_PKE, c)
    fn kpke_decrypt(&self, c: &Ciphertext) -> Message {
        // 1. c_1 <- c[0 ∶ 32 * du * k]
        // 2. c_2 <- c[32 * du * k ∶ 32 * (du * k + dv)]
        let (c_1, c_2) = c.0.split_at(32 * DU * K);

        // 3. u' <- Decompress_du(ByteDecode_du(c1))
        let u_prime = Coeffs::decompress_from_bytes_du_10(c_1.try_into().unwrap());
        // 4. v' <- Decompress_dv(ByteDecode_dv(c2))
        let v_prime = Coeffs::decompress_from_bytes_dv_4(c_2.try_into().unwrap());

        // 5. s^ <- ByteDecode_12(dk_PKE)
        let s_hat = Coeffs::from_bytes(&self.dk_pke);

        // 6. w <- v' - NTT-1(transpose(s^) * NTT(u'))
        let u_hat = u_prime.ntt();
        let w = v_prime.sub(&s_hat.mul_and_inverse_ntt(&u_hat, &u_hat.mul_cache()));

        // 7. m <- ByteEncode_1(Compress_1(w))
        w.to_message_bits()
    }
}

// Wiped whole, so no byte of the key survives, padding included.
impl Drop for DecapKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::Zeroable for DecapKey {}

/// An ML-KEM-768 encapsulation key.
#[derive(Clone)]
pub(crate) struct EncapKey {
    /// `H(ek)`, which both encapsulation and decapsulation hash in.
    h_ek: [u8; 32],
    rho: [u8; 32],
    /// `t_hat` decoded, which the modulus check computes anyway. No encoded
    /// copy is kept: only `as_bytes` needs one, and it re-encodes.
    t_hat_coeffs: Coeffs<{ K * N }, Ntt>,
    transpose_a_hat: Coeffs<{ K * K * N }, Ntt>,
}

impl EncapKey {
    /// Create a new [`EncapKey`] from bytes.
    pub(crate) fn from_bytes(input: &[u8; K * 384 + 32]) -> Result<Self, Error> {
        let _entry = low::Entry::new_public();
        let (t_hat, rho) = input.split_at(K * 384);
        let t_hat = t_hat.try_into().unwrap();
        let rho = rho.try_into().unwrap();

        // 2. (Modulus check) Perform the computation
        //
        //   test <- ByteEncode_12(ByteDecode_12(ek[0 ∶ 384k]))
        //
        // If test != ek[0 ∶ 384k], then input checking failed.
        let t_hat_coeffs = Coeffs::from_bytes(&t_hat);
        if t_hat != t_hat_coeffs.to_bytes() {
            return Err(KeyFormatError::MlKemModulus.into());
        }

        let transpose_a_hat = Coeffs::sample_poly_transposed(&rho);

        let mut h = sha3::Sha3_256Context::new();
        h.update(input);

        Ok(Self {
            h_ek: h.finish(),
            rho,
            t_hat_coeffs,
            transpose_a_hat,
        })
    }

    /// Encapsulate a random shared secret, returning the shared secret and a ciphertext.
    ///
    /// The ciphertext can be returned to the holder of the [`DecapKey`] who can then
    /// derive the same [`SharedSecret`].
    pub(crate) fn encaps(&self) -> Result<(SharedSecret, Ciphertext), Error> {
        let _entry = low::Entry::new_secret();
        let mut m = Message([0; 32]);
        SystemRandom.fill(&mut m.0)?;
        Ok(self.encaps_internal(m))
    }

    /// Encode the [`EncapKey`] as bytes.
    pub(crate) fn as_bytes(&self) -> [u8; K * 384 + 32] {
        let _entry = low::Entry::new_public();
        let mut out = [0u8; K * 384 + 32];
        out[..K * 384].copy_from_slice(&self.t_hat_coeffs.to_bytes());
        out[K * 384..].copy_from_slice(&self.rho);
        out
    }

    pub(crate) fn encaps_internal(&self, m: Message) -> (SharedSecret, Ciphertext) {
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

    fn kpke_encrypt(&self, m: Message, r: KpkeRandomness) -> Ciphertext {
        // 2. t^ <- ByteDecode12(ekPKE[0 ∶ 384k])
        //  - already decoded, as self.t_hat_coeffs.
        // 3. 𝜌 <- ekPKE[384k ∶ 384k + 32]
        //  - only required for a_hat expansion
        // 4. - 8. rolled into self.transpose_a_hat.

        // 9. - 12.
        // 13. - 16.
        // 17. e_2 <- SamplePolyCBD(PRF (r, N))
        let mut y = Coeffs::zero();
        let mut e_1 = Coeffs::zero();
        let mut e_2 = Coeffs::zero();
        sample_poly_cbd::<{ 2 * K + 1 }>(
            &r.0,
            y.polys_mut().chain(e_1.polys_mut()).chain(e_2.polys_mut()),
        );

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
            .mul_and_inverse_ntt(&y_hat, &y_cache)
            .add(&e_2)
            .add(&mu);
        v.reduce_in_place();

        let mut c = Ciphertext([0; _]);
        let (c_1, c_2) = c.0.split_at_mut(32 * DU * K);

        // 22. c_1 <- ByteEncode_du(Compress_du(u))
        u.compress_into_bytes_du_10(c_1.try_into().unwrap());
        // 23. c_2 <- ByteEncode_dv(Compress_dv(v))
        v.compress_into_bytes_dv_4(c_2.try_into().unwrap());

        // 24. return c <- (c_1 || c_2)
        c
    }
}

/// An ML-KEM-768 ciphertext.
#[derive(Debug, Clone)]
pub(crate) struct Ciphertext([u8; 32 * (DU * K + DV)]);

impl From<[u8; 1088]> for Ciphertext {
    fn from(value: [u8; 1088]) -> Self {
        Self(value)
    }
}

impl AsRef<[u8; 1088]> for Ciphertext {
    fn as_ref(&self) -> &[u8; 1088] {
        &self.0
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

/// Tracks what the values in a `Coeffs` mean.
trait Domain: Clone {}

/// Coefficients in normal domain.
#[derive(Clone)]
struct Normal;
impl Domain for Normal {}

/// Coefficients in NTT domain.
#[derive(Clone)]
struct Ntt;
impl Domain for Ntt {}

/// Multiplication cache values.
#[derive(Clone)]
struct MulCache;
impl Domain for MulCache {}

/// Polynomial coefficients.
///
/// Arithmetic on coefficients, here and in the compression and sampling
/// helpers, wraps: their bounds rule out overflow, and a debug build's
/// overflow check would branch on secret values.
#[derive(Clone, Debug)]
#[repr(align(32))]
struct Coeffs<const C: usize, D: Domain>([i16; C], PhantomData<D>);

impl<const C: usize, D: Domain> Coeffs<C, D> {
    const fn zero() -> Self {
        Self([0; C], PhantomData)
    }

    /// Each polynomial's coefficients.
    fn polys_mut(&mut self) -> impl Iterator<Item = &mut [i16; N]> {
        self.0.as_chunks_mut().0.iter_mut()
    }

    /// Reduce coefficients into [0, Q)
    fn reduce_in_place(&mut self) {
        for k in self.0.as_chunks_mut().0 {
            low::mlkem_reduce(k);
        }
    }
}

impl Coeffs<{ K * K * N }, Ntt> {
    fn sample_poly(rho: &[u8; 32]) -> Self {
        let mut r = Self(sample_ntt::sample_ntt(rho), PhantomData);
        r.reorder();
        r
    }

    fn sample_poly_transposed(rho: &[u8; 32]) -> Self {
        let mut r = Self(sample_ntt::sample_ntt_transposed(rho), PhantomData);
        r.reorder();
        r
    }

    // a * s + e
    fn mul_add(
        &self,
        s: &Coeffs<{ K * N }, Ntt>,
        e: &Coeffs<{ K * N }, Ntt>,
    ) -> Coeffs<{ K * N }, Ntt> {
        let mut r = e.clone();

        let s_precomp = s.mul_cache();

        let mut term = Coeffs::<_, Ntt>::zero();

        for (aa, rr) in self
            .0
            .as_chunks()
            .0
            .iter()
            .zip(r.0.as_chunks_mut::<N>().0.iter_mut())
        {
            low::mlkem_basemul_k3(&mut term.0, aa, &s.0, &s_precomp.0);
            low::mlkem_tomont(&mut term.0);

            for (r, t) in rr.iter_mut().zip(term.0.iter()) {
                *r = r.wrapping_add(*t);
            }
        }

        r.reduce_in_place();
        r
    }

    fn reorder(&mut self) {
        for ch in self.0.as_chunks_mut().0 {
            low::mlkem_unpack(ch);
        }
    }

    fn transpose(mut self) -> Self {
        let (chunks, _) = self.0.as_chunks_mut::<N>();

        for i in 0..K {
            for j in (i + 1)..K {
                chunks.swap(i * K + j, j * K + i);
            }
        }

        self
    }

    /// This is `NTT-1(self * y)`, given `y`'s mulcache `y_cache`.
    ///
    /// The inverse NTT takes any `i16`, so the products go in unreduced.
    fn mul_and_inverse_ntt(
        &self,
        y: &Coeffs<{ K * N }, Ntt>,
        y_cache: &Coeffs<{ K * 128 }, MulCache>,
    ) -> Coeffs<{ K * N }, Normal> {
        let mut r = Coeffs::<_, Ntt>::zero();

        for (aa, rr) in self.0.as_chunks().0.iter().zip(r.polys_mut()) {
            low::mlkem_basemul_k3(rr, aa, &y.0, &y_cache.0);
        }

        r.inverse_ntt()
    }
}

impl Coeffs<{ K * N }, Ntt> {
    /// This is `ByteDecode_12(bytes)`.
    fn from_bytes(bytes: &[u8; 1152]) -> Self {
        let mut r = Coeffs::zero();

        let (r_chunks, _) = r.0.as_chunks_mut();
        let (b_chunks, _) = bytes.as_chunks();

        for (rr, bb) in r_chunks.iter_mut().zip(b_chunks.iter()) {
            low::mlkem_frombytes(rr, bb);
            low::mlkem_reduce(rr);
        }

        r
    }

    /// This is `ByteEncode_12(self)`
    fn to_bytes(&self) -> [u8; 1152] {
        let mut r = [0u8; 1152];

        let (c_chunks, _) = self.0.as_chunks();
        let (r_chunks, _) = r.as_chunks_mut();

        for (rr, cc) in r_chunks.iter_mut().zip(c_chunks.iter()) {
            low::mlkem_tobytes(rr, cc);
        }

        r
    }

    /// This is `NTT-1(self * s)`, given `s`'s mulcache `s_cache`.
    fn mul_and_inverse_ntt(
        &self,
        s: &Coeffs<{ K * N }, Ntt>,
        s_cache: &Coeffs<{ K * 128 }, MulCache>,
    ) -> Coeffs<{ N }, Normal> {
        let mut r = Coeffs::zero();

        low::mlkem_basemul_k3(&mut r.0, &self.0, &s.0, &s_cache.0);
        // nb. no need for a tomont here, as `inverse_ntt` incorporates that

        r.inverse_ntt()
    }

    fn mul_cache(&self) -> Coeffs<{ K * 128 }, MulCache> {
        let mut r = Coeffs::zero();

        let (m, _) = self.0.as_chunks();
        let (rr, _) = r.0.as_chunks_mut();

        low::mlkem_mulcache_compute(&mut rr[0], &m[0]);
        low::mlkem_mulcache_compute(&mut rr[1], &m[1]);
        low::mlkem_mulcache_compute(&mut rr[2], &m[2]);

        r
    }
}

impl<const C: usize> Coeffs<C, Ntt> {
    fn inverse_ntt(mut self) -> Coeffs<C, Normal> {
        for ch in self.0.as_chunks_mut().0 {
            low::mlkem_intt(ch);
        }
        Coeffs(self.0, PhantomData)
    }
}

/// `Decompress_4(y) = round((q / 2^4) * y)`, for y in [0, 2^4)
fn decompress_4(y: u16) -> i16 {
    debug_assert!(y < 16);
    let d = y as u32;
    let d = d * (Q as u32);
    let d = d + 8;
    let d = d >> 4;
    d as i16
}

/// `Decompress_10(y) = round((q / 2^10) * y)`, for y in [0, 2^10)
fn decompress_10(y: u16) -> i16 {
    debug_assert!(y < 1024);
    let d = y as u32;
    let d = d * (Q as u32);
    let d = d + 512;
    let d = d >> 10;
    d as i16
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

impl Coeffs<{ K * N }, Normal> {
    /// K-wise NTT
    fn ntt(mut self) -> Coeffs<{ K * N }, Ntt> {
        for ch in self.0.as_chunks_mut().0 {
            low::mlkem_ntt(ch);
        }
        Coeffs(self.0, PhantomData)
    }

    /// This is `ByteEncode_10(Compress_10(u))`, for `u` in `[0, Q)`
    fn compress_into_bytes_du_10(&self, c_1: &mut [u8; 960]) {
        let (polys, _) = self.0.as_chunks::<N>();
        let (out_chunks, _) = c_1.as_chunks_mut::<320>();

        for (poly, out) in polys.iter().zip(out_chunks.iter_mut()) {
            low::mlkem_compress_d10(out, poly);
        }
    }

    /// This is `Decompress_10(ByteDecode_10(c_1))`
    ///
    /// The inverse of [`Self::compress_into_bytes_du_10`]: each group of
    /// five bytes yields four ten-bit values, little-endian bit order.
    fn decompress_from_bytes_du_10(c_1: &[u8; 960]) -> Self {
        let mut r = Self::zero();

        let (in_chunks, _) = c_1.as_chunks::<5>();
        let (quads, _) = r.0.as_chunks_mut::<4>();

        for (inp, quad) in in_chunks.iter().zip(quads.iter_mut()) {
            let t0 = (inp[0] as u16) | ((inp[1] as u16 & 0x3) << 8);
            let t1 = ((inp[1] as u16) >> 2) | ((inp[2] as u16 & 0xf) << 6);
            let t2 = ((inp[2] as u16) >> 4) | ((inp[3] as u16 & 0x3f) << 4);
            let t3 = ((inp[3] as u16) >> 6) | ((inp[4] as u16) << 2);

            quad[0] = decompress_10(t0);
            quad[1] = decompress_10(t1);
            quad[2] = decompress_10(t2);
            quad[3] = decompress_10(t3);
        }

        r
    }
}

impl Coeffs<N, Normal> {
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

    /// This is `ByteEncode_4(Compress_4(v))`, for `v` in `[0, Q)`
    fn compress_into_bytes_dv_4(&self, c_2: &mut [u8; 128]) {
        low::mlkem_compress_d4(c_2, &self.0);
    }

    /// This is `Decompress_4(ByteDecode_4(c_2))`
    ///
    /// The inverse of [`Self::compress_into_bytes_dv_4`]: each byte yields
    /// two four-bit values, low nibble first.
    fn decompress_from_bytes_dv_4(c_2: &[u8; 128]) -> Self {
        let mut r = Self::zero();

        let (pairs, _) = r.0.as_chunks_mut::<2>();
        for (byte, pair) in c_2.iter().zip(pairs.iter_mut()) {
            pair[0] = decompress_4((byte & 0xf) as u16);
            pair[1] = decompress_4((byte >> 4) as u16);
        }

        r
    }
}

impl<const C: usize> Coeffs<C, Normal> {
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
        self.reduce_in_place();
        self
    }
}

/// `SamplePolyCBD(PRF(sigma, n))` into the `n`th of the `P` `polys`.
fn sample_poly_cbd<'a, const P: usize>(
    sigma: &[u8; 32],
    mut polys: impl Iterator<Item = &'a mut [i16; N]>,
) {
    let mut samples = [[0; 128]; P];

    // Prepare P SHAKE256 inputs.
    let mut bufs = [[0; 40]; P];
    for (n, buf) in bufs.iter_mut().enumerate() {
        buf[..32].copy_from_slice(sigma);
        buf[32] = n as u8;
        buf[33] = sha3::SHAKE_PAD_BYTE;
    }

    sha3::shake256_batch(&bufs, &mut samples);

    for (sample, poly) in samples.iter().zip(polys.by_ref()) {
        sample_cbd2(sample, poly);
    }
    debug_assert!(polys.next().is_none());
}

fn sample_cbd2(buf: &[u8; 128], out: &mut [i16; 256]) {
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

const K: usize = 3;
const K_BYTE: u8 = K as u8;
const DU: usize = 10;
const DV: usize = 4;

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
        for group in acvp("ML-KEM-keyGen-FIPS203") {
            assert_eq!(group.str("parameterSet"), "ML-KEM-768");
            for test in group.tests() {
                let dk = DecapKey::keygen_internal(&acvp_seed(test));
                assert_eq!(dk.encapsulation_key().as_bytes(), &test.hex("ek")[..]);
                assert_eq!(low::ct::into_public(dk.as_bytes()), &test.hex("dk")[..]);
            }
        }
    }

    #[test]
    fn acvp_encap_decap() {
        for group in acvp("ML-KEM-encapDecap-FIPS203-tr1") {
            assert_eq!(group.str("parameterSet"), "ML-KEM-768");
            for test in group.tests() {
                let ek = || EncapKey::from_bytes(&test.hex("ek").try_into().unwrap());
                let dk = || DecapKey::from_bytes(&test.hex("dk").try_into().unwrap());
                let ciphertext =
                    || Ciphertext::from(<[u8; 1088]>::try_from(test.hex("c")).unwrap());
                match (group.str("function"), group.str("keyFormat")) {
                    ("encapsulation", "none") => {
                        let m = Message(test.hex("m").try_into().unwrap());
                        let (k, c) = ek().unwrap().encaps_internal(m);
                        assert_eq!(low::ct::into_public(*k.as_ref()), &test.hex("k")[..]);
                        assert_eq!(c.as_ref(), &test.hex("c")[..]);
                    }
                    ("decapsulation", "seed") => {
                        let dk = DecapKey::keygen_internal(&acvp_seed(test));
                        assert_eq!(low::ct::into_public(dk.as_bytes()), &test.hex("dk")[..]);
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
    }

    #[test]
    fn shared_secret_debug() {
        assert_eq!(format!("{:?}", SharedSecret([0u8; 32])), "SharedSecret(..)");
    }

    #[test]
    fn pairwise() {
        let d = DecapKey::generate().unwrap();
        let (ess, ct) = d.encapsulation_key().encaps().unwrap();
        let dss = d.decaps(&ct);
        assert_eq!(low::ct::into_public(ess.0), low::ct::into_public(dss.0));
    }

    #[test]
    fn encaps_modulus_test() {
        assert_eq!(
            EncapKey::from_bytes(&[0xffu8; 1184]).err(),
            Some(KeyFormatError::MlKemModulus.into())
        );
    }

    // Valgrind hides SHA3, so `admin/ctgrind` never reaches the Keccak
    // kernels aarch64 runs with it; `admin/ct-qemu` traces them here instead,
    // under qemu-aarch64's `max` CPU. Encapsulating a secret message takes
    // the one-, two-, and four-way kernels, and decapsulation runs them on
    // the secret key, for a ciphertext it accepts and one it rejects. The key
    // is fixed between runs, so the public matrix is too. A second key then
    // shares that public key but takes its implicit-rejection secret `z` from
    // the seed, and decapsulates fixed ciphertexts, so only `z` varies.
    #[cfg(rind_backend = "aarch64")]
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_mlkem768() {
        use crate::low::ct_qemu;

        assert!(std::arch::is_aarch64_feature_detected!("sha3"), "SHA3");
        let seed = ct_qemu::seed().to_le_bytes();
        let dk = DecapKey::keygen_internal(&[0x5a; 64]);
        let m = Message(core::array::from_fn(|i| seed[i % seed.len()]));
        let (_, mut c) = ct_qemu::traced(|| dk.ek_pke.encaps_internal(m));
        ct_qemu::traced(|| dk.decaps(&c));
        c.0[0] ^= 1;
        ct_qemu::traced(|| dk.decaps(&c));

        let dk = DecapKey::keygen_internal(&core::array::from_fn(|i| match i {
            ..32 => 0x5a,
            _ => seed[i % seed.len()],
        }));
        let (_, mut c) = dk.ek_pke.encaps_internal(Message([0xa5; 32]));
        ct_qemu::traced(|| dk.decaps(&c));
        c.0[0] ^= 1;
        ct_qemu::traced(|| dk.decaps(&c));
    }
}
