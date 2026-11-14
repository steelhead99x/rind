// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

//! ML-DSA, as FIPS 204 specifies it: a port of mldsa-native v2.0.0's
//! `sign.c`, `packing.c`, `poly.c`, and `poly_kl.c` over the `low` layer's
//! arithmetic, which is s2n-bignum's where it has a routine.
//!
//! Like mldsa-native, signing declassifies which attempt it accepts, and why
//! it rejects the others: FIPS 204's security argument makes them public.
//!
//! Coefficient arithmetic wraps: the bounds rule out overflow, and a debug
//! build's overflow check would branch on secret values.

// A parameter set's dimensions are associated constants, which stable Rust
// cannot pass as `as_chunks`'s const argument in generic code.
#![allow(clippy::chunks_exact_to_as_chunks)]

use core::fmt;
use core::panic::{RefUnwindSafe, UnwindSafe};

use crate::Error;
use crate::error::KeyFormatError;
use crate::low::{self, Entry, MldsaPoly as Poly};
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::sha3::{
    SHAKE_128_R_BYTES, SHAKE_256_R_BYTES, Shake128x4, Shake256, Shake256Sponge, Shake256x4,
};

const N: usize = 256;
const Q: i32 = 8380417;
const D: u32 = 13;

/// The length of a key's seed, `xi`.
pub(crate) const SEED_LEN: usize = 32;
pub(crate) const TR_LEN: usize = 64;
const MU_LEN: usize = 64;
const RND_LEN: usize = 32;
const T1_PACKED: usize = 320;
const T0_PACKED: usize = 416;

/// mldsa-native's `MLD_MAX_KAPPA`: a mask's nonce is 16 bits.
const MAX_KAPPA: usize = 0xffff;

/// ML-DSA-44, as standardised by FIPS 204.
#[derive(Debug)]
pub enum MlDsa44 {}

/// ML-DSA-65, as standardised by FIPS 204.
#[derive(Debug)]
pub enum MlDsa65 {}

/// ML-DSA-87, as standardised by FIPS 204.
#[derive(Debug)]
pub enum MlDsa87 {}

/// A FIPS 204 parameter set: its dimensions `K` and `L` and its bounds, with
/// the arrays its encodings fill, which stable Rust cannot size from the
/// constants.
///
/// Its bounds, like [`Array`]'s, let a generic caller rely on the auto
/// traits every key and signature has.
pub trait Params: fmt::Debug + Send + Sync + Unpin + UnwindSafe + RefUnwindSafe + 'static {
    #[doc(hidden)]
    const K: usize;
    #[doc(hidden)]
    const L: usize;
    #[doc(hidden)]
    const ETA: i32;
    #[doc(hidden)]
    const TAU: usize;
    #[doc(hidden)]
    const GAMMA1_BITS: u32;
    #[doc(hidden)]
    const GAMMA2: i32;
    #[doc(hidden)]
    const OMEGA: usize;
    #[doc(hidden)]
    const CTILDE_LEN: usize;

    #[doc(hidden)]
    const BETA: i32 = Self::TAU as i32 * Self::ETA;
    #[doc(hidden)]
    const GAMMA1: i32 = 1 << Self::GAMMA1_BITS;
    #[doc(hidden)]
    const ETA_PACKED: usize = if Self::ETA == 2 { 96 } else { 128 };
    #[doc(hidden)]
    const Z_PACKED: usize = 32 * (Self::GAMMA1_BITS as usize + 1);
    #[doc(hidden)]
    const W1_PACKED: usize = if Self::GAMMA2 == (Q - 1) / 88 {
        192
    } else {
        128
    };

    /// `pk`, FIPS 204's public key encoding.
    #[doc(hidden)]
    type PublicKey: Array;
    /// `sk`, FIPS 204's expanded private key encoding.
    #[doc(hidden)]
    type SecretKey: Array;
    /// `sigma`, FIPS 204's signature encoding.
    #[doc(hidden)]
    type Signature: Array;
}

/// A byte array of a parameter set's length.
pub trait Array:
    Clone
    + fmt::Debug
    + AsRef<[u8]>
    + AsMut<[u8]>
    + Send
    + Sync
    + Unpin
    + UnwindSafe
    + RefUnwindSafe
    + 'static
{
    /// Every byte zero.
    #[doc(hidden)]
    fn zeroed() -> Self;
}

impl<const LEN: usize> Array for [u8; LEN] {
    fn zeroed() -> Self {
        [0; LEN]
    }
}

macro_rules! params {
    ($(
        $set:ident: K = $k:literal, L = $l:literal, ETA = $eta:literal, TAU = $tau:literal,
        GAMMA1 = 2^$gamma1:literal, GAMMA2 = (Q - 1) / $gamma2:literal, OMEGA = $omega:literal,
        LAMBDA = $lambda:literal, pk = $pk:literal, sk = $sk:literal, sig = $sig:literal;
    )*) => {$(
        impl Params for $set {
            const K: usize = $k;
            const L: usize = $l;
            const ETA: i32 = $eta;
            const TAU: usize = $tau;
            const GAMMA1_BITS: u32 = $gamma1;
            const GAMMA2: i32 = (Q - 1) / $gamma2;
            const OMEGA: usize = $omega;
            const CTILDE_LEN: usize = $lambda / 4;
            type PublicKey = [u8; $pk];
            type SecretKey = [u8; $sk];
            type Signature = [u8; $sig];
        }

        // FIPS 204's table 2, from table 1.
        const _: () = {
            assert!($pk == public_key_len::<$set>());
            assert!($sk == secret_key_len::<$set>());
            assert!($sig == signature_len::<$set>());
        };
    )*};
}

params! {
    MlDsa44: K = 4, L = 4, ETA = 2, TAU = 39, GAMMA1 = 2^17, GAMMA2 = (Q - 1) / 88,
        OMEGA = 80, LAMBDA = 128, pk = 1312, sk = 2560, sig = 2420;
    MlDsa65: K = 6, L = 5, ETA = 4, TAU = 49, GAMMA1 = 2^19, GAMMA2 = (Q - 1) / 32,
        OMEGA = 55, LAMBDA = 192, pk = 1952, sk = 4032, sig = 3309;
    MlDsa87: K = 8, L = 7, ETA = 2, TAU = 60, GAMMA1 = 2^19, GAMMA2 = (Q - 1) / 32,
        OMEGA = 75, LAMBDA = 256, pk = 2592, sk = 4896, sig = 4627;
}

/// The length of a parameter set's public key encoding, which [`verify`]
/// requires.
pub(crate) const fn public_key_len<P: Params>() -> usize {
    SEED_LEN + P::K * T1_PACKED
}

/// The length of a parameter set's expanded private key encoding.
pub(crate) const fn secret_key_len<P: Params>() -> usize {
    2 * SEED_LEN + TR_LEN + (P::K + P::L) * P::ETA_PACKED + P::K * T0_PACKED
}

const fn signature_len<P: Params>() -> usize {
    P::CTILDE_LEN + P::L * P::Z_PACKED + P::OMEGA + P::K
}

/// A key pair: the encodings FIPS 204 defines, and the seed it was generated
/// from, if known. Signing expands them as it goes, as mldsa-native and
/// aws-lc do, which keeps the key small.
///
/// It wipes its whole value on drop under the `wipe` feature.
pub(crate) struct KeyPair<P: Params> {
    seed: Option<[u8; SEED_LEN]>,
    secret_key: P::SecretKey,
    public_key: P::PublicKey,
}

impl<P: Params> KeyPair<P> {
    /// Generates a key pair from the system random source.
    pub(crate) fn generate() -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let mut seed = [0u8; SEED_LEN];
        SystemRandom.fill(&mut seed)?;
        Ok(Self::from_seed(&seed))
    }

    /// FIPS 204's `ML-DSA.KeyGen_internal`: the key pair seed `xi` expands to.
    pub(crate) fn from_seed(seed: &[u8; SEED_LEN]) -> Self {
        let _entry = Entry::new_secret();
        let seed = low::ct::into_secret(*seed);
        let mut key = Self {
            seed: Some(seed),
            secret_key: P::SecretKey::zeroed(),
            public_key: P::PublicKey::zeroed(),
        };
        keygen::<P>(&seed, key.public_key.as_mut(), key.secret_key.as_mut());
        key
    }

    /// Loads the expanded private key `sk`, checking it as mldsa-native's
    /// `mld_sign_pk_from_sk` does: its `s1` and `s2` must be in range, and its
    /// `t0` and `tr` must be those its other parts compute.
    pub(crate) fn from_secret_key(sk: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let mut key = Self {
            seed: None,
            secret_key: P::SecretKey::zeroed(),
            public_key: P::PublicKey::zeroed(),
        };
        if sk.len() != key.secret_key.as_ref().len() {
            return Err(KeyFormatError::WrongLength.into());
        }
        key.secret_key.as_mut().copy_from_slice(sk);
        low::ct::secret_slice(key.secret_key.as_ref());
        match public_key_from_secret::<P>(key.secret_key.as_ref(), key.public_key.as_mut()) {
            true => Ok(key),
            false => Err(KeyFormatError::MlDsaSecretKey.into()),
        }
    }

    /// The seed this key pair was generated from, unless it was loaded from
    /// its expanded form.
    pub(crate) fn seed(&self) -> Option<&[u8; SEED_LEN]> {
        self.seed.as_ref()
    }

    /// FIPS 204's expanded private key encoding.
    pub(crate) fn secret_key(&self) -> &P::SecretKey {
        &self.secret_key
    }

    /// FIPS 204's public key encoding.
    pub(crate) fn public_key(&self) -> &P::PublicKey {
        &self.public_key
    }

    /// `tr`, the public key's hash, which the expanded private key stores.
    pub(crate) fn tr(&self) -> &[u8; TR_LEN] {
        tr_of::<P>(self.secret_key.as_ref())
    }

    /// Signs `message` under context `context` with fresh randomness: FIPS
    /// 204's hedged `ML-DSA.Sign`.
    pub(crate) fn sign(&self, context: &[u8], message: &[u8]) -> Result<P::Signature, Error> {
        let _entry = Entry::new_secret();
        let mu = self.mu(context, message)?;
        let mut rnd = [0u8; RND_LEN];
        SystemRandom.fill(&mut rnd)?;
        low::ct::secret_slice(&rnd);
        sign_internal::<P>(self.secret_key.as_ref(), &mu, &rnd)
    }

    /// `mu`, the message representative this key signs for `message` under
    /// `context`.
    pub(crate) fn mu(&self, context: &[u8], message: &[u8]) -> Result<[u8; MU_LEN], Error> {
        mu(self.tr(), context, message)
    }

    /// The expanded private key, FIPS 204's `sk`.
    #[cfg(feature = "__acvp")]
    pub(crate) fn secret_key_bytes(&self) -> &[u8] {
        self.secret_key.as_ref()
    }

    /// FIPS 204's `ML-DSA.Sign_internal`, for tests, `rind-acvp`, and the
    /// FIPS module's self-test to fix `rnd` and `mu`.
    #[cfg(any(test, feature = "__acvp", rind_fips))]
    pub(crate) fn sign_internal(
        &self,
        mu: &[u8; MU_LEN],
        rnd: &[u8; RND_LEN],
    ) -> Result<P::Signature, Error> {
        let _entry = Entry::new_secret();
        sign_internal::<P>(self.secret_key.as_ref(), mu, rnd)
    }
}

impl<P: Params> Drop for KeyPair<P> {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl<P: Params> low::Zeroable for KeyPair<P> {}

/// `tr`, the hash of public key `pk` that `mu` binds in.
pub(crate) fn tr(pk: &[u8]) -> [u8; TR_LEN] {
    let _entry = Entry::new_public();
    let mut tr = [0u8; TR_LEN];
    let mut h = Shake256Sponge::new();
    h.absorb(pk);
    Shake256::new(&h).read(&mut tr);
    tr
}

/// The `tr` stored in expanded private key `sk`.
fn tr_of<P: Params>(sk: &[u8]) -> &[u8; TR_LEN] {
    sk[2 * SEED_LEN..2 * SEED_LEN + TR_LEN].try_into().unwrap()
}

/// `mu = H(tr || message)`, FIPS 204's internal interface, which binds no
/// context.
#[cfg(feature = "__acvp")]
pub(crate) fn mu_internal(tr: &[u8; TR_LEN], message: &[u8]) -> [u8; MU_LEN] {
    let mut mu = [0u8; MU_LEN];
    let mut h = Shake256Sponge::new();
    h.absorb(tr);
    h.absorb(message);
    Shake256::new(&h).read(&mut mu);
    mu
}

/// Verifies `signature` over an already computed `mu`.
#[cfg(feature = "__acvp")]
pub(crate) fn verify_mu<P: Params>(
    pk: &[u8],
    mu: &[u8; MU_LEN],
    signature: &[u8],
) -> Result<(), Error> {
    let _entry = Entry::new_public();
    verify_internal::<P>(pk, mu, signature)
}

/// `mu = H(tr || 0 || len(context) || context || message)`, pure ML-DSA's
/// message representative. A context is at most 255 bytes.
pub(crate) fn mu(tr: &[u8; TR_LEN], context: &[u8], message: &[u8]) -> Result<[u8; MU_LEN], Error> {
    let context_len = u8::try_from(context.len()).map_err(|_| Error::WrongLength)?;
    let mut mu = [0u8; MU_LEN];
    let mut h = Shake256Sponge::new();
    h.absorb(tr);
    h.absorb(&[0, context_len]);
    h.absorb(context);
    h.absorb(message);
    Shake256::new(&h).read(&mut mu);
    Ok(mu)
}

/// Verifies `signature` over `message` and `context` under public key `pk`,
/// whose hash is `tr`.
pub(crate) fn verify<P: Params>(
    pk: &[u8],
    tr: &[u8; TR_LEN],
    context: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<(), Error> {
    let _entry = Entry::new_public();
    let mu = mu(tr, context, message).map_err(|_| Error::BadSignature)?;
    verify_internal::<P>(pk, &mu, signature)
}

/// Polynomials on the heap, wiped before they are freed under the `wipe`
/// feature, as heap scratch derived from a private key must be.
struct Scratch(Vec<Poly>);

impl Scratch {
    fn new(polys: usize) -> Self {
        Self(vec![Poly::ZERO; polys])
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        low::zeroise(&mut self.0);
    }
}

/// FIPS 204's `ML-DSA.KeyGen_internal`, writing `pk` and `sk`.
fn keygen<P: Params>(seed: &[u8; SEED_LEN], pk: &mut [u8], sk: &mut [u8]) {
    let mut expanded = [0u8; 2 * SEED_LEN + 64];
    let mut h = Shake256Sponge::new();
    h.absorb(seed);
    h.absorb(&[P::K as u8, P::L as u8]);
    Shake256::new(&h).read(&mut expanded);
    let (rho, rest) = expanded.split_at(SEED_LEN);
    let (rho_prime, key) = rest.split_at(64);
    let rho: &[u8; SEED_LEN] = rho.try_into().unwrap();
    low::ct::public_slice(rho);

    let mut scratch = Scratch::new(P::K * P::L + P::L + P::K);
    let (a, s) = scratch.0.split_at_mut(P::K * P::L);
    expand_s::<P>(rho_prime.try_into().unwrap(), s);
    let (s1, s2) = s.split_at_mut(P::L);

    let layout = SecretKeyLayout::<P>::new();
    for (s, packed) in s1
        .iter()
        .chain(s2.iter())
        .zip(sk[layout.s1.start..layout.s2.end].chunks_exact_mut(P::ETA_PACKED))
    {
        pack_eta::<P>(packed, s);
    }
    for s in s1.iter_mut() {
        low::mldsa_ntt(&mut s.0);
    }

    pk[..SEED_LEN].copy_from_slice(rho);
    expand_a::<P>(rho, a);
    compute_t::<P>(a, s1, s2, &mut pk[SEED_LEN..], &mut sk[layout.t0]);
    low::ct::public_slice(pk);

    sk[..SEED_LEN].copy_from_slice(rho);
    sk[SEED_LEN..2 * SEED_LEN].copy_from_slice(key);
    let mut h = Shake256Sponge::new();
    h.absorb(pk);
    Shake256::new(&h).read(&mut sk[layout.tr]);
}

/// Where an expanded private key's parts lie.
struct SecretKeyLayout<P> {
    tr: core::ops::Range<usize>,
    s1: core::ops::Range<usize>,
    s2: core::ops::Range<usize>,
    t0: core::ops::Range<usize>,
    _params: core::marker::PhantomData<P>,
}

impl<P: Params> SecretKeyLayout<P> {
    fn new() -> Self {
        let tr = 2 * SEED_LEN..2 * SEED_LEN + TR_LEN;
        let s1 = tr.end..tr.end + P::L * P::ETA_PACKED;
        let s2 = s1.end..s1.end + P::K * P::ETA_PACKED;
        let t0 = s2.end..s2.end + P::K * T0_PACKED;
        Self {
            tr,
            s1,
            s2,
            t0,
            _params: core::marker::PhantomData,
        }
    }
}

/// `t = A * s1 + s2`, split into `t1`, packed into `t1_packed`, and `t0`,
/// packed into `t0_packed`, for `s1` in the NTT domain.
fn compute_t<P: Params>(
    a: &[Poly],
    s1_hat: &[Poly],
    s2: &[Poly],
    t1_packed: &mut [u8],
    t0_packed: &mut [u8],
) {
    let mut t = Poly::ZERO;
    for (((row, s2), t1_packed), t0_packed) in a
        .chunks_exact(P::L)
        .zip(s2)
        .zip(t1_packed.as_chunks_mut::<T1_PACKED>().0)
        .zip(t0_packed.as_chunks_mut::<T0_PACKED>().0)
    {
        low::mldsa_pointwise_acc(&mut t.0, row, s1_hat);
        low::mldsa_intt(&mut t.0);
        add(&mut t, s2);
        low::mldsa_reduce(&mut t.0);
        low::mldsa_caddq(&mut t.0);

        // Power2Round: t = t1 * 2^d + t0, with -2^(d-1) < t0 <= 2^(d-1).
        let mut t1 = Poly::ZERO;
        for (t, t1) in t.0.iter_mut().zip(t1.0.iter_mut()) {
            *t1 = t.wrapping_add((1 << (D - 1)) - 1) >> D;
            *t = t.wrapping_sub(*t1 << D);
        }
        pack_t1(t1_packed, &t1);
        pack_t0(t0_packed, &t);
    }
}

/// mldsa-native's `mld_sign_pk_from_sk`: writes the public key expanded
/// private key `sk` computes into `pk`, returning whether `sk` is
/// consistent. Its time does not depend on `sk`.
fn public_key_from_secret<P: Params>(sk: &[u8], pk: &mut [u8]) -> bool {
    let layout = SecretKeyLayout::<P>::new();
    let rho: &[u8; SEED_LEN] = sk[..SEED_LEN].try_into().unwrap();
    low::ct::public_slice(rho);

    let mut scratch = Scratch::new(P::K * P::L + P::L + P::K);
    let (a, rest) = scratch.0.split_at_mut(P::K * P::L);
    let (s1, s2) = rest.split_at_mut(P::L);
    let mut out_of_range = 0;
    for (s, packed) in s1
        .iter_mut()
        .chain(s2.iter_mut())
        .zip(sk[layout.s1.start..layout.s2.end].chunks_exact(P::ETA_PACKED))
    {
        unpack_eta::<P>(s, packed);
        out_of_range |= low::mldsa_chknorm(&s.0, (P::ETA + 1) as u64);
    }
    for s in s1.iter_mut() {
        low::mldsa_ntt(&mut s.0);
    }

    pk[..SEED_LEN].copy_from_slice(rho);
    expand_a::<P>(rho, a);
    let mut t0 = vec![0u8; P::K * T0_PACKED];
    compute_t::<P>(a, s1, s2, &mut pk[SEED_LEN..], &mut t0);
    let t0_matches = low::ct_equal(&t0, &sk[layout.t0]);
    low::zeroise(&mut t0);

    let mut tr = [0u8; TR_LEN];
    let mut h = Shake256Sponge::new();
    h.absorb(pk);
    Shake256::new(&h).read(&mut tr);
    let tr_matches = low::ct_equal(&tr, &sk[layout.tr]);
    low::ct::public_slice(pk);

    // `&`, not `&&`, which would branch on each before declassifying.
    low::ct::into_public((out_of_range == 0) & t0_matches & tr_matches)
}

/// FIPS 204's `ML-DSA.Sign_internal`: signs `mu` with expanded private key
/// `sk` and randomness `rnd`.
fn sign_internal<P: Params>(
    sk: &[u8],
    mu: &[u8; MU_LEN],
    rnd: &[u8; RND_LEN],
) -> Result<P::Signature, Error> {
    let layout = SecretKeyLayout::<P>::new();
    let rho: &[u8; SEED_LEN] = sk[..SEED_LEN].try_into().unwrap();
    low::ct::public_slice(rho);
    let key = &sk[SEED_LEN..2 * SEED_LEN];

    let (k, l) = (P::K, P::L);
    let mut scratch = Scratch::new(k * l + 3 * l + 4 * k);
    let (a, rest) = scratch.0.split_at_mut(k * l);
    let (s1, rest) = rest.split_at_mut(l);
    let (s2, rest) = rest.split_at_mut(k);
    let (t0, rest) = rest.split_at_mut(k);
    let (y, rest) = rest.split_at_mut(l);
    let (y_hat, rest) = rest.split_at_mut(l);
    let (w0, w1) = rest.split_at_mut(k);

    for (s, packed) in s1
        .iter_mut()
        .chain(s2.iter_mut())
        .zip(sk[layout.s1.start..layout.s2.end].chunks_exact(P::ETA_PACKED))
    {
        unpack_eta::<P>(s, packed);
        low::mldsa_ntt(&mut s.0);
    }
    for (t, packed) in t0.iter_mut().zip(sk[layout.t0].as_chunks::<T0_PACKED>().0) {
        unpack_t0(t, packed);
        low::mldsa_ntt(&mut t.0);
    }

    let mut rho_prime = [0u8; 64];
    let mut h = Shake256Sponge::new();
    h.absorb(key);
    h.absorb(rnd);
    h.absorb(mu);
    Shake256::new(&h).read(&mut rho_prime);
    expand_a::<P>(rho, a);

    let mut signature = P::Signature::zeroed();
    let mut w1_packed = [0u8; 8 * 192];
    let w1_packed = &mut w1_packed[..k * P::W1_PACKED];
    let mut c_tilde = [0u8; 64];
    let c_tilde = &mut c_tilde[..P::CTILDE_LEN];
    let (mut c, mut tmp) = (Poly::ZERO, Poly::ZERO);

    let mut accepted = false;
    'attempts: for kappa in (0..=MAX_KAPPA - l).step_by(l) {
        expand_mask::<P>(&rho_prime, kappa as u16, y);
        y_hat.copy_from_slice(y);
        for y in y_hat.iter_mut() {
            low::mldsa_ntt(&mut y.0);
        }

        // w = A * y, split into high bits w1 and low bits w0.
        for ((row, w0), w1) in a.chunks_exact(l).zip(w0.iter_mut()).zip(w1.iter_mut()) {
            low::mldsa_pointwise_acc(&mut w0.0, row, y_hat);
            low::mldsa_intt(&mut w0.0);
            low::mldsa_caddq(&mut w0.0);
            decompose::<P>(w1, w0);
        }
        for (w1, packed) in w1.iter().zip(w1_packed.chunks_exact_mut(P::W1_PACKED)) {
            pack_w1::<P>(packed, w1);
        }

        let mut h = Shake256Sponge::new();
        h.absorb(mu);
        h.absorb(w1_packed);
        Shake256::new(&h).read(c_tilde);
        low::ct::public_slice(c_tilde);
        sample_in_ball::<P>(&mut c, c_tilde);
        low::mldsa_ntt(&mut c.0);

        // z = y + c * s1
        let z_packed = &mut signature.as_mut()[P::CTILDE_LEN..P::CTILDE_LEN + l * P::Z_PACKED];
        for ((s1, y), packed) in s1
            .iter()
            .zip(y.iter())
            .zip(z_packed.chunks_exact_mut(P::Z_PACKED))
        {
            low::mldsa_pointwise(&mut tmp.0, &c.0, &s1.0);
            low::mldsa_intt(&mut tmp.0);
            add(&mut tmp, y);
            low::mldsa_reduce(&mut tmp.0);
            if rejected(low::mldsa_chknorm(&tmp.0, (P::GAMMA1 - P::BETA) as u64)) {
                continue 'attempts;
            }
            pack_z::<P>(packed, &tmp);
        }

        // r0 = w0 - c * s2, then w0 - c * s2 + c * t0 for the hints.
        for ((s2, t0), w0) in s2.iter().zip(t0.iter()).zip(w0.iter_mut()) {
            low::mldsa_pointwise(&mut tmp.0, &c.0, &s2.0);
            low::mldsa_intt(&mut tmp.0);
            sub(w0, &tmp);
            low::mldsa_reduce(&mut w0.0);
            if rejected(low::mldsa_chknorm(&w0.0, (P::GAMMA2 - P::BETA) as u64)) {
                continue 'attempts;
            }

            low::mldsa_pointwise(&mut tmp.0, &c.0, &t0.0);
            low::mldsa_intt(&mut tmp.0);
            low::mldsa_reduce(&mut tmp.0);
            if rejected(low::mldsa_chknorm(&tmp.0, P::GAMMA2 as u64)) {
                continue 'attempts;
            }
            add(w0, &tmp);
        }

        low::ct::public_slice(w0);
        low::ct::public_slice(w1);
        if !pack_hints::<P>(signature.as_mut(), w0, w1) {
            continue 'attempts;
        }

        signature.as_mut()[..P::CTILDE_LEN].copy_from_slice(c_tilde);
        low::ct::public_slice(signature.as_ref());
        accepted = true;
        break;
    }

    // FIPS 204 expects about five attempts at most; this many fail with
    // negligible probability.
    match accepted {
        true => Ok(signature),
        false => Err(Error::Fault),
    }
}

/// Declassifies a rejection test, as FIPS 204's security argument allows.
fn rejected(check: u64) -> bool {
    low::ct::into_public(check) != 0
}

/// FIPS 204's `ML-DSA.Verify_internal`: verifies `signature` over `mu` under
/// public key `pk`.
fn verify_internal<P: Params>(pk: &[u8], mu: &[u8; MU_LEN], signature: &[u8]) -> Result<(), Error> {
    if pk.len() != public_key_len::<P>() || signature.len() != signature_len::<P>() {
        return Err(Error::BadSignature);
    }
    let (k, l) = (P::K, P::L);
    let (c_tilde, rest) = signature.split_at(P::CTILDE_LEN);
    let (z_packed, hints) = rest.split_at(l * P::Z_PACKED);

    let mut polys = vec![Poly::ZERO; k * l + l];
    let (a, z) = polys.split_at_mut(k * l);
    // Verification slices by index: zipping `chunks_exact` with a run-time
    // size divides to count the chunks, which `admin/ct-vartime` refuses
    // wherever the compiler leaves `Zip::new` outlined.
    for (i, z) in z.iter_mut().enumerate() {
        unpack_z::<P>(z, &z_packed[i * P::Z_PACKED..(i + 1) * P::Z_PACKED]);
        if low::mldsa_chknorm(&z.0, (P::GAMMA1 - P::BETA) as u64) != 0 {
            return Err(Error::BadSignature);
        }
        low::mldsa_ntt(&mut z.0);
    }

    expand_a::<P>(pk[..SEED_LEN].try_into().unwrap(), a);
    let mut c = Poly::ZERO;
    sample_in_ball::<P>(&mut c, c_tilde);
    low::mldsa_ntt(&mut c.0);

    // w1' = UseHint(h, A * z - c * t1 * 2^d)
    let mut w1_packed = [0u8; 8 * 192];
    let w1_packed = &mut w1_packed[..k * P::W1_PACKED];
    let (mut w1, mut t1, mut h) = (Poly::ZERO, Poly::ZERO, Poly::ZERO);
    for (i, t1_packed) in pk[SEED_LEN..].as_chunks::<T1_PACKED>().0.iter().enumerate() {
        let row = &a[i * l..(i + 1) * l];
        let packed = &mut w1_packed[i * P::W1_PACKED..(i + 1) * P::W1_PACKED];
        low::mldsa_pointwise_acc(&mut w1.0, row, z);
        unpack_t1(&mut t1, t1_packed);
        for t in t1.0.iter_mut() {
            *t <<= D;
        }
        low::mldsa_ntt(&mut t1.0);
        let t1_hat = t1;
        low::mldsa_pointwise(&mut t1.0, &t1_hat.0, &c.0);
        sub(&mut w1, &t1);
        low::mldsa_reduce(&mut w1.0);
        low::mldsa_intt(&mut w1.0);
        low::mldsa_caddq(&mut w1.0);
        if !unpack_hints::<P>(&mut h, hints, i) {
            return Err(Error::BadSignature);
        }
        use_hint::<P>(&mut w1, &h);
        pack_w1::<P>(packed, &w1);
    }

    let mut c_tilde_prime = [0u8; 64];
    let c_tilde_prime = &mut c_tilde_prime[..P::CTILDE_LEN];
    let mut h = Shake256Sponge::new();
    h.absorb(mu);
    h.absorb(w1_packed);
    Shake256::new(&h).read(c_tilde_prime);
    match low::ct_equal(c_tilde, c_tilde_prime) {
        true => Ok(()),
        false => Err(Error::BadSignature),
    }
}

fn add(a: &mut Poly, b: &Poly) {
    for (a, b) in a.0.iter_mut().zip(b.0.iter()) {
        *a = a.wrapping_add(*b);
    }
}

fn sub(a: &mut Poly, b: &Poly) {
    for (a, b) in a.0.iter_mut().zip(b.0.iter()) {
        *a = a.wrapping_sub(*b);
    }
}

fn decompose<P: Params>(a1: &mut Poly, a0: &mut Poly) {
    match P::GAMMA2 == (Q - 1) / 88 {
        true => low::mldsa_decompose_88(&mut a1.0, &mut a0.0),
        false => low::mldsa_decompose_32(&mut a1.0, &mut a0.0),
    }
}

fn use_hint<P: Params>(a: &mut Poly, h: &Poly) {
    match P::GAMMA2 == (Q - 1) / 88 {
        true => low::mldsa_poly_use_hint_88(&mut a.0, &h.0),
        false => low::mldsa_poly_use_hint_32(&mut a.0, &h.0),
    }
}

/// Packs the hints that move `w1` to the high bits of `w0 + w1 * 2 * gamma2`,
/// returning false if there are more than `omega`. Its inputs are public.
fn pack_hints<P: Params>(signature: &mut [u8], w0: &[Poly], w1: &[Poly]) -> bool {
    let hints = &mut signature[signature_len::<P>() - P::OMEGA - P::K..];
    hints.fill(0);
    let mut n = 0;
    for (k, (w0, w1)) in w0.iter().zip(w1.iter()).enumerate() {
        for (j, (a0, a1)) in w0.0.iter().zip(w1.0.iter()).enumerate() {
            let hint = *a0 > P::GAMMA2 || *a0 < -P::GAMMA2 || (*a0 == -P::GAMMA2 && *a1 != 0);
            if hint {
                if n == P::OMEGA {
                    return false;
                }
                hints[n] = j as u8;
                n += 1;
            }
        }
        hints[P::OMEGA + k] = n as u8;
    }
    true
}

/// Unpacks the `i`th polynomial's hints into `h`, returning false for an
/// encoding FIPS 204's `HintBitUnpack` refuses: counts that fall or pass
/// `omega`, indices not strictly increasing, or nonzero padding.
fn unpack_hints<P: Params>(h: &mut Poly, hints: &[u8], i: usize) -> bool {
    let old = match i {
        0 => 0,
        _ => hints[P::OMEGA + i - 1] as usize,
    };
    let new = hints[P::OMEGA + i] as usize;
    if new < old || new > P::OMEGA {
        return false;
    }
    h.0 = [0; N];
    for j in old..new {
        if j > old && hints[j] <= hints[j - 1] {
            return false;
        }
        h.0[hints[j] as usize] = 1;
    }
    i != P::K - 1 || hints[new..P::OMEGA].iter().all(|b| *b == 0)
}

/// ExpandA: the matrix `A` in the NTT domain, row by row, in the backend's
/// coefficient order.
fn expand_a<P: Params>(rho: &[u8; SEED_LEN], a: &mut [Poly]) {
    const FIRST: usize = 5 * SHAKE_128_R_BYTES;
    for (batch, polys) in a.chunks_mut(4).enumerate() {
        let mut seeds = [[0u8; SEED_LEN + 2]; 4];
        for (n, seed) in seeds.iter_mut().enumerate() {
            let index = (batch * 4 + n).min(P::K * P::L - 1);
            seed[..SEED_LEN].copy_from_slice(rho);
            seed[SEED_LEN] = (index % P::L) as u8;
            seed[SEED_LEN + 1] = (index / P::L) as u8;
        }
        let mut xof = Shake128x4::new(&seeds[..polys.len()]);
        let mut buf = [[0u8; FIRST]; 4];
        xof.squeeze(&mut buf);
        let mut filled = [0; 4];
        for ((poly, buf), filled) in polys.iter_mut().zip(&buf).zip(&mut filled) {
            *filled = low::mldsa_rej_uniform_vartime(&mut poly.0, 0, buf);
        }
        while filled[..polys.len()].iter().any(|f| *f < N) {
            let mut block = [[0u8; SHAKE_128_R_BYTES]; 4];
            xof.squeeze(&mut block);
            for ((poly, block), filled) in polys.iter_mut().zip(&block).zip(&mut filled) {
                *filled = low::mldsa_rej_uniform_vartime(&mut poly.0, *filled, block);
            }
        }
        for poly in polys {
            low::mldsa_nttunpack(&mut poly.0);
        }
    }
}

/// ExpandS: the secret vectors `s1` and `s2`, in that order in `s`, from
/// `rho_prime`.
fn expand_s<P: Params>(rho_prime: &[u8; 64], s: &mut [Poly]) {
    // One block for eta = 2 and two for eta = 4 fill a polynomial with
    // overwhelming probability, as mldsa-native's AVX2 and Neon routines
    // expect.
    const BLOCK: usize = SHAKE_256_R_BYTES;
    let first = if P::ETA == 2 { BLOCK } else { 2 * BLOCK };
    let sample = |poly: &mut Poly, offset: usize, buf: &[u8]| match P::ETA {
        2 => low::mldsa_rej_uniform_eta2_vartime(&mut poly.0, offset, buf),
        _ => low::mldsa_rej_uniform_eta4_vartime(&mut poly.0, offset, buf),
    };

    for (batch, polys) in s.chunks_mut(4).enumerate() {
        let mut seeds = [[0u8; 66]; 4];
        for (n, seed) in seeds.iter_mut().enumerate() {
            seed[..64].copy_from_slice(rho_prime);
            seed[64..].copy_from_slice(&((batch * 4 + n) as u16).to_le_bytes());
        }
        let mut xof = Shake256x4::new(&seeds[..polys.len()]);
        let mut buf = [[0u8; 2 * BLOCK]; 4];
        xof.squeeze(&mut buf);
        let mut filled = [0; 4];
        for ((poly, buf), filled) in polys.iter_mut().zip(&buf).zip(&mut filled) {
            *filled = sample(poly, 0, &buf[..first]);
        }
        // An eta = 2 polynomial continues from the second block squeezed.
        let mut extra = (P::ETA == 2).then_some(1);
        while filled[..polys.len()].iter().any(|f| *f < N) {
            let mut block = [[0u8; BLOCK]; 4];
            match extra.take() {
                Some(_) => {
                    for (block, buf) in block.iter_mut().zip(&buf) {
                        block.copy_from_slice(&buf[BLOCK..]);
                    }
                }
                None => xof.squeeze(&mut block),
            }
            for ((poly, block), filled) in polys.iter_mut().zip(&block).zip(&mut filled) {
                if *filled < N {
                    *filled = sample(poly, *filled, block);
                }
            }
        }
    }
}

/// ExpandMask: the mask `y` for attempt `kappa`, the first nonce.
fn expand_mask<P: Params>(rho_prime: &[u8; 64], kappa: u16, y: &mut [Poly]) {
    const BYTES: usize = 5 * SHAKE_256_R_BYTES;
    for (batch, polys) in y.chunks_mut(4).enumerate() {
        let mut seeds = [[0u8; 66]; 4];
        for (n, seed) in seeds.iter_mut().enumerate() {
            seed[..64].copy_from_slice(rho_prime);
            let nonce = kappa.wrapping_add((batch * 4 + n) as u16);
            seed[64..].copy_from_slice(&nonce.to_le_bytes());
        }
        let mut buf = [[0u8; BYTES]; 4];
        Shake256x4::new(&seeds[..polys.len()]).squeeze(&mut buf);
        for (poly, buf) in polys.iter_mut().zip(&buf) {
            unpack_z::<P>(poly, &buf[..P::Z_PACKED]);
        }
    }
}

/// SampleInBall: the challenge `c`, with `tau` coefficients of 1 or -1, from
/// public `c_tilde`.
fn sample_in_ball<P: Params>(c: &mut Poly, c_tilde: &[u8]) {
    let mut h = Shake256Sponge::new();
    h.absorb(c_tilde);
    let mut xof = Shake256::new(&h);
    let mut signs = [0u8; 8];
    xof.read(&mut signs);
    let mut signs = u64::from_le_bytes(signs);
    c.0 = [0; N];
    for i in N - P::TAU..N {
        let j = loop {
            let mut j = [0u8];
            xof.read(&mut j);
            if j[0] as usize <= i {
                break j[0] as usize;
            }
        };
        c.0[i] = c.0[j];
        c.0[j] = 1 - 2 * (signs & 1) as i32;
        signs >>= 1;
    }
}

fn pack_t1(r: &mut [u8; T1_PACKED], a: &Poly) {
    for (r, a) in r
        .as_chunks_mut::<5>()
        .0
        .iter_mut()
        .zip(a.0.as_chunks::<4>().0)
    {
        r[0] = a[0] as u8;
        r[1] = ((a[0] >> 8) | (a[1] << 2)) as u8;
        r[2] = ((a[1] >> 6) | (a[2] << 4)) as u8;
        r[3] = ((a[2] >> 4) | (a[3] << 6)) as u8;
        r[4] = (a[3] >> 2) as u8;
    }
}

fn unpack_t1(r: &mut Poly, a: &[u8; T1_PACKED]) {
    for (r, a) in
        r.0.as_chunks_mut::<4>()
            .0
            .iter_mut()
            .zip(a.as_chunks::<5>().0)
    {
        let a = a.map(i32::from);
        r[0] = (a[0] | (a[1] << 8)) & 0x3ff;
        r[1] = ((a[1] >> 2) | (a[2] << 6)) & 0x3ff;
        r[2] = ((a[2] >> 4) | (a[3] << 4)) & 0x3ff;
        r[3] = ((a[3] >> 6) | (a[4] << 2)) & 0x3ff;
    }
}

fn pack_t0(r: &mut [u8; T0_PACKED], a: &Poly) {
    for (r, a) in r
        .as_chunks_mut::<13>()
        .0
        .iter_mut()
        .zip(a.0.as_chunks::<8>().0)
    {
        let t = a.map(|a| (1i32 << (D - 1)).wrapping_sub(a) as u32);
        r[0] = t[0] as u8;
        r[1] = ((t[0] >> 8) | (t[1] << 5)) as u8;
        r[2] = (t[1] >> 3) as u8;
        r[3] = ((t[1] >> 11) | (t[2] << 2)) as u8;
        r[4] = ((t[2] >> 6) | (t[3] << 7)) as u8;
        r[5] = (t[3] >> 1) as u8;
        r[6] = ((t[3] >> 9) | (t[4] << 4)) as u8;
        r[7] = (t[4] >> 4) as u8;
        r[8] = ((t[4] >> 12) | (t[5] << 1)) as u8;
        r[9] = ((t[5] >> 7) | (t[6] << 6)) as u8;
        r[10] = (t[6] >> 2) as u8;
        r[11] = ((t[6] >> 10) | (t[7] << 3)) as u8;
        r[12] = (t[7] >> 5) as u8;
    }
}

fn unpack_t0(r: &mut Poly, a: &[u8; T0_PACKED]) {
    for (r, a) in
        r.0.as_chunks_mut::<8>()
            .0
            .iter_mut()
            .zip(a.as_chunks::<13>().0)
    {
        let a = a.map(i32::from);
        r[0] = a[0] | (a[1] << 8);
        r[1] = (a[1] >> 5) | (a[2] << 3) | (a[3] << 11);
        r[2] = (a[3] >> 2) | (a[4] << 6);
        r[3] = (a[4] >> 7) | (a[5] << 1) | (a[6] << 9);
        r[4] = (a[6] >> 4) | (a[7] << 4) | (a[8] << 12);
        r[5] = (a[8] >> 1) | (a[9] << 7);
        r[6] = (a[9] >> 6) | (a[10] << 2) | (a[11] << 10);
        r[7] = (a[11] >> 3) | (a[12] << 5);
        for r in r.iter_mut() {
            *r = (1i32 << (D - 1)).wrapping_sub(*r & 0x1fff);
        }
    }
}

fn pack_eta<P: Params>(r: &mut [u8], a: &Poly) {
    match P::ETA {
        2 => {
            for (r, a) in r
                .as_chunks_mut::<3>()
                .0
                .iter_mut()
                .zip(a.0.as_chunks::<8>().0)
            {
                let t = a.map(|a| 2i32.wrapping_sub(a) as u8);
                r[0] = t[0] | (t[1] << 3) | (t[2] << 6);
                r[1] = (t[2] >> 2) | (t[3] << 1) | (t[4] << 4) | (t[5] << 7);
                r[2] = (t[5] >> 1) | (t[6] << 2) | (t[7] << 5);
            }
        }
        _ => {
            for (r, a) in r.iter_mut().zip(a.0.as_chunks::<2>().0) {
                *r = 4i32.wrapping_sub(a[0]) as u8 | ((4i32.wrapping_sub(a[1]) as u8) << 4);
            }
        }
    }
}

/// Unpacks `eta`-bounded coefficients. An out-of-range field unpacks to a
/// coefficient outside `[-eta, eta]`, which callers check for.
fn unpack_eta<P: Params>(r: &mut Poly, a: &[u8]) {
    match P::ETA {
        2 => {
            for (r, a) in
                r.0.as_chunks_mut::<8>()
                    .0
                    .iter_mut()
                    .zip(a.as_chunks::<3>().0)
            {
                let a = a.map(i32::from);
                r[0] = a[0] & 7;
                r[1] = (a[0] >> 3) & 7;
                r[2] = ((a[0] >> 6) | (a[1] << 2)) & 7;
                r[3] = (a[1] >> 1) & 7;
                r[4] = (a[1] >> 4) & 7;
                r[5] = ((a[1] >> 7) | (a[2] << 1)) & 7;
                r[6] = (a[2] >> 2) & 7;
                r[7] = (a[2] >> 5) & 7;
                for r in r.iter_mut() {
                    *r = 2i32.wrapping_sub(*r);
                }
            }
        }
        _ => {
            for (r, a) in r.0.as_chunks_mut::<2>().0.iter_mut().zip(a) {
                r[0] = 4i32.wrapping_sub((*a & 0x0f) as i32);
                r[1] = 4i32.wrapping_sub((*a >> 4) as i32);
            }
        }
    }
}

fn pack_z<P: Params>(r: &mut [u8], a: &Poly) {
    match P::GAMMA1_BITS {
        17 => {
            for (r, a) in r
                .as_chunks_mut::<9>()
                .0
                .iter_mut()
                .zip(a.0.as_chunks::<4>().0)
            {
                let t = a.map(|a| P::GAMMA1.wrapping_sub(a) as u32);
                r[0] = t[0] as u8;
                r[1] = (t[0] >> 8) as u8;
                r[2] = ((t[0] >> 16) | (t[1] << 2)) as u8;
                r[3] = (t[1] >> 6) as u8;
                r[4] = ((t[1] >> 14) | (t[2] << 4)) as u8;
                r[5] = (t[2] >> 4) as u8;
                r[6] = ((t[2] >> 12) | (t[3] << 6)) as u8;
                r[7] = (t[3] >> 2) as u8;
                r[8] = (t[3] >> 10) as u8;
            }
        }
        _ => {
            for (r, a) in r
                .as_chunks_mut::<5>()
                .0
                .iter_mut()
                .zip(a.0.as_chunks::<2>().0)
            {
                let t = a.map(|a| P::GAMMA1.wrapping_sub(a) as u32);
                r[0] = t[0] as u8;
                r[1] = (t[0] >> 8) as u8;
                r[2] = ((t[0] >> 16) | (t[1] << 4)) as u8;
                r[3] = (t[1] >> 4) as u8;
                r[4] = (t[1] >> 12) as u8;
            }
        }
    }
}

fn unpack_z<P: Params>(r: &mut Poly, a: &[u8]) {
    match P::GAMMA1_BITS {
        17 => low::mldsa_polyz_unpack_17(&mut r.0, a.try_into().unwrap()),
        _ => low::mldsa_polyz_unpack_19(&mut r.0, a.try_into().unwrap()),
    }
}

fn pack_w1<P: Params>(r: &mut [u8], a: &Poly) {
    match P::W1_PACKED {
        192 => {
            for (r, a) in r
                .as_chunks_mut::<3>()
                .0
                .iter_mut()
                .zip(a.0.as_chunks::<4>().0)
            {
                r[0] = (a[0] | (a[1] << 6)) as u8;
                r[1] = ((a[1] >> 2) | (a[2] << 4)) as u8;
                r[2] = ((a[2] >> 4) | (a[3] << 2)) as u8;
            }
        }
        _ => {
            for (r, a) in r.iter_mut().zip(a.0.as_chunks::<2>().0) {
                *r = (a[0] | (a[1] << 4)) as u8;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test::{Acvp, Expected, acvp, wycheproof_groups};

    /// Runs `$f::<P>($args)` for the parameter set ACVP names `$set`.
    macro_rules! by_set {
        ($set:expr, $f:ident($($arg:expr),*)) => {
            match $set {
                "ML-DSA-44" => $f::<MlDsa44>($($arg),*),
                "ML-DSA-65" => $f::<MlDsa65>($($arg),*),
                "ML-DSA-87" => $f::<MlDsa87>($($arg),*),
                other => panic!("unexpected parameter set {other}"),
            }
        };
    }

    /// The `mu` a test's group signs or verifies: given, of a message under
    /// the internal interface, or of a message and context under the
    /// external one.
    fn acvp_mu(
        group: &serde_json::Value,
        test: &serde_json::Value,
        tr: &[u8; TR_LEN],
    ) -> [u8; MU_LEN] {
        if group.flag("externalMu") {
            return test.hex("mu").try_into().unwrap();
        }
        match group.str("signatureInterface") {
            "internal" => {
                let mut mu = [0u8; MU_LEN];
                let mut h = Shake256Sponge::new();
                h.absorb(tr);
                h.absorb(&test.hex("message"));
                Shake256::new(&h).read(&mut mu);
                mu
            }
            "external" => mu(tr, &test.hex("context"), &test.hex("message")).unwrap(),
            other => panic!("unexpected interface {other}"),
        }
    }

    #[test]
    fn acvp_key_gen() {
        fn check<P: Params>(test: &serde_json::Value) {
            let key = KeyPair::<P>::from_seed(&test.hex("seed").try_into().unwrap());
            assert_eq!(
                key.public_key().as_ref(),
                test.hex("pk"),
                "tcId {}",
                test.int("tcId")
            );
            assert_eq!(
                low::ct::into_public(key.secret_key().clone()).as_ref(),
                test.hex("sk"),
                "tcId {}",
                test.int("tcId")
            );

            let loaded = KeyPair::<P>::from_secret_key(&test.hex("sk")).unwrap();
            assert_eq!(loaded.public_key().as_ref(), test.hex("pk"));
            assert!(loaded.seed().is_none());
        }
        for group in acvp("ML-DSA-keyGen-FIPS204") {
            for test in group.tests() {
                by_set!(group.str("parameterSet"), check(test));
            }
        }
    }

    #[test]
    fn acvp_sig_gen() {
        fn check<P: Params>(group: &serde_json::Value, test: &serde_json::Value) {
            let key = KeyPair::<P>::from_secret_key(&test.hex("sk")).unwrap();
            assert_eq!(key.public_key().as_ref(), test.hex("pk"));
            let rnd = match group.flag("deterministic") {
                true => [0; RND_LEN],
                false => test.hex("rnd").try_into().unwrap(),
            };
            let mu = acvp_mu(group, test, key.tr());
            let signature = key.sign_internal(&mu, &rnd).unwrap();
            assert_eq!(
                signature.as_ref(),
                test.hex("signature"),
                "tcId {}",
                test.int("tcId")
            );
        }
        for group in acvp("ML-DSA-sigGen-FIPS204") {
            for test in group.tests() {
                by_set!(group.str("parameterSet"), check(&group, test));
            }
        }
    }

    #[test]
    fn acvp_sig_ver() {
        fn check<P: Params>(group: &serde_json::Value, test: &serde_json::Value) {
            let pk = test.hex("pk");
            let mu = acvp_mu(group, test, &tr(&pk));
            let _entry = Entry::new_public();
            assert_eq!(
                verify_internal::<P>(&pk, &mu, &test.hex("signature")).is_ok(),
                test.flag("testPassed"),
                "tcId {}: {}",
                test.int("tcId"),
                test.str("reason"),
            );
        }
        for group in acvp("ML-DSA-sigVer-FIPS204") {
            for test in group.tests() {
                by_set!(group.str("parameterSet"), check(&group, test));
            }
        }
    }

    // The context and `mu` vectors need crate access, so these live here
    // rather than in `tests/wycheproof.rs`.
    #[derive(serde::Deserialize)]
    struct WycheproofGroup {
        #[serde(default, rename = "privateSeed", with = "hex::serde")]
        seed: Vec<u8>,
        #[serde(default, rename = "privateKey", with = "hex::serde")]
        private_key: Vec<u8>,
        // Hex, or null for a group whose private key is invalid.
        #[serde(rename = "publicKey")]
        public_key: Option<String>,
        tests: Vec<WycheproofTest>,
    }

    #[derive(serde::Deserialize)]
    struct WycheproofTest {
        #[serde(rename = "tcId")]
        id: usize,
        #[serde(default, with = "hex::serde")]
        msg: Vec<u8>,
        #[serde(default, with = "hex::serde")]
        ctx: Vec<u8>,
        #[serde(default, with = "hex::serde")]
        mu: Vec<u8>,
        #[serde(default, with = "hex::serde")]
        rnd: Vec<u8>,
        #[serde(with = "hex::serde")]
        sig: Vec<u8>,
        result: Expected,
        flags: Vec<String>,
    }

    impl WycheproofTest {
        /// The `mu` this test signs: of its message and context, unless it
        /// gives only `mu` (flag `Internal`). `None` if its context is too
        /// long, so it has none.
        fn mu(&self, tr: &[u8; TR_LEN]) -> Option<[u8; MU_LEN]> {
            if self.flags.iter().any(|flag| flag == "Internal") {
                return Some(self.mu.as_slice().try_into().unwrap());
            }
            let mu = mu(tr, &self.ctx, &self.msg).ok()?;
            if !self.mu.is_empty() {
                assert_eq!(mu[..], self.mu, "tcId {}", self.id);
            }
            Some(mu)
        }
    }

    /// Runs a `sign_seed` or `sign_noseed` file: loads each group's key,
    /// checks its public key, and signs each test with its `rnd`, or zeros.
    fn wycheproof_sign<P: Params>(
        name: &str,
        load: fn(&WycheproofGroup) -> Result<KeyPair<P>, Error>,
    ) {
        for group in wycheproof_groups::<WycheproofGroup>(name) {
            let key = match load(&group) {
                Ok(key) => key,
                Err(_) => {
                    for test in &group.tests {
                        assert_eq!(test.result, Expected::Invalid, "tcId {}", test.id);
                    }
                    continue;
                }
            };
            let public_key = hex::decode(group.public_key.as_ref().unwrap()).unwrap();
            assert_eq!(key.public_key().as_ref(), public_key);
            // `tr` is the public key's hash, though a loaded private key's
            // copy is marked secret.
            let tr = low::ct::into_public(*key.tr());
            for test in &group.tests {
                let Some(mu) = test.mu(&tr) else {
                    assert_eq!(test.result, Expected::Invalid, "tcId {}", test.id);
                    continue;
                };
                assert_eq!(test.result, Expected::Valid, "tcId {}", test.id);
                let rnd = match test.rnd.is_empty() {
                    true => [0; RND_LEN],
                    false => test.rnd.as_slice().try_into().unwrap(),
                };
                let signature = key.sign_internal(&mu, &rnd).unwrap();
                assert_eq!(signature.as_ref(), test.sig, "tcId {}", test.id);
                let _entry = Entry::new_public();
                verify_internal::<P>(key.public_key().as_ref(), &mu, signature.as_ref()).unwrap();
            }
        }
    }

    fn wycheproof_verify<P: Params>(name: &str) {
        for group in wycheproof_groups::<WycheproofGroup>(name) {
            let pk = &hex::decode(group.public_key.as_ref().unwrap()).unwrap();
            for test in &group.tests {
                let result = verify::<P>(pk, &tr(pk), &test.ctx, &test.msg, &test.sig);
                assert_eq!(
                    result.is_ok(),
                    test.result == Expected::Valid,
                    "tcId {}",
                    test.id
                );
            }
        }
    }

    #[test]
    fn wycheproof() {
        fn check<P: Params>([seed, noseed, verify]: [&str; 3]) {
            wycheproof_sign::<P>(seed, |group| {
                let seed = group
                    .seed
                    .as_slice()
                    .try_into()
                    .map_err(|_| Error::WrongLength)?;
                Ok(KeyPair::from_seed(seed))
            });
            wycheproof_sign::<P>(noseed, |group| KeyPair::from_secret_key(&group.private_key));
            wycheproof_verify::<P>(verify);
        }
        check::<MlDsa44>([
            "mldsa_44_sign_seed_test.json",
            "mldsa_44_sign_noseed_test.json",
            "mldsa_44_verify_test.json",
        ]);
        check::<MlDsa65>([
            "mldsa_65_sign_seed_test.json",
            "mldsa_65_sign_noseed_test.json",
            "mldsa_65_verify_test.json",
        ]);
        check::<MlDsa87>([
            "mldsa_87_sign_seed_test.json",
            "mldsa_87_sign_noseed_test.json",
            "mldsa_87_verify_test.json",
        ]);
    }

    #[test]
    fn sign_verify_round_trip() {
        fn check<P: Params>() {
            let key = KeyPair::<P>::generate().unwrap();
            let pk = key.public_key().as_ref();
            let tr = tr(pk);
            assert_eq!(&tr, key.tr());
            let signature = key.sign(b"context", b"message").unwrap();
            verify::<P>(pk, &tr, b"context", b"message", signature.as_ref()).unwrap();
            assert_eq!(
                verify::<P>(pk, &tr, b"", b"message", signature.as_ref()),
                Err(Error::BadSignature)
            );
            assert_eq!(
                verify::<P>(pk, &tr, b"context", b"massage", signature.as_ref()),
                Err(Error::BadSignature)
            );
            assert_eq!(
                key.sign(&[0; 256], b"message").err(),
                Some(Error::WrongLength)
            );
        }
        check::<MlDsa44>();
        check::<MlDsa65>();
        // ML-DSA-44 and -65 between them take each branch on `ETA`,
        // `GAMMA1`, and `GAMMA2`, so Miri, which is slow, leaves out -87.
        if !cfg!(miri) {
            check::<MlDsa87>();
        }
    }
}
