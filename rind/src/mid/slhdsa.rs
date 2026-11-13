// Ported from the SPHINCS+ team's FIPS 205 code, which its authors placed in
// the public domain.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SLH-DSA, as FIPS 205 specifies it: a port of the SPHINCS+ team's code
//! (`sphincs/sphincsplus`, branch `bas/fips205`), its `sign.c`, `fors.c`,
//! `wots.c`, and `merkle.c`, with the multi-lane tree hashing of its AVX2
//! builds (`treehashx4` and `treehashx8`, generalised over the lane count).
//!
//! SHAKE runs four Keccak-f permutations at once, as rind's four-way
//! Keccak-f does with AVX2 or two two-way SHA-3 calls on aarch64, and the
//! SHA-2 sets run eight SHA-256 hashes at once, which AVX2 does without the
//! SHA extensions.
//!
//! A signature reveals its randomiser `R`, so the indices the message digest
//! picks, and every tree root each layer signs, which verification
//! recomputes. Signing declassifies them as it derives them; what stays
//! secret is `SK.seed` and `SK.prf`, and the chain values and leaves they
//! derive, which only constant-time hashes touch.

// A parameter set's sizes are associated constants, which stable Rust cannot
// pass as `as_chunks`'s const argument in generic code.
#![allow(clippy::chunks_exact_to_as_chunks)]

use core::fmt;
use core::panic::{RefUnwindSafe, UnwindSafe};

use crate::Error;
use crate::error::KeyFormatError;
use crate::low::{self, Entry, UpdateBlocks};
use crate::mid::mldsa::Array;
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::sha2::{Sha256Context, Sha256State, Sha512Context, Sha512State};
use crate::mid::sha3::{Shake256Sponge, shake256_x4};

/// The largest `n`, the hash output length.
const MAX_N: usize = 32;
/// The largest `len`, the WOTS+ chains per key: `2n + 3` with `lg_w = 4`.
const MAX_LEN: usize = 2 * MAX_N + 3;
/// The largest FORS tree height `a`, and so the tallest tree hashed.
const MAX_A: usize = 14;
/// The largest FORS tree count `k`.
const MAX_K: usize = 35;
/// The largest message digest length `m`.
const MAX_M: usize = 49;
/// The hashes run at once: four SHAKE, or eight SHA-256.
const MAX_LANES: usize = 8;
/// The Winternitz parameter `w`, for `lg_w = 4`.
const W: u32 = 16;

macro_rules! sets {
    ($($(#[$doc:meta])* $set:ident,)*) => {$(
        $(#[$doc])*
        #[derive(Debug)]
        pub enum $set {}
    )*};
}

sets! {
    /// SLH-DSA-SHA2-128s, as standardised by FIPS 205.
    SlhDsaSha2_128s,
    /// SLH-DSA-SHA2-128f, as standardised by FIPS 205.
    SlhDsaSha2_128f,
    /// SLH-DSA-SHA2-192s, as standardised by FIPS 205.
    SlhDsaSha2_192s,
    /// SLH-DSA-SHA2-192f, as standardised by FIPS 205.
    SlhDsaSha2_192f,
    /// SLH-DSA-SHA2-256s, as standardised by FIPS 205.
    SlhDsaSha2_256s,
    /// SLH-DSA-SHA2-256f, as standardised by FIPS 205.
    SlhDsaSha2_256f,
    /// SLH-DSA-SHAKE-128s, as standardised by FIPS 205.
    SlhDsaShake128s,
    /// SLH-DSA-SHAKE-128f, as standardised by FIPS 205.
    SlhDsaShake128f,
    /// SLH-DSA-SHAKE-192s, as standardised by FIPS 205.
    SlhDsaShake192s,
    /// SLH-DSA-SHAKE-192f, as standardised by FIPS 205.
    SlhDsaShake192f,
    /// SLH-DSA-SHAKE-256s, as standardised by FIPS 205.
    SlhDsaShake256s,
    /// SLH-DSA-SHAKE-256f, as standardised by FIPS 205.
    SlhDsaShake256f,
}

/// A FIPS 205 parameter set: its hash family and dimensions, with the arrays
/// its keys fill, which stable Rust cannot size from the constants.
///
/// Its bounds, like [`Array`]'s, let a generic caller rely on the auto
/// traits every key and signature has.
pub trait Params: fmt::Debug + Send + Sync + Unpin + UnwindSafe + RefUnwindSafe + 'static {
    /// SHAKE256 rather than SHA-2.
    #[doc(hidden)]
    const SHAKE: bool;
    /// `n`, the hash output length.
    #[doc(hidden)]
    const N: usize;
    /// `h`, the hypertree's height.
    #[doc(hidden)]
    const H: usize;
    /// `d`, the hypertree's layers.
    #[doc(hidden)]
    const D: usize;
    /// `a`, each FORS tree's height.
    #[doc(hidden)]
    const A: usize;
    /// `k`, the FORS trees.
    #[doc(hidden)]
    const K: usize;

    /// `h'`, each XMSS tree's height.
    #[doc(hidden)]
    const HP: usize = Self::H / Self::D;
    /// `len`, the WOTS+ chains per key.
    #[doc(hidden)]
    const LEN: usize = 2 * Self::N + 3;
    /// A FORS signature's length.
    #[doc(hidden)]
    const FORS_LEN: usize = Self::K * (Self::A + 1) * Self::N;
    /// An XMSS signature's length: a WOTS+ signature and an authentication
    /// path.
    #[doc(hidden)]
    const XMSS_LEN: usize = (Self::LEN + Self::HP) * Self::N;
    /// A signature's length.
    #[doc(hidden)]
    const SIG_LEN: usize = Self::N + Self::FORS_LEN + Self::D * Self::XMSS_LEN;

    /// `PK.seed || PK.root`, FIPS 205's public key encoding.
    #[doc(hidden)]
    type PublicKey: Array;
    /// `SK.seed || SK.prf || PK.seed || PK.root`, FIPS 205's private key
    /// encoding.
    #[doc(hidden)]
    type SecretKey: Array;
}

macro_rules! params {
    ($(
        $set:ident: $family:ident, n = $n:literal, h = $h:literal, d = $d:literal,
        a = $a:literal, k = $k:literal, m = $m:literal, sig = $sig:literal;
    )*) => {$(
        impl Params for $set {
            const SHAKE: bool = params!(@shake $family);
            const N: usize = $n;
            const H: usize = $h;
            const D: usize = $d;
            const A: usize = $a;
            const K: usize = $k;
            type PublicKey = [u8; 2 * $n];
            type SecretKey = [u8; 4 * $n];
        }

        // FIPS 205's table 2.
        const _: () = {
            assert!(<$set as Params>::SIG_LEN == $sig);
            assert!(digest_len::<$set>() == $m && $m <= MAX_M);
            assert!($n <= MAX_N && $a <= MAX_A && $k <= MAX_K);
            assert!(<$set as Params>::HP * $d == $h);
            // The trees hash a whole group of lanes at their foot.
            assert!(1 << <$set as Params>::HP >= MAX_LANES && 1 << $a >= MAX_LANES);
        };
    )*};
    (@shake Sha2) => { false };
    (@shake Shake) => { true };
}

params! {
    SlhDsaSha2_128s: Sha2, n = 16, h = 63, d = 7, a = 12, k = 14, m = 30, sig = 7856;
    SlhDsaSha2_128f: Sha2, n = 16, h = 66, d = 22, a = 6, k = 33, m = 34, sig = 17088;
    SlhDsaSha2_192s: Sha2, n = 24, h = 63, d = 7, a = 14, k = 17, m = 39, sig = 16224;
    SlhDsaSha2_192f: Sha2, n = 24, h = 66, d = 22, a = 8, k = 33, m = 42, sig = 35664;
    SlhDsaSha2_256s: Sha2, n = 32, h = 64, d = 8, a = 14, k = 22, m = 47, sig = 29792;
    SlhDsaSha2_256f: Sha2, n = 32, h = 68, d = 17, a = 9, k = 35, m = 49, sig = 49856;
    SlhDsaShake128s: Shake, n = 16, h = 63, d = 7, a = 12, k = 14, m = 30, sig = 7856;
    SlhDsaShake128f: Shake, n = 16, h = 66, d = 22, a = 6, k = 33, m = 34, sig = 17088;
    SlhDsaShake192s: Shake, n = 24, h = 63, d = 7, a = 14, k = 17, m = 39, sig = 16224;
    SlhDsaShake192f: Shake, n = 24, h = 66, d = 22, a = 8, k = 33, m = 42, sig = 35664;
    SlhDsaShake256s: Shake, n = 32, h = 64, d = 8, a = 14, k = 22, m = 47, sig = 29792;
    SlhDsaShake256f: Shake, n = 32, h = 68, d = 17, a = 9, k = 35, m = 49, sig = 49856;
}

/// The length of a parameter set's public key encoding.
pub(crate) const fn public_key_len<P: Params>() -> usize {
    2 * P::N
}

/// `m`, the message digest's length: the FORS indices, then the tree and
/// leaf indices.
const fn digest_len<P: Params>() -> usize {
    (P::K * P::A).div_ceil(8) + (P::H - P::HP).div_ceil(8) + P::HP.div_ceil(8)
}

/// The hashes a parameter set runs at once.
const fn lanes<P: Params>() -> usize {
    if P::SHAKE { 4 } else { 8 }
}

/// A key pair: FIPS 205's private key encoding, whose second half is the
/// public key.
///
/// It wipes its whole value on drop under the `wipe` feature.
pub(crate) struct KeyPair<P: Params> {
    secret_key: P::SecretKey,
}

impl<P: Params> KeyPair<P> {
    /// Generates a key pair from the system random source.
    pub(crate) fn generate() -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let n = P::N;
        let mut seeds = [0u8; 3 * MAX_N];
        SystemRandom.fill(&mut seeds[..3 * n])?;
        Ok(Self::from_seeds(
            &seeds[..n],
            &seeds[n..2 * n],
            &seeds[2 * n..3 * n],
        ))
    }

    /// FIPS 205's `slh_keygen_internal`: the key pair `SK.seed`, `SK.prf`,
    /// and `PK.seed` make, each `n` bytes.
    pub(crate) fn from_seeds(sk_seed: &[u8], sk_prf: &[u8], pk_seed: &[u8]) -> Self {
        let _entry = Entry::new_secret();
        let n = P::N;
        let mut key = Self {
            secret_key: P::SecretKey::zeroed(),
        };
        let sk = key.secret_key.as_mut();
        sk[..n].copy_from_slice(sk_seed);
        sk[n..2 * n].copy_from_slice(sk_prf);
        sk[2 * n..3 * n].copy_from_slice(pk_seed);
        low::ct::secret_slice(&sk[..2 * n]);
        let root = top_root::<P>(&sk[..n], &sk[2 * n..3 * n]);
        sk[3 * n..].copy_from_slice(&root[..n]);
        key
    }

    /// Loads FIPS 205's private key encoding, refusing one whose `PK.root`
    /// is not the root its seeds make, so whose signatures its public key
    /// would never verify.
    pub(crate) fn from_secret_key(sk: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let n = P::N;
        if sk.len() != 4 * n {
            return Err(KeyFormatError::WrongLength.into());
        }
        let key = Self::from_seeds(&sk[..n], &sk[n..2 * n], &sk[2 * n..3 * n]);
        match key.public_key()[n..] == sk[3 * n..] {
            true => Ok(key),
            false => Err(KeyFormatError::MismatchedPublicKey.into()),
        }
    }

    /// FIPS 205's private key encoding.
    pub(crate) fn secret_key(&self) -> &P::SecretKey {
        &self.secret_key
    }

    /// FIPS 205's public key encoding, `PK.seed || PK.root`.
    pub(crate) fn public_key(&self) -> &[u8] {
        &self.secret_key.as_ref()[2 * P::N..]
    }

    /// Signs `prefix || message` with fresh randomness: FIPS 205's
    /// `slh_sign_internal`, which pure SLH-DSA calls with the prefix
    /// `0 || len(context) || context`.
    pub(crate) fn sign(&self, prefix: &[u8], message: &[u8]) -> Result<Box<[u8]>, Error> {
        let _entry = Entry::new_secret();
        let mut addrnd = [0u8; MAX_N];
        SystemRandom.fill(&mut addrnd[..P::N])?;
        low::ct::secret_slice(&addrnd);
        Ok(self.sign_internal(prefix, message, &addrnd[..P::N]))
    }

    /// FIPS 205's `slh_sign_internal` with randomness `addrnd`, `n` bytes.
    pub(crate) fn sign_internal(&self, prefix: &[u8], message: &[u8], addrnd: &[u8]) -> Box<[u8]> {
        let _entry = Entry::new_secret();
        let mut signature = vec![0u8; P::SIG_LEN].into_boxed_slice();
        sign_internal::<P>(
            self.secret_key.as_ref(),
            prefix,
            message,
            addrnd,
            &mut signature,
        );
        low::ct::public_slice(&signature);
        signature
    }
}

impl<P: Params> Drop for KeyPair<P> {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl<P: Params> low::Zeroable for KeyPair<P> {}

/// Verifies `signature` over `prefix || message` under public key `pk`:
/// FIPS 205's `slh_verify_internal`, which pure SLH-DSA calls with the
/// prefix `0 || len(context) || context`.
pub(crate) fn verify<P: Params>(
    pk: &[u8],
    prefix: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<(), Error> {
    let _entry = Entry::new_public();
    let n = P::N;
    if pk.len() != 2 * n || signature.len() != P::SIG_LEN {
        return Err(Error::BadSignature);
    }
    let (pk_seed, pk_root) = pk.split_at(n);
    let hasher = Hasher::<P>::new(pk_seed, &[0; MAX_N][..n]);

    let (r, signature) = signature.split_at(n);
    let (md, mut tree, mut idx_leaf) = hash_message::<P>(r, pk_seed, pk_root, prefix, message);

    let mut wots_addr = Address::new(WOTS_HASH);
    let mut tree_addr = Address::new(TREE);
    let mut wots_pk_addr = Address::new(WOTS_PK);
    wots_addr.set_tree(tree);
    wots_addr.set_keypair(idx_leaf);

    let (fors, layers) = signature.split_at(P::FORS_LEN);
    let mut root = fors_pk_from_sig::<P>(&hasher, fors, &md, &wots_addr);

    for (layer, xmss) in layers.chunks_exact(P::XMSS_LEN).enumerate() {
        tree_addr.set_layer(layer as u32);
        tree_addr.set_tree(tree);
        wots_addr.copy_subtree(&tree_addr);
        wots_addr.set_keypair(idx_leaf);
        wots_pk_addr.copy_keypair(&wots_addr);

        let (wots, auth_path) = xmss.split_at(P::LEN * n);
        let mut wots_pk = [0u8; MAX_LEN * MAX_N];
        wots_pk_from_sig::<P>(&hasher, &mut wots_pk[..P::LEN * n], wots, &root, &wots_addr);
        let leaf = hasher.thash1(&wots_pk[..P::LEN * n], &wots_pk_addr);
        root = compute_root::<P>(&hasher, &leaf, idx_leaf, 0, auth_path, &mut tree_addr);

        idx_leaf = (tree & ((1 << P::HP) - 1)) as u32;
        tree >>= P::HP;
    }

    match root[..n] == *pk_root {
        true => Ok(()),
        false => Err(Error::BadSignature),
    }
}

/// `PK.root`, the root of the top XMSS tree.
fn top_root<P: Params>(sk_seed: &[u8], pk_seed: &[u8]) -> [u8; MAX_N] {
    let hasher = Hasher::<P>::new(pk_seed, sk_seed);
    let mut top_tree_addr = Address::new(TREE);
    let mut wots_addr = Address::new(WOTS_HASH);
    top_tree_addr.set_layer(P::D as u32 - 1);
    wots_addr.set_layer(P::D as u32 - 1);
    // Leaf `u32::MAX` is none, so no signature or authentication path is
    // written.
    let mut unused = [0u8; (MAX_LEN + MAX_A) * MAX_N];
    let mut root = [0u8; MAX_N];
    merkle_sign::<P>(
        &hasher,
        &mut unused[..P::XMSS_LEN],
        &mut root,
        &wots_addr,
        &top_tree_addr,
        u32::MAX,
    );
    low::ct::into_public(root)
}

fn sign_internal<P: Params>(
    sk: &[u8],
    prefix: &[u8],
    message: &[u8],
    addrnd: &[u8],
    signature: &mut [u8],
) {
    let n = P::N;
    let (sk_seed, sk) = sk.split_at(n);
    let (sk_prf, pk) = sk.split_at(n);
    let (pk_seed, pk_root) = pk.split_at(n);
    let hasher = Hasher::<P>::new(pk_seed, sk_seed);

    // `R` is the signature's first `n` bytes.
    let r = low::ct::into_public(prf_msg::<P>(sk_prf, addrnd, prefix, message));
    let (sig_r, signature) = signature.split_at_mut(n);
    sig_r.copy_from_slice(&r[..n]);
    let (md, mut tree, mut idx_leaf) =
        hash_message::<P>(&r[..n], pk_seed, pk_root, prefix, message);

    let mut wots_addr = Address::new(WOTS_HASH);
    let mut tree_addr = Address::new(TREE);
    wots_addr.set_tree(tree);
    wots_addr.set_keypair(idx_leaf);

    let (fors, layers) = signature.split_at_mut(P::FORS_LEN);
    // Each root is public: the next layer signs it, and verification
    // recomputes it.
    let mut root = low::ct::into_public(fors_sign::<P>(&hasher, fors, &md, &wots_addr));

    for (layer, xmss) in layers.chunks_exact_mut(P::XMSS_LEN).enumerate() {
        tree_addr.set_layer(layer as u32);
        tree_addr.set_tree(tree);
        wots_addr.copy_subtree(&tree_addr);
        wots_addr.set_keypair(idx_leaf);
        merkle_sign::<P>(&hasher, xmss, &mut root, &wots_addr, &tree_addr, idx_leaf);
        root = low::ct::into_public(root);

        idx_leaf = (tree & ((1 << P::HP) - 1)) as u32;
        tree >>= P::HP;
    }
}

/// `H_msg(R, PK.seed, PK.root, prefix || message)`, split into the FORS
/// message digest, the hypertree's tree index, and its leaf index.
fn hash_message<P: Params>(
    r: &[u8],
    pk_seed: &[u8],
    pk_root: &[u8],
    prefix: &[u8],
    message: &[u8],
) -> ([u8; MAX_M], u64, u32) {
    let m = digest_len::<P>();
    let mut digest = [0u8; MAX_M];
    if P::SHAKE {
        shake256(&[r, pk_seed, pk_root, prefix, message], &mut digest[..m]);
    } else {
        // MGF1-SHA-X(R || PK.seed || SHA-X(R || PK.seed || PK.root || M), m)
        let (inner, len) = sha2::<P>(&[r, pk_seed, pk_root, prefix, message]);
        for (counter, chunk) in (0u32..).zip(digest[..m].chunks_mut(len)) {
            let (block, _) = sha2::<P>(&[r, pk_seed, &inner[..len], &counter.to_be_bytes()]);
            chunk.copy_from_slice(&block[..chunk.len()]);
        }
    }

    let md_len = (P::K * P::A).div_ceil(8);
    let tree_len = (P::H - P::HP).div_ceil(8);
    let tree_bits = P::H - P::HP;
    let (_, rest) = digest.split_at(md_len);
    let (tree_bytes, rest) = rest.split_at(tree_len);
    let tree = to_int(tree_bytes) & (u64::MAX >> (64 - tree_bits));
    let leaf = to_int(&rest[..P::HP.div_ceil(8)]) & ((1 << P::HP) - 1);
    (digest, tree, leaf as u32)
}

/// SHAKE256 of `parts` in turn, filling `output`.
fn shake256(parts: &[&[u8]], output: &mut [u8]) {
    let mut sponge = Shake256Sponge::new();
    for part in parts {
        sponge.absorb(part);
    }
    sponge.finish().squeeze(output);
}

/// `PRF_msg(SK.prf, opt_rand, prefix || message)`: `R`, the randomiser.
fn prf_msg<P: Params>(
    sk_prf: &[u8],
    opt_rand: &[u8],
    prefix: &[u8],
    message: &[u8],
) -> [u8; MAX_N] {
    let mut r = [0u8; MAX_N];
    if P::SHAKE {
        shake256(&[sk_prf, opt_rand, prefix, message], &mut r[..P::N]);
    } else {
        // HMAC-SHA-X(SK.prf, opt_rand || prefix || message), whose key is
        // shorter than a block.
        let block = sha2_block::<P>();
        let keyed = |byte: u8| {
            let mut pad = [byte; 128];
            for (pad, key) in pad.iter_mut().zip(sk_prf) {
                *pad ^= key;
            }
            pad
        };
        let (inner, len) = sha2::<P>(&[&keyed(0x36)[..block], opt_rand, prefix, message]);
        let (outer, _) = sha2::<P>(&[&keyed(0x5c)[..block], &inner[..len]]);
        r[..P::N].copy_from_slice(&outer[..P::N]);
    }
    r
}

/// SHA-256 of `parts`, concatenated, for the sets of security category 1,
/// else SHA-512, and its output length.
fn sha2<P: Params>(parts: &[&[u8]]) -> ([u8; 64], usize) {
    let mut digest = [0u8; 64];
    if P::N < 24 {
        let mut ctx = Sha256Context::new();
        for part in parts {
            ctx.update(part);
        }
        digest[..32].copy_from_slice(&ctx.finish());
        (digest, 32)
    } else {
        let mut ctx = Sha512Context::new();
        for part in parts {
            ctx.update(part);
        }
        digest.copy_from_slice(&ctx.finish());
        (digest, 64)
    }
}

/// The block length of [`sha2`]'s hash.
const fn sha2_block<P: Params>() -> usize {
    if P::N < 24 { 64 } else { 128 }
}

/// `bytes`, at most eight, as a big-endian integer.
fn to_int(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0, |acc, b| (acc << 8) | u64::from(*b))
}

/// The WOTS+ chain lengths that sign `message`, `n` bytes: its base-16
/// digits, then their checksum's three.
fn chain_lengths<P: Params>(message: &[u8]) -> [u8; MAX_LEN] {
    let len1 = 2 * P::N;
    let mut lengths = [0u8; MAX_LEN];
    for (i, byte) in message[..P::N].iter().enumerate() {
        lengths[2 * i] = byte >> 4;
        lengths[2 * i + 1] = byte & 0xf;
    }
    let checksum: u32 = lengths[..len1].iter().map(|&l| W - 1 - u32::from(l)).sum();
    lengths[len1] = (checksum >> 8) as u8 & 0xf;
    lengths[len1 + 1] = (checksum >> 4) as u8 & 0xf;
    lengths[len1 + 2] = checksum as u8 & 0xf;
    lengths
}

/// Signs `root` with the WOTS+ key at leaf `idx_leaf` of the XMSS tree
/// `tree_addr` names, writing the signature and the authentication path to
/// `xmss`, and replaces `root` with the tree's root.
///
/// Leaf `u32::MAX` signs nothing, for key generation's root.
fn merkle_sign<P: Params>(
    hasher: &Hasher<P>,
    xmss: &mut [u8],
    root: &mut [u8; MAX_N],
    wots_addr: &Address,
    tree_addr: &Address,
    idx_leaf: u32,
) {
    let (wots_sig, auth_path) = xmss.split_at_mut(P::LEN * P::N);
    let steps = chain_lengths::<P>(&root[..]);

    let mut tree_addrs = [Address::new(TREE); MAX_LANES];
    let mut leaf_addrs = [Address::new(WOTS_HASH); MAX_LANES];
    let mut pk_addrs = [Address::new(WOTS_PK); MAX_LANES];
    for j in 0..MAX_LANES {
        tree_addrs[j].copy_subtree(tree_addr);
        leaf_addrs[j].copy_subtree(wots_addr);
        pk_addrs[j].copy_subtree(wots_addr);
    }

    treehash::<P>(
        hasher,
        root,
        auth_path,
        idx_leaf,
        0,
        P::HP as u32,
        &mut tree_addrs,
        |leaves, leaf_idx| {
            wots_gen_leaves::<P>(
                hasher,
                leaves,
                leaf_idx,
                &mut leaf_addrs,
                &mut pk_addrs,
                (&mut *wots_sig, idx_leaf, &steps),
            )
        },
    );
}

/// The WOTS+ public keys of the `lanes` leaves from `leaf_idx`, compressed
/// into `leaves`. If one is `sign_leaf`, its chains also write the signature
/// on the message whose chain lengths are `steps` to `sig`.
fn wots_gen_leaves<P: Params>(
    hasher: &Hasher<P>,
    leaves: &mut [[u8; MAX_N]; MAX_LANES],
    leaf_idx: u32,
    leaf_addrs: &mut [Address; MAX_LANES],
    pk_addrs: &mut [Address; MAX_LANES],
    (sig, sign_leaf, steps): (&mut [u8], u32, &[u8; MAX_LEN]),
) {
    let lanes = lanes::<P>();
    let n = P::N;
    let mask = lanes as u32 - 1;
    // The lane whose chains sign, if any.
    let signing = ((leaf_idx ^ sign_leaf) & !mask == 0).then_some((sign_leaf & mask) as usize);

    for j in 0..lanes {
        leaf_addrs[j].set_keypair(leaf_idx + j as u32);
        pk_addrs[j].set_keypair(leaf_idx + j as u32);
    }

    let mut public_keys = [[0u8; MAX_LEN * MAX_N]; MAX_LANES];
    for chain in 0..P::LEN {
        for addr in &mut leaf_addrs[..lanes] {
            addr.set_chain(chain as u32);
            addr.set_hash(0);
            addr.set_type(WOTS_PRF);
        }
        let mut nodes = [[0u8; MAX_N]; MAX_LANES];
        hasher.prf(&leaf_addrs[..lanes], &mut nodes);
        for addr in &mut leaf_addrs[..lanes] {
            addr.set_type(WOTS_HASH);
        }

        let step = u32::from(steps[chain]);
        for k in 0..W {
            if let Some(lane) = signing
                && k == step
            {
                sig[chain * n..(chain + 1) * n].copy_from_slice(&nodes[lane][..n]);
            }
            if k == W - 1 {
                break;
            }
            for addr in &mut leaf_addrs[..lanes] {
                addr.set_hash(k);
            }
            hasher.f_in_place(&mut nodes, &leaf_addrs[..lanes]);
        }
        for (public_key, node) in public_keys.iter_mut().zip(&nodes[..lanes]) {
            public_key[chain * n..(chain + 1) * n].copy_from_slice(&node[..n]);
        }
    }

    let inputs: [&[u8]; MAX_LANES] = core::array::from_fn(|j| &public_keys[j][..P::LEN * n]);
    hasher.thash(&inputs[..lanes], &pk_addrs[..lanes], leaves);
}

/// The WOTS+ public key a signature `sig` on `message` makes, written to
/// `pk`.
fn wots_pk_from_sig<P: Params>(
    hasher: &Hasher<P>,
    pk: &mut [u8],
    sig: &[u8],
    message: &[u8; MAX_N],
    addr: &Address,
) {
    let n = P::N;
    let lanes = lanes::<P>();
    let start = chain_lengths::<P>(message);
    let steps: [u8; MAX_LEN] = core::array::from_fn(|i| W as u8 - 1 - start[i]);
    pk.copy_from_slice(sig);

    // Sorting the chains longest first lets each group of lanes drop its
    // shortest chain as it finishes.
    let mut counts = [0usize; W as usize];
    for &step in &steps[..P::LEN] {
        counts[step as usize] += 1;
    }
    let mut total = 0;
    for count in counts.iter_mut().rev() {
        (*count, total) = (total, total + *count);
    }
    let mut order = [0usize; MAX_LEN];
    for (chain, &step) in steps[..P::LEN].iter().enumerate() {
        order[counts[step as usize]] = chain;
        counts[step as usize] += 1;
    }

    let mut addrs = [*addr; MAX_LANES];
    for group in order[..P::LEN].chunks(lanes) {
        let mut nodes = [[0u8; MAX_N]; MAX_LANES];
        for (j, &chain) in group.iter().enumerate() {
            addrs[j].set_chain(chain as u32);
            nodes[j][..n].copy_from_slice(&pk[chain * n..(chain + 1) * n]);
        }
        let mut active = group.len();
        for k in 0..W {
            while active > 0 && k == u32::from(steps[group[active - 1]]) {
                active -= 1;
            }
            if active == 0 {
                break;
            }
            for (addr, &chain) in addrs.iter_mut().zip(&group[..active]) {
                addr.set_hash(k + u32::from(start[chain]));
            }
            hasher.f_in_place(&mut nodes, &addrs[..active]);
        }
        for (node, &chain) in nodes.iter().zip(group) {
            pk[chain * n..(chain + 1) * n].copy_from_slice(&node[..n]);
        }
    }
}

/// The FORS indices `md` encodes: `k` integers of `a` bits, most significant
/// bit first.
fn fors_indices<P: Params>(md: &[u8]) -> [u32; MAX_K] {
    let mut indices = [0u32; MAX_K];
    let mut offset = 0;
    for index in &mut indices[..P::K] {
        for _ in 0..P::A {
            let bit = (md[offset >> 3] >> (7 - (offset & 7))) & 1;
            *index = (*index << 1) | u32::from(bit);
            offset += 1;
        }
    }
    indices
}

/// Signs `md` with the FORS key `fors_addr` names, writing the signature to
/// `sig` and returning the FORS public key.
fn fors_sign<P: Params>(
    hasher: &Hasher<P>,
    sig: &mut [u8],
    md: &[u8],
    fors_addr: &Address,
) -> [u8; MAX_N] {
    let n = P::N;
    let lanes = lanes::<P>();
    let mut tree_addrs = [Address::new(FORS_TREE); MAX_LANES];
    let mut leaf_addrs = [Address::new(FORS_TREE); MAX_LANES];
    for j in 0..MAX_LANES {
        tree_addrs[j].copy_keypair(fors_addr);
        leaf_addrs[j].copy_keypair(fors_addr);
    }
    let mut roots_addr = Address::new(FORS_ROOTS);
    roots_addr.copy_keypair(fors_addr);

    let indices = fors_indices::<P>(md);
    let mut roots = [0u8; MAX_K * MAX_N];
    for (i, tree) in sig.chunks_exact_mut((P::A + 1) * n).enumerate() {
        let idx_offset = (i as u32) << P::A;
        let (sk, auth_path) = tree.split_at_mut(n);

        tree_addrs[0].set_tree_height(0);
        tree_addrs[0].set_tree_index(indices[i] + idx_offset);
        tree_addrs[0].set_type(FORS_PRF);
        sk.copy_from_slice(&hasher.prf1(&tree_addrs[0])[..n]);
        tree_addrs[0].set_type(FORS_TREE);

        let mut root = [0u8; MAX_N];
        treehash::<P>(
            hasher,
            &mut root,
            auth_path,
            indices[i],
            idx_offset,
            P::A as u32,
            &mut tree_addrs,
            |leaves, addr_idx| {
                for (j, addr) in leaf_addrs[..lanes].iter_mut().enumerate() {
                    addr.set_tree_index(addr_idx + j as u32);
                    addr.set_type(FORS_PRF);
                }
                hasher.prf(&leaf_addrs[..lanes], leaves);
                for addr in &mut leaf_addrs[..lanes] {
                    addr.set_type(FORS_TREE);
                }
                hasher.f_in_place(leaves, &leaf_addrs[..lanes]);
            },
        );
        roots[i * n..(i + 1) * n].copy_from_slice(&root[..n]);
    }
    hasher.thash1(&roots[..P::K * n], &roots_addr)
}

/// The FORS public key a signature `sig` on `md` makes.
fn fors_pk_from_sig<P: Params>(
    hasher: &Hasher<P>,
    sig: &[u8],
    md: &[u8],
    fors_addr: &Address,
) -> [u8; MAX_N] {
    let n = P::N;
    let mut tree_addr = Address::new(FORS_TREE);
    tree_addr.copy_keypair(fors_addr);
    let mut roots_addr = Address::new(FORS_ROOTS);
    roots_addr.copy_keypair(fors_addr);

    let indices = fors_indices::<P>(md);
    let mut roots = [0u8; MAX_K * MAX_N];
    for (i, tree) in sig.chunks_exact((P::A + 1) * n).enumerate() {
        let idx_offset = (i as u32) << P::A;
        let (sk, auth_path) = tree.split_at(n);
        tree_addr.set_tree_height(0);
        tree_addr.set_tree_index(indices[i] + idx_offset);
        let leaf = hasher.thash1(sk, &tree_addr);
        let root = compute_root::<P>(
            hasher,
            &leaf,
            indices[i],
            idx_offset,
            auth_path,
            &mut tree_addr,
        );
        roots[i * n..(i + 1) * n].copy_from_slice(&root[..n]);
    }
    hasher.thash1(&roots[..P::K * n], &roots_addr)
}

/// The root a leaf and its authentication path make, `auth_path.len() / n`
/// levels up, at `leaf_idx` of the tree starting at `idx_offset`.
fn compute_root<P: Params>(
    hasher: &Hasher<P>,
    leaf: &[u8; MAX_N],
    mut leaf_idx: u32,
    mut idx_offset: u32,
    auth_path: &[u8],
    addr: &mut Address,
) -> [u8; MAX_N] {
    let n = P::N;
    let mut node = *leaf;
    for (height, sibling) in auth_path.chunks_exact(n).enumerate() {
        let mut pair = [0u8; 2 * MAX_N];
        match leaf_idx & 1 {
            0 => {
                pair[..n].copy_from_slice(&node[..n]);
                pair[n..2 * n].copy_from_slice(sibling);
            }
            _ => {
                pair[..n].copy_from_slice(sibling);
                pair[n..2 * n].copy_from_slice(&node[..n]);
            }
        }
        leaf_idx >>= 1;
        idx_offset >>= 1;
        addr.set_tree_height(height as u32 + 1);
        addr.set_tree_index(leaf_idx + idx_offset);
        node = hasher.thash1(&pair[..2 * n], addr);
    }
    node
}

/// Merkle's TreeHash over a tree of height `tree_height`, whose leaves
/// `gen_leaves` makes a group of lanes at a time: writes its root, and the
/// authentication path of leaf `leaf_idx`, if any.
///
/// The SPHINCS+ team's `treehashx4` and `treehashx8`, for any lane count:
/// each node on the stack is that many adjacent nodes of the tree, and two
/// combine into their parents. The top levels, where fewer nodes remain than
/// lanes, keep combining in place, the leftmost lanes then holding garbage
/// and `left_adj` saying where the real nodes start.
#[allow(clippy::too_many_arguments)]
fn treehash<P: Params>(
    hasher: &Hasher<P>,
    root: &mut [u8; MAX_N],
    auth_path: &mut [u8],
    leaf_idx: u32,
    idx_offset: u32,
    tree_height: u32,
    tree_addrs: &mut [Address; MAX_LANES],
    mut gen_leaves: impl FnMut(&mut [[u8; MAX_N]; MAX_LANES], u32),
) {
    let n = P::N;
    let lanes = lanes::<P>() as u32;
    let lane_bits = lanes.trailing_zeros();
    let mut stack = [[[0u8; MAX_N]; MAX_LANES]; MAX_A];
    let mut left_adj = 0;
    let mut prev_left_adj = 0;
    let max_idx = (1 << (tree_height - lane_bits)) - 1;

    let mut idx = 0;
    loop {
        let mut current = [[0u8; MAX_N]; MAX_LANES];
        gen_leaves(&mut current, lanes * idx + idx_offset);

        let mut internal_idx_offset = idx_offset;
        let mut internal_idx = idx;
        let mut internal_leaf = leaf_idx;
        let mut h = 0;
        loop {
            if h >= tree_height - lane_bits {
                if h == tree_height {
                    *root = current[lanes as usize - 1];
                    return;
                }
                prev_left_adj = left_adj;
                left_adj = lanes - (1 << (tree_height - h - 1));
            }

            if ((internal_idx << lane_bits) ^ internal_leaf) & !(lanes - 1) == 0 {
                let lane = ((internal_leaf & (lanes - 1)) ^ 1) + prev_left_adj;
                let h = h as usize;
                auth_path[h * n..(h + 1) * n].copy_from_slice(&current[lane as usize][..n]);
            }

            if internal_idx & 1 == 0 && idx < max_idx {
                break;
            }

            // Combine the left node on the stack with this right one. Lanes
            // left of `left_adj` are garbage, whose addresses don't matter.
            internal_idx_offset >>= 1;
            for (j, addr) in tree_addrs[..lanes as usize].iter_mut().enumerate() {
                addr.set_tree_height(h + 1);
                addr.set_tree_index(
                    ((lanes / 2) * (internal_idx & !1))
                        .wrapping_add(j as u32)
                        .wrapping_sub(left_adj)
                        .wrapping_add(internal_idx_offset),
                );
            }
            let left = &stack[h as usize];
            let half = lanes as usize / 2;
            let mut pairs = [[0u8; 2 * MAX_N]; MAX_LANES];
            for (j, pair) in pairs[..lanes as usize].iter_mut().enumerate() {
                let side = if j < half { left } else { &current };
                let j = 2 * (j % half);
                pair[..n].copy_from_slice(&side[j][..n]);
                pair[n..2 * n].copy_from_slice(&side[j + 1][..n]);
            }
            let inputs: [&[u8]; MAX_LANES] = core::array::from_fn(|j| &pairs[j][..2 * n]);
            hasher.thash(
                &inputs[..lanes as usize],
                &tree_addrs[..lanes as usize],
                &mut current,
            );

            h += 1;
            internal_idx >>= 1;
            internal_leaf >>= 1;
        }

        stack[h as usize] = current;
        idx += 1;
    }
}

// ADRS's types.
const WOTS_HASH: u8 = 0;
const WOTS_PK: u8 = 1;
const TREE: u8 = 2;
const FORS_TREE: u8 = 3;
const FORS_ROOTS: u8 = 4;
const WOTS_PRF: u8 = 5;
const FORS_PRF: u8 = 6;

/// ADRS, the 32-byte address that tweaks each hash.
#[derive(Clone, Copy)]
struct Address([u8; 32]);

impl Address {
    fn new(kind: u8) -> Self {
        let mut addr = Self([0; 32]);
        addr.set_type(kind);
        addr
    }

    fn set_layer(&mut self, layer: u32) {
        self.0[0..4].copy_from_slice(&layer.to_be_bytes());
    }

    fn set_tree(&mut self, tree: u64) {
        self.0[8..16].copy_from_slice(&tree.to_be_bytes());
    }

    fn set_type(&mut self, kind: u8) {
        self.0[19] = kind;
    }

    /// Copies the layer and tree from `from`.
    fn copy_subtree(&mut self, from: &Self) {
        self.0[..16].copy_from_slice(&from.0[..16]);
    }

    fn set_keypair(&mut self, keypair: u32) {
        self.0[20..24].copy_from_slice(&keypair.to_be_bytes());
    }

    /// Copies the layer, tree, and key pair from `from`.
    fn copy_keypair(&mut self, from: &Self) {
        self.copy_subtree(from);
        self.0[20..24].copy_from_slice(&from.0[20..24]);
    }

    fn set_chain(&mut self, chain: u32) {
        self.0[24..28].copy_from_slice(&chain.to_be_bytes());
    }

    fn set_hash(&mut self, hash: u32) {
        self.0[28..32].copy_from_slice(&hash.to_be_bytes());
    }

    fn set_tree_height(&mut self, height: u32) {
        self.set_chain(height);
    }

    fn set_tree_index(&mut self, index: u32) {
        self.set_hash(index);
    }

    /// ADRSc, the 22-byte form the SHA-2 sets hash: the layer's, type's,
    /// and tree's low bytes, and the last 12.
    fn compressed(&self) -> [u8; 22] {
        let mut c = [0u8; 22];
        c[0] = self.0[3];
        c[1..9].copy_from_slice(&self.0[8..16]);
        c[9] = self.0[19];
        c[10..].copy_from_slice(&self.0[20..]);
        c
    }
}

/// The keyed hashes F, H, `T_l`, and PRF, for one key's `PK.seed` and
/// `SK.seed`.
struct Hasher<P: Params> {
    pk_seed: [u8; MAX_N],
    sk_seed: [u8; MAX_N],
    /// SHA-256 after the block `PK.seed || 0`, which every F, PRF, and
    /// category 1 H and `T_l` start with.
    sha256: Sha256State,
    /// SHA-512 after the block `PK.seed || 0`, which categories 3 and 5's H
    /// and `T_l` start with.
    sha512: Sha512State,
    _params: core::marker::PhantomData<P>,
}

impl<P: Params> Hasher<P> {
    fn new(pk_seed: &[u8], sk_seed: &[u8]) -> Self {
        let n = P::N;
        let mut hasher = Self {
            pk_seed: [0; MAX_N],
            sk_seed: [0; MAX_N],
            sha256: Sha256State::new(),
            sha512: Sha512State::new(),
            _params: core::marker::PhantomData,
        };
        hasher.pk_seed[..n].copy_from_slice(pk_seed);
        hasher.sk_seed[..n].copy_from_slice(sk_seed);
        if !P::SHAKE {
            let mut block = [0u8; 128];
            block[..n].copy_from_slice(pk_seed);
            hasher.sha256.update_blocks(&block[..64]);
            if P::N >= 24 {
                hasher.sha512.update_blocks(&block);
            }
        }
        hasher
    }

    /// `T_l(PK.seed, ADRS, M)` of one input.
    fn thash1(&self, input: &[u8], addr: &Address) -> [u8; MAX_N] {
        let mut out = [[0u8; MAX_N]; MAX_LANES];
        self.thash(&[input], core::slice::from_ref(addr), &mut out);
        out[0]
    }

    /// `PRF(PK.seed, SK.seed, ADRS)` of one address.
    fn prf1(&self, addr: &Address) -> [u8; MAX_N] {
        let mut out = [[0u8; MAX_N]; MAX_LANES];
        self.prf(core::slice::from_ref(addr), &mut out);
        out[0]
    }

    /// `PRF(PK.seed, SK.seed, ADRS)` of each of `addrs`, a lane each.
    fn prf(&self, addrs: &[Address], out: &mut [[u8; MAX_N]; MAX_LANES]) {
        // PRF is F with `SK.seed` as its message.
        let inputs = [&self.sk_seed[..P::N]; MAX_LANES];
        self.thash(&inputs[..addrs.len()], addrs, out);
    }

    /// F of each of `nodes`' first `addrs.len()` lanes, in place.
    fn f_in_place(&self, nodes: &mut [[u8; MAX_N]; MAX_LANES], addrs: &[Address]) {
        let copy = *nodes;
        let inputs: [&[u8]; MAX_LANES] = core::array::from_fn(|j| &copy[j][..P::N]);
        self.thash(&inputs[..addrs.len()], addrs, nodes);
    }

    /// `T_l(PK.seed, ADRS, M)`, F and H as its one- and two-block cases, of
    /// each of `inputs`, of equal length, under its item of `addrs`, writing
    /// `n` bytes to its item of `out`.
    fn thash(&self, inputs: &[&[u8]], addrs: &[Address], out: &mut [[u8; MAX_N]; MAX_LANES]) {
        debug_assert!(inputs.len() <= lanes::<P>() && addrs.len() >= inputs.len());
        if P::SHAKE {
            // SHAKE256(PK.seed || ADRS || M)
            let pk_seed = &self.pk_seed[..P::N];
            if let [input] = inputs {
                // Verification's paths up the trees hash one lane at a
                // time, which one state does with less to set up.
                shake256(&[pk_seed, &addrs[0].0, input], &mut out[0][..P::N]);
                return;
            }
            let parts: [[&[u8]; 3]; 4] = core::array::from_fn(|j| {
                let j = Ord::min(j, inputs.len() - 1);
                [pk_seed, &addrs[j].0, inputs[j]]
            });
            let mut digests = [[0u8; MAX_N]; 4];
            shake256_x4(&parts[..inputs.len()], &mut digests);
            for (out, digest) in out.iter_mut().zip(&digests[..inputs.len()]) {
                out[..P::N].copy_from_slice(&digest[..P::N]);
            }
            return;
        }
        // F and H fill a small buffer, which zeroing costs little against.
        match inputs[0].len() <= 2 * MAX_N {
            true => self.thash_in::<{ 64 + 2 * MAX_N }>(inputs, addrs, out),
            false => self.thash_in::<{ 64 + MAX_LEN * MAX_N }>(inputs, addrs, out),
        }
    }

    fn thash_in<const CAP: usize>(
        &self,
        inputs: &[&[u8]],
        addrs: &[Address],
        out: &mut [[u8; MAX_N]; MAX_LANES],
    ) {
        let n = P::N;
        let lanes = inputs.len();
        let len = inputs[0].len();
        // SHA-X(PK.seed || 0 || ADRSc || M), from the state after its first
        // block.
        let total = 22 + len;
        let mut buffers = [[0u8; CAP]; MAX_LANES];
        for (buffer, (input, addr)) in buffers.iter_mut().zip(inputs.iter().zip(addrs)) {
            buffer[..22].copy_from_slice(&addr.compressed());
            buffer[22..total].copy_from_slice(input);
        }
        let messages: [&[u8]; MAX_LANES] = core::array::from_fn(|j| &buffers[j][..total]);
        if P::N >= 24 && len > n {
            for (out, message) in out.iter_mut().zip(&messages[..lanes]) {
                out[..n].copy_from_slice(&self.sha512.finish_with(message)[..n]);
            }
        } else {
            let digests = self.sha256.finish_x8(&messages[..lanes]);
            for (out, digest) in out.iter_mut().zip(&digests[..lanes]) {
                out[..n].copy_from_slice(&digest[..n]);
            }
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::{Acvp, CTGRIND_DEBUG, acvp};

    /// Runs `$f::<P>($args)` for the parameter set ACVP names `$set`.
    macro_rules! by_set {
        ($set:expr, $f:ident($($arg:expr),*)) => {
            match $set {
                "SLH-DSA-SHA2-128s" => $f::<SlhDsaSha2_128s>($($arg),*),
                "SLH-DSA-SHA2-128f" => $f::<SlhDsaSha2_128f>($($arg),*),
                "SLH-DSA-SHA2-192s" => $f::<SlhDsaSha2_192s>($($arg),*),
                "SLH-DSA-SHA2-192f" => $f::<SlhDsaSha2_192f>($($arg),*),
                "SLH-DSA-SHA2-256s" => $f::<SlhDsaSha2_256s>($($arg),*),
                "SLH-DSA-SHA2-256f" => $f::<SlhDsaSha2_256f>($($arg),*),
                "SLH-DSA-SHAKE-128s" => $f::<SlhDsaShake128s>($($arg),*),
                "SLH-DSA-SHAKE-128f" => $f::<SlhDsaShake128f>($($arg),*),
                "SLH-DSA-SHAKE-192s" => $f::<SlhDsaShake192s>($($arg),*),
                "SLH-DSA-SHAKE-192f" => $f::<SlhDsaShake192f>($($arg),*),
                "SLH-DSA-SHAKE-256s" => $f::<SlhDsaShake256s>($($arg),*),
                "SLH-DSA-SHAKE-256f" => $f::<SlhDsaShake256f>($($arg),*),
                other => panic!("unexpected parameter set {other}"),
            }
        };
    }

    /// Whether a group's parameter set is tested in this build.
    fn runs(group: &serde_json::Value) -> bool {
        !CTGRIND_DEBUG || group.str("parameterSet").ends_with("128f")
    }

    /// The prefix a test's message is signed under: none under the
    /// internal interface, or pure SLH-DSA's for its context under the
    /// external one.
    fn acvp_prefix(group: &serde_json::Value, test: &serde_json::Value) -> Vec<u8> {
        match group.str("signatureInterface") {
            "internal" => Vec::new(),
            "external" => {
                let context = test.hex("context");
                let mut prefix = vec![0, u8::try_from(context.len()).unwrap()];
                prefix.extend(context);
                prefix
            }
            other => panic!("unexpected interface {other}"),
        }
    }

    #[test]
    fn acvp_key_gen() {
        fn check<P: Params>(test: &serde_json::Value) {
            let key = KeyPair::<P>::from_seeds(
                &test.hex("skSeed"),
                &test.hex("skPrf"),
                &test.hex("pkSeed"),
            );
            assert_eq!(
                key.public_key(),
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
            assert_eq!(loaded.public_key(), test.hex("pk"));
        }
        for group in acvp("SLH-DSA-keyGen-FIPS205") {
            if !runs(&group) {
                continue;
            }
            for test in group.tests() {
                by_set!(group.str("parameterSet"), check(test));
            }
        }
    }

    #[test]
    fn acvp_sig_gen() {
        fn check<P: Params>(group: &serde_json::Value, test: &serde_json::Value) {
            let key = KeyPair::<P>::from_secret_key(&test.hex("sk")).unwrap();
            assert_eq!(key.public_key(), test.hex("pk"));
            let prefix = acvp_prefix(group, test);
            let addrnd = test.hex("additionalRandomness");
            let signature = key.sign_internal(&prefix, &test.hex("message"), &addrnd);
            assert_eq!(
                *signature,
                test.hex("signature"),
                "tcId {}",
                test.int("tcId")
            );
        }
        // The s sets sign for seconds in a debug build, so only SLOW_TESTS
        // takes every test; otherwise each group gives its first.
        let per_group = match std::env::var_os("SLOW_TESTS") {
            Some(_) => usize::MAX,
            None => 1,
        };
        for group in acvp("SLH-DSA-sigGen-FIPS205") {
            if !runs(&group) {
                continue;
            }
            for test in group.tests().iter().take(per_group) {
                by_set!(group.str("parameterSet"), check(&group, test));
            }
        }
    }

    #[test]
    fn acvp_sig_ver() {
        fn check<P: Params>(group: &serde_json::Value, test: &serde_json::Value) {
            let prefix = acvp_prefix(group, test);
            let result = verify::<P>(
                &test.hex("pk"),
                &prefix,
                &test.hex("message"),
                &test.hex("signature"),
            );
            assert_eq!(
                result.is_ok(),
                test.flag("testPassed"),
                "tcId {}: {}",
                test.int("tcId"),
                test.str("reason"),
            );
        }
        for group in acvp("SLH-DSA-sigVer-FIPS205") {
            if !runs(&group) {
                continue;
            }
            for test in group.tests() {
                by_set!(group.str("parameterSet"), check(&group, test));
            }
        }
    }

    #[test]
    fn sign_verify_round_trip() {
        fn check<P: Params>() {
            let key = KeyPair::<P>::generate().unwrap();
            let pk = key.public_key();
            let signature = key.sign(&[0, 0], b"message").unwrap();
            assert_eq!(signature.len(), P::SIG_LEN);
            verify::<P>(pk, &[0, 0], b"message", &signature).unwrap();
            assert_eq!(
                verify::<P>(pk, &[0, 0], b"massage", &signature),
                Err(Error::BadSignature)
            );
            assert_eq!(
                verify::<P>(pk, &[0, 0], b"message", &signature[1..]),
                Err(Error::BadSignature)
            );

            // A private key whose `PK.root` is not its seeds' is refused.
            let mut sk = low::ct::into_public(key.secret_key().clone());
            sk.as_mut()[4 * P::N - 1] ^= 1;
            assert_eq!(
                KeyPair::<P>::from_secret_key(sk.as_ref()).err(),
                Some(KeyFormatError::MismatchedPublicKey.into())
            );
        }
        check::<SlhDsaSha2_128f>();
        check::<SlhDsaShake128f>();
        if CTGRIND_DEBUG {
            return;
        }
        check::<SlhDsaSha2_192f>();
        check::<SlhDsaSha2_256f>();
        check::<SlhDsaShake192f>();
        check::<SlhDsaShake256f>();
    }
}
