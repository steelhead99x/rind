// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The deterministic forms of the module's randomized services, which ACVP
//! drives with randomness of its own, from the module's ACVP build: for
//! `rind-acvp` only.
//!
//! FIPS 203 and 204 allow these forms only for testing, so the `__acvp`
//! feature that builds them is for testing only; no other build of the
//! module has them.

use ids::acvp as op;

use crate::Error;
use crate::ffi::{Bytes, Status, check, ids};
use crate::kem;
use crate::ml_dsa::ParameterSet;

unsafe extern "C" {
    fn rind_fips_acvp(
        op: u32,
        param: u32,
        args: *const Bytes,
        nargs: usize,
        out: *mut u8,
        cap: usize,
        len: *mut usize,
    ) -> Status;
}

/// Runs `op` of `param` on `args`, into `out`, returning the length used.
fn call(op: u32, param: u32, args: &[&[u8]], out: &mut [u8]) -> Result<usize, Error> {
    let list = Bytes::list(args);
    let mut len = 0;
    // SAFETY: each byte string in `list` is borrowed from `args`, `out` is
    // writable for its length, and `len` is writable.
    check(unsafe {
        rind_fips_acvp(
            op,
            param,
            list.as_ptr(),
            list.len(),
            out.as_mut_ptr(),
            out.len(),
            &mut len,
        )
    })?;
    Ok(len)
}

/// Runs `op` of `param` on `args` for an output of up to `cap` bytes.
fn call_vec(op: u32, param: u32, args: &[&[u8]], cap: usize) -> Result<Vec<u8>, Error> {
    let mut out = vec![0; cap];
    let len = call(op, param, args, &mut out)?;
    out.truncate(len);
    Ok(out)
}

/// `out` split at `at`.
fn split(mut out: Vec<u8>, at: usize) -> (Vec<u8>, Vec<u8>) {
    let tail = out.split_off(at);
    (out, tail)
}

/// One prediction-resistant generate's inputs: the additional input and the
/// entropy it reseeds with first.
#[derive(Clone, Copy, Debug)]
pub struct Generate<'a> {
    /// The reseed's additional input.
    pub additional_input: &'a [u8],
    /// The reseed's entropy input.
    pub entropy: &'a [u8],
}

/// ACVP's prediction-resistance test of the module's DRBG, HMAC_DRBG over
/// SHA-512: instantiates with `entropy`, `nonce`, and `personalization`,
/// runs both `generates`, and writes the second's output to `out`.
pub fn drbg(
    entropy: &[u8],
    nonce: &[u8],
    personalization: &[u8],
    generates: [Generate<'_>; 2],
    out: &mut [u8],
) -> Result<(), Error> {
    let [first, second] = generates;
    call(
        op::DRBG,
        0,
        &[
            entropy,
            nonce,
            personalization,
            first.additional_input,
            first.entropy,
            second.additional_input,
            second.entropy,
        ],
        out,
    )
    .map(drop)
}

/// The lengths of the encapsulation key, decapsulation key, ciphertext, and
/// shared secret of parameter set `A`.
fn ml_kem_lens<A: kem::Algorithm>() -> [usize; 4] {
    match A::ID {
        ids::kem::ML_KEM_512 => [800, 1632, 768, 32],
        ids::kem::ML_KEM_768 => [1184, 2400, 1088, 32],
        _ => [1568, 3168, 1568, 32],
    }
}

/// FIPS 203's `ML-KEM.KeyGen_internal` at parameter set `A` from seeds `d`
/// and `z`: the encapsulation key and the expanded decapsulation key.
pub fn ml_kem_key_gen<A: kem::Algorithm>(d: &[u8], z: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let [ek, dk, ..] = ml_kem_lens::<A>();
    let out = call_vec(op::ML_KEM_KEY_GEN, A::ID, &[d, z], ek + dk)?;
    Ok(split(out, ek))
}

/// FIPS 203's `ML-KEM.Encaps_internal` of message `m` to encapsulation key
/// `ek` of parameter set `A`, after its input check: the ciphertext and the
/// shared secret.
pub fn ml_kem_encap<A: kem::Algorithm>(ek: &[u8], m: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let [.., ciphertext, secret] = ml_kem_lens::<A>();
    let out = call_vec(op::ML_KEM_ENCAP, A::ID, &[ek, m], ciphertext + secret)?;
    Ok(split(out, ciphertext))
}

/// FIPS 203's `ML-KEM.Decaps_internal` of `ciphertext` with expanded
/// decapsulation key `dk` of parameter set `A`, after their input checks:
/// the shared secret.
pub fn ml_kem_decap<A: kem::Algorithm>(dk: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>, Error> {
    let [.., secret] = ml_kem_lens::<A>();
    call_vec(op::ML_KEM_DECAP, A::ID, &[dk, ciphertext], secret)
}

/// FIPS 203's encapsulation key check, at parameter set `A`.
pub fn ml_kem_check_encapsulation_key<A: kem::Algorithm>(ek: &[u8]) -> Result<(), Error> {
    call(op::ML_KEM_CHECK_ENCAPSULATION_KEY, A::ID, &[ek], &mut []).map(drop)
}

/// FIPS 203's decapsulation key check, at parameter set `A`.
pub fn ml_kem_check_decapsulation_key<A: kem::Algorithm>(dk: &[u8]) -> Result<(), Error> {
    call(op::ML_KEM_CHECK_DECAPSULATION_KEY, A::ID, &[dk], &mut []).map(drop)
}

/// What an ML-DSA signature is over, by the interface ACVP tests.
#[derive(Clone, Copy, Debug)]
pub enum MlDsaMessage<'a> {
    /// FIPS 204's external interface, pure ML-DSA: a message under a
    /// context of at most 255 bytes.
    External {
        /// The context string.
        context: &'a [u8],
        /// The message.
        message: &'a [u8],
    },
    /// The internal interface's `M'`, taken as is.
    Internal(&'a [u8]),
    /// The message representative `mu`, computed elsewhere.
    Mu(&'a [u8]),
}

impl<'a> MlDsaMessage<'a> {
    /// The interface's byte, the message, and the context.
    fn args(self) -> ([u8; 1], &'a [u8], &'a [u8]) {
        use ids::ml_dsa_interface::*;
        match self {
            Self::External { context, message } => ([EXTERNAL], message, context),
            Self::Internal(message) => ([INTERNAL], message, &[]),
            Self::Mu(mu) => ([MU], mu, &[]),
        }
    }
}

/// The public key, expanded private key, and signature lengths of `P`.
fn ml_dsa_lens<P: ParameterSet>() -> [usize; 3] {
    match P::ID {
        ids::ml_dsa::ML_DSA_44 => [1312, 2560, 2420],
        ids::ml_dsa::ML_DSA_65 => [1952, 4032, 3309],
        _ => [2592, 4896, 4627],
    }
}

/// FIPS 204's `ML-DSA.KeyGen_internal` from `seed`: the public key and the
/// expanded private key.
pub fn ml_dsa_key_gen<P: ParameterSet>(seed: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let [pk, sk, _] = ml_dsa_lens::<P>();
    let out = call_vec(op::ML_DSA_KEY_GEN, P::ID, &[seed], pk + sk)?;
    Ok(split(out, pk))
}

/// FIPS 204's `ML-DSA.Sign_internal` with expanded private key `sk` over
/// `message`, with randomness `rnd`, all zeros for the deterministic variant.
pub fn ml_dsa_sign<P: ParameterSet>(
    sk: &[u8],
    message: MlDsaMessage<'_>,
    rnd: &[u8],
) -> Result<Vec<u8>, Error> {
    let (interface, message, context) = message.args();
    let [.., len] = ml_dsa_lens::<P>();
    call_vec(
        op::ML_DSA_SIGN,
        P::ID,
        &[sk, rnd, &interface, message, context],
        len,
    )
}

/// FIPS 204's `ML-DSA.Verify_internal` of `signature` over `message` under
/// public key `pk`.
pub fn ml_dsa_verify<P: ParameterSet>(
    pk: &[u8],
    message: MlDsaMessage<'_>,
    signature: &[u8],
) -> Result<(), Error> {
    let (interface, message, context) = message.args();
    call(
        op::ML_DSA_VERIFY,
        P::ID,
        &[pk, signature, &interface, message, context],
        &mut [],
    )
    .map(drop)
}
