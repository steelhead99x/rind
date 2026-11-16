// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The ACVP build's one extra service: the deterministic forms of the
//! randomized services (`rind::fips::acvp`), with the randomness ACVP
//! supplies, for `rind-acvp`.
//!
//! FIPS 203 and 204 allow these forms only for testing, so only the build
//! `rind-fips`'s `__acvp` feature asks for has this symbol; the module a
//! program links never does. Every other service ACVP tests is the module's
//! own, which `rind-acvp` calls as any program does.

use rind::Error;
use rind::fips::acvp::{self, MlDsaMessage};
use rind::ml_dsa::{MlDsa44, MlDsa65, MlDsa87, ParameterSet};

use crate::abi::{Bytes, Status, byte_list, copy_out, status};
use crate::ids::{acvp as op, kem, ml_dsa};
use crate::scrub::{Depth, scrubbed};
use crate::selftest::{SelfTest, ensure};

/// Runs ACVP operation `op` (`ids::acvp`) of the algorithm or parameter set
/// `param` names on the `nargs` byte strings at `args`, writing its output
/// to the `cap` bytes at `out` and its length to `len`.
///
/// The DRBG's output is `cap` bytes long; the others' outputs are their
/// encodings, concatenated in the order `ids::acvp` lists them.
///
/// # Safety
/// `args` must be valid as `abi::byte_list` requires, `out` for `cap`
/// writes, and `len` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_acvp(
    op: u32,
    param: u32,
    args: *const Bytes,
    nargs: usize,
    out: *mut u8,
    cap: usize,
    len: *mut usize,
) -> Status {
    // SAFETY: the caller's contract.
    let args = unsafe { byte_list(args, nargs) };
    let test = match op {
        op::DRBG => SelfTest::Drbg,
        op::ML_KEM_KEY_GEN
        | op::ML_KEM_ENCAP
        | op::ML_KEM_DECAP
        | op::ML_KEM_CHECK_ENCAPSULATION_KEY
        | op::ML_KEM_CHECK_DECAPSULATION_KEY => SelfTest::MlKem,
        op::ML_DSA_KEY_GEN | op::ML_DSA_SIGN | op::ML_DSA_VERIFY => SelfTest::MlDsa,
        _ => return status(Err(Error::Unsupported)),
    };
    ensure(&[test]);
    scrubbed(Depth::Large, || {
        let output = match test {
            SelfTest::Drbg => drbg(&args, cap),
            SelfTest::MlKem => ml_kem(op, param, &args),
            _ => ml_dsa(op, param, &args),
        };
        // SAFETY: the caller's contract.
        status(output.and_then(|output| unsafe { copy_out(&output, out, cap, len) }))
    })
}

/// `args` as exactly `N` byte strings.
fn take<'a, const N: usize>(args: &[&'a [u8]]) -> Result<[&'a [u8]; N], Error> {
    args.try_into().map_err(|_| Error::WrongLength)
}

/// `bytes` as an array of `N`.
fn array<const N: usize>(bytes: &[u8]) -> Result<&[u8; N], Error> {
    bytes.try_into().map_err(|_| Error::WrongLength)
}

/// HMAC_DRBG over SHA-512 with prediction resistance, as `op::DRBG`
/// documents.
fn drbg(args: &[&[u8]], len: usize) -> Result<Vec<u8>, Error> {
    let [
        entropy,
        nonce,
        personalization,
        ad1,
        entropy1,
        ad2,
        entropy2,
    ] = take(args)?;
    let mut out = vec![0; len];
    acvp::Drbg {
        entropy,
        nonce,
        personalization,
        generates: [
            acvp::Generate {
                entropy: entropy1,
                additional_input: ad1,
            },
            acvp::Generate {
                entropy: entropy2,
                additional_input: ad2,
            },
        ],
    }
    .run(&mut out);
    Ok(out)
}

/// ML-KEM of parameter set `param`, as `ids::acvp` documents each operation.
fn ml_kem(op: u32, param: u32, args: &[&[u8]]) -> Result<Vec<u8>, Error> {
    match param {
        kem::ML_KEM_512 => ml_kem_set::<rind::kem::MlKem512>(op, args),
        kem::ML_KEM_768 => ml_kem_set::<rind::kem::MlKem768>(op, args),
        kem::ML_KEM_1024 => ml_kem_set::<rind::kem::MlKem1024>(op, args),
        _ => Err(Error::Unsupported),
    }
}

fn ml_kem_set<P: rind::kem::Algorithm>(op: u32, args: &[&[u8]]) -> Result<Vec<u8>, Error> {
    Ok(match op {
        op::ML_KEM_KEY_GEN => {
            let [d, z] = take(args)?;
            let (ek, dk) = acvp::ml_kem_key_gen::<P>(array(d)?, array(z)?);
            [ek.as_ref(), dk.as_ref()].concat()
        }
        op::ML_KEM_ENCAP => {
            let [ek, m] = take(args)?;
            let (ciphertext, secret) = acvp::ml_kem_encap::<P>(ek, array(m)?)?;
            [ciphertext.as_ref(), &secret[..]].concat()
        }
        op::ML_KEM_DECAP => {
            let [dk, ciphertext] = take(args)?;
            acvp::ml_kem_decap::<P>(dk, ciphertext)?.to_vec()
        }
        op::ML_KEM_CHECK_ENCAPSULATION_KEY => {
            let [ek] = take(args)?;
            acvp::ml_kem_check_encapsulation_key::<P>(ek)?;
            Vec::new()
        }
        _ => {
            let [dk] = take(args)?;
            acvp::ml_kem_check_decapsulation_key::<P>(dk)?;
            Vec::new()
        }
    })
}

/// ML-DSA of parameter set `set`, as `ids::acvp` documents each operation.
fn ml_dsa(op: u32, set: u32, args: &[&[u8]]) -> Result<Vec<u8>, Error> {
    match set {
        ml_dsa::ML_DSA_44 => ml_dsa_with::<MlDsa44>(op, args),
        ml_dsa::ML_DSA_65 => ml_dsa_with::<MlDsa65>(op, args),
        ml_dsa::ML_DSA_87 => ml_dsa_with::<MlDsa87>(op, args),
        _ => Err(Error::Unsupported),
    }
}

fn ml_dsa_with<P: ParameterSet>(op: u32, args: &[&[u8]]) -> Result<Vec<u8>, Error> {
    Ok(match op {
        op::ML_DSA_KEY_GEN => {
            let [seed] = take(args)?;
            let (pk, sk) = acvp::ml_dsa_key_gen::<P>(array(seed)?);
            [pk.as_ref(), sk.as_ref()].concat()
        }
        op::ML_DSA_SIGN => {
            let [sk, rnd, interface, a, b] = take(args)?;
            let message = message(interface, a, b)?;
            acvp::ml_dsa_sign::<P>(sk, message, array(rnd)?)?
                .as_ref()
                .to_vec()
        }
        _ => {
            let [pk, signature, interface, a, b] = take(args)?;
            acvp::ml_dsa_verify::<P>(pk, message(interface, a, b)?, signature)?;
            Vec::new()
        }
    })
}

/// The message by the interface `ids::acvp::ml_dsa_interface` names in
/// `interface`'s one byte: `a` is the message, internal `M'`, or `mu`, and
/// `b` the external interface's context, empty for the others.
fn message<'a>(interface: &[u8], a: &'a [u8], b: &'a [u8]) -> Result<MlDsaMessage<'a>, Error> {
    use crate::ids::ml_dsa_interface::*;
    let internal = || {
        if b.is_empty() {
            Ok(())
        } else {
            Err(Error::Unsupported)
        }
    };
    match interface {
        [EXTERNAL] => Ok(MlDsaMessage::External {
            context: b,
            message: a,
        }),
        [INTERNAL] => internal().map(|()| MlDsaMessage::Internal(a)),
        [MU] => internal().map(|()| MlDsaMessage::Mu(a)),
        _ => Err(Error::Unsupported),
    }
}
