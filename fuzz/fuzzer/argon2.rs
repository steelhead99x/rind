#![no_main]

//! Argon2id against RustCrypto's `argon2`, as aws-lc-rs has none, for any
//! password and salt, small costs, and any output length, and checking
//! that output tampered with fails to verify.

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::argon2 as ours;

mod edit;

#[derive(Arbitrary, Debug)]
struct Input {
    /// The memory, in KiB, which stays small so each input runs quickly,
    /// down to below the minimum.
    memory_kib: u8,
    passes: u8,
    lanes: u8,
    password: Vec<u8>,
    salt: Vec<u8>,
    len: u8,
    edit: edit::Edit,
}

fuzz_target!(|input: Input| {
    let (memory_kib, passes, lanes) = (
        u32::from(input.memory_kib),
        u32::from(input.passes % 4),
        u32::from(input.lanes % 8),
    );
    let ours_params = ours::Params::new(memory_kib, passes, lanes);
    let theirs_params = argon2::Params::new(memory_kib, passes, lanes, None);
    // RustCrypto refuses only what RFC 9106 does, as rind does.
    assert_eq!(
        ours_params.is_ok(),
        theirs_params.is_ok(),
        "{ours_params:?}"
    );
    let (Ok(ours_params), Ok(theirs_params)) = (ours_params, theirs_params) else {
        return;
    };
    let theirs = argon2::Argon2::new(
        argon2::Algorithm::Argon2id,
        argon2::Version::V0x13,
        theirs_params,
    );

    // Any length up to 255 bytes, so below RFC 9106's 4-byte minimum and on
    // both sides of BLAKE2b's 64-byte output, where H' changes form.
    let len = usize::from(input.len);
    let (password, salt) = (&input.password, &input.salt);
    let secret = ours::Secret::new(password);
    let mut ours_out = vec![0; len];
    let ours_result = secret.derive(ours_params, salt, &mut ours_out);
    let mut theirs_out = vec![0; len];
    let theirs_result = theirs.hash_password_into(password, salt, &mut theirs_out);
    // Both refuse a salt shorter than 8 bytes and an output shorter than 4.
    assert_eq!(
        ours_result.is_ok(),
        theirs_result.is_ok(),
        "{ours_result:?}"
    );
    if ours_result.is_err() {
        assert_eq!(ours_result, Err(rind::Error::WrongLength));
        return;
    }
    assert_eq!(ours_out, theirs_out);

    // An edited tag verifies exactly when it is RustCrypto's derivation of
    // its own length, which an edit that also cuts bytes can still be.
    let mut stored = ours_out.clone();
    input.edit.apply(&mut stored);
    let expected = match stored.len() == len {
        true => stored == theirs_out,
        false => {
            let mut again = vec![0; stored.len()];
            theirs
                .hash_password_into(password, salt, &mut again)
                .is_ok()
                && stored == again
        }
    };
    assert_eq!(secret.verify(ours_params, salt, &stored).is_ok(), expected);
});
