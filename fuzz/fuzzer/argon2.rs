#![no_main]

//! Argon2id against RustCrypto's `argon2`, as aws-lc-rs has none, for any
//! password and salt, small costs, and several output lengths, and checking
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

    // Lengths around BLAKE2b's 64-byte output, where H' changes form.
    match input.len % 6 {
        0 => check::<4>(&input, &theirs, ours_params),
        1 => check::<32>(&input, &theirs, ours_params),
        2 => check::<64>(&input, &theirs, ours_params),
        3 => check::<65>(&input, &theirs, ours_params),
        4 => check::<97>(&input, &theirs, ours_params),
        _ => check::<200>(&input, &theirs, ours_params),
    }
});

fn check<const N: usize>(input: &Input, theirs: &argon2::Argon2, params: ours::Params) {
    let (password, salt) = (&input.password, &input.salt);
    let mut ours_out = [0; N];
    let ours_result = ours::derive(params, password, salt, &mut ours_out);
    let mut theirs_out = [0; N];
    let theirs_result = theirs.hash_password_into(password, salt, &mut theirs_out);
    // Both refuse a salt shorter than 8 bytes.
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

    let mut stored = ours_out.to_vec();
    input.edit.apply(&mut stored);
    let Ok(stored) = <[u8; N]>::try_from(stored) else {
        return;
    };
    assert_eq!(
        ours::verify(params, password, salt, &stored).is_ok(),
        stored == ours_out
    );
}
