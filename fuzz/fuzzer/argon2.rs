#![no_main]

//! Argon2id against RustCrypto's `argon2` for any password, salt, secret,
//! associated data, and output length, at a small memory, and checking that
//! output tampered with.

use ::argon2::{Algorithm, Argon2, AssociatedData, ParamsBuilder, Version};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::argon2::Params;

mod edit;

#[derive(Arbitrary, Debug)]
struct Input {
    password: Vec<u8>,
    salt: Vec<u8>,
    secret: Vec<u8>,
    ad: Vec<u8>,
    /// Added to the minimum memory of eight blocks per lane.
    extra_kib: u8,
    passes: u8,
    lanes: u8,
    /// The output length, from the minimum of 4.
    len: u8,
    edit: edit::Edit,
}

fuzz_target!(|input: Input| {
    let lanes = u32::from(input.lanes % 3) + 1;
    let memory = lanes * 8 + u32::from(input.extra_kib % 16);
    let passes = u32::from(input.passes % 2) + 1;
    let len = usize::from(input.len % 96) + 4;
    let salt = if input.salt.len() >= 8 {
        input.salt
    } else {
        let mut salt = input.salt;
        salt.resize(8, 0x02);
        salt
    };
    let ad = if input.ad.len() <= AssociatedData::MAX_LEN {
        input.ad
    } else {
        input.ad[..AssociatedData::MAX_LEN].to_vec()
    };

    let mut builder = ParamsBuilder::new();
    builder
        .m_cost(memory)
        .t_cost(passes)
        .p_cost(lanes)
        .output_len(len);
    builder.data(AssociatedData::new(&ad).unwrap());
    let theirs = Argon2::new_with_secret(
        &input.secret,
        Algorithm::Argon2id,
        Version::V0x13,
        builder.build().unwrap(),
    )
    .unwrap();
    let mut theirs_out = vec![0u8; len];
    theirs
        .hash_password_into(&input.password, &salt, &mut theirs_out)
        .unwrap();

    let params = Params::new(memory, passes, lanes).unwrap();
    let ours = rind::argon2::Secret::new(&input.password).unwrap();
    let mut ours_out = vec![0u8; len];
    ours.derive(params, &salt, &input.secret, &ad, &mut ours_out)
        .unwrap();
    assert_eq!(ours_out, theirs_out);

    let mut stored = ours_out.clone();
    input.edit.apply(&mut stored);
    // The tag length is hashed into H0, so a shorter tag is not a prefix of a
    // longer one. A cut is a different derivation, and `verify` rejects it.
    let valid = stored.len() == ours_out.len() && stored == ours_out;
    let result = ours.verify(params, &salt, &input.secret, &ad, &stored);
    if stored.len() < 4 {
        assert_eq!(result, Err(rind::Error::WrongLength));
        return;
    }
    assert_eq!(result.is_ok(), valid, "{result:?}");
});
