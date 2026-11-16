// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Ed25519 verification's `[b]B + [s0]P0 + [s1]P1` over s2n-bignum's point
//! routines, for scalars `s0` and `s1` of about 128 bits.
//!
//! Straus's method over width-5 non-adjacent forms of `s0` and `s1`, with
//! tables of each point's odd multiples, and width-8 forms of `b`'s two
//! 128-bit halves, with static tables of `B`'s and `[2^128]B`'s, so the
//! loop runs as many doublings as the longest scalar has bits.
//!
//! Every input is public, so this runs in variable time. Each point
//! routine is HOL Light-proven in s2n-bignum; this composition is covered by
//! tests only.

use crate::low::{
    bignum_neg_p25519, edwards25519_epadd, edwards25519_epdouble, edwards25519_pdouble,
};

/// Computes `res := [base]B + [scalars[0]]points[0] + [scalars[1]]points[1]`
/// as reduced projective `(X, Y, Z)`, from points in reduced extended
/// coordinates `(X, Y, Z, T)`, for scalars below 2^255.
pub(crate) fn edwards25519_msm(
    res: &mut [u64; 12],
    base: &[u64; 4],
    scalars: &[[u64; 4]; 2],
    points: &[[u64; 16]; 2],
) {
    let nafs = [
        non_adjacent_form(&[base[0], base[1], 0, 0], 8),
        non_adjacent_form(&[base[2], base[3], 0, 0], 8),
        non_adjacent_form(&scalars[0], 5),
        non_adjacent_form(&scalars[1], 5),
    ];
    let tables = [odd_multiples(&points[0]), odd_multiples(&points[1])];

    let top = (0..256).rev().find(|&i| nafs.iter().any(|naf| naf[i] != 0));
    let mut acc = IDENTITY;
    for i in (0..=top.unwrap_or(0)).rev() {
        let digits = nafs.map(|naf| naf[i]);
        if digits == [0; 4] {
            // Only the next addition reads `T`, so skip it.
            let mut doubled = [0; 12];
            edwards25519_pdouble(&mut doubled, projective(&acc));
            acc[..12].copy_from_slice(&doubled);
            continue;
        }

        let doubled = acc;
        edwards25519_epdouble(&mut acc, projective(&doubled));
        let entries = [
            BASE_ODD_MULTIPLES.get(odd_index(digits[0])),
            BASE128_ODD_MULTIPLES.get(odd_index(digits[1])),
            tables[0].get(odd_index(digits[2])),
            tables[1].get(odd_index(digits[3])),
        ];
        for (digit, entry) in digits.iter().zip(entries) {
            let Some(entry) = entry else { continue };
            let sum = acc;
            match *digit > 0 {
                true => edwards25519_epadd(&mut acc, &sum, entry),
                false => edwards25519_epadd(&mut acc, &sum, &neg(entry)),
            }
        }
    }
    res.copy_from_slice(projective(&acc));
}

/// `(0, 1, 1, 0)`.
const IDENTITY: [u64; 16] = [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0];

/// The table index of a digit's magnitude, past the end for zero, which
/// adds nothing.
fn odd_index(digit: i8) -> usize {
    match digit {
        0 => usize::MAX,
        d => d.unsigned_abs() as usize / 2,
    }
}

/// `[P, 3P, 5P, ..., 15P]`, the odd multiples a width-5 form's digits take.
fn odd_multiples(point: &[u64; 16]) -> [[u64; 16]; 8] {
    let mut double = [0; 16];
    edwards25519_epdouble(&mut double, projective(point));
    let mut table = [*point; 8];
    for i in 1..table.len() {
        let previous = table[i - 1];
        edwards25519_epadd(&mut table[i], &previous, &double);
    }
    table
}

/// `-(x, y) = (-x, y)`, so `X` and `T` change sign.
fn neg(point: &[u64; 16]) -> [u64; 16] {
    let mut out = *point;
    for i in [0, 12] {
        let mut x = [0; 4];
        bignum_neg_p25519(&mut x, point[i..i + 4].try_into().unwrap());
        out[i..i + 4].copy_from_slice(&x);
    }
    out
}

/// `(X, Y, Z)`.
fn projective(point: &[u64; 16]) -> &[u64; 12] {
    point[..12].try_into().unwrap()
}

/// The width-`w` non-adjacent form of `x < 2^255`: `x = sum(naf[i] 2^i)`,
/// each digit zero or odd and below `2^(w-1)` in magnitude, and at most one
/// nonzero in any `w` consecutive.
pub(crate) fn non_adjacent_form(x: &[u64; 4], w: usize) -> [i8; 256] {
    let mut naf = [0i8; 256];
    // What remains of x above bit i, which a negative digit's borrow raises
    // by one at bit i + w: below 2^256 throughout, as x < 2^255.
    let mut k = *x;
    let mut i = 0;
    while i < 256 {
        let (word, bit) = (i / 64, i % 64);
        if k[word] >> bit & 1 == 0 {
            i += 1;
            continue;
        }

        let mut window = k[word] >> bit;
        if bit + w > 64 && word < 3 {
            window |= k[word + 1] << (64 - bit);
        }
        let window = (window & ((1 << w) - 1)) as i16;
        let digit = match window >= 1 << (w - 1) {
            true => window - (1 << w),
            false => window,
        };
        naf[i] = digit as i8;

        // k -= digit 2^i clears the window, which the scan never reads
        // again, and for a negative digit adds 2^(i + w).
        if digit < 0 {
            let mut j = i + w;
            while j < 256 {
                let (sum, carry) = k[j / 64].overflowing_add(1 << (j % 64));
                k[j / 64] = sum;
                if !carry {
                    break;
                }
                j = (j / 64 + 1) * 64;
            }
        }
        i += w;
    }
    naf
}

/// `[B, 3B, 5B, ..., 127B]`, `B` the base point, with `Z = 1`.
#[rustfmt::skip]
static BASE_ODD_MULTIPLES: [[u64; 16]; 64] = [
    [
        0xc9562d608f25d51a, 0x692cc7609525a7b2, 0xc0a4e231fdd6dc5c, 0x216936d3cd6e53fe,
        0x6666666666666658, 0x6666666666666666, 0x6666666666666666, 0x6666666666666666,
        1, 0, 0, 0,
        0x6dde8ab3a5b7dda3, 0x20f09f80775152f5, 0x66ea4e8e64abe37d, 0x67875f0fd78b7665,
    ],
    [
        0xac62485fd3f8e25c, 0x6343981981624886, 0x1ff4ae743edac83a, 0x67ae9c4a22928f49,
        0x02c3684878f5b4d4, 0x9f16ec1767240304, 0xa126a18e60269ef7, 0x1267b1d177ee69ab,
        1, 0, 0, 0,
        0xcdf908fa78b3a41a, 0x5c27358bfb16fc4a, 0xebef3783adb91527, 0x2a4d025cb1dd9510,
    ],
    [
        0x91409cc0322ef233, 0x5c2819f93e1be1a5, 0xfcef7cf7d12da5de, 0x49fda73eade3587b,
        0x10d21f83d676c8ed, 0x31282eca89430b5d, 0xe02c6e1489924666, 0x5f4825b298feae6f,
        1, 0, 0, 0,
        0x641950bcf3e801d0, 0xafb94e85000926bf, 0x3160ea508736c7f9, 0x745c562c9c593d4c,
    ],
    [
        0x5855981af50e4107, 0x83e809f3bbf1ce95, 0xe9e3ee194b1d8107, 0x14568685fcf4bd4e,
        0x12c4c4b59f4062b8, 0xf0882b46f7abf23d, 0x87ce6468dd36ad41, 0x31c563e32b47d52f,
        1, 0, 0, 0,
        0x10bd45565587ed1b, 0x5294632a1e9aa4e4, 0x9be82dc589d5bab4, 0x119e77b11d165e1b,
    ],
    [
        0xd3e023065185715c, 0x86d80e5c2e4e0294, 0x1bf336e06f9422b8, 0x357cc970c8007165,
        0xc74e44845522f1c0, 0x1f789013236e4430, 0xb2befce956f2d2fd, 0x7f3d23c2c2dd0df4,
        1, 0, 0, 0,
        0x5c3b386f88b2f465, 0x17b3d4a0f770327e, 0xdb6676adf747cd74, 0x5c70fc48ea87cbf9,
    ],
    [
        0xff2fd2c1207cf3cb, 0xd381a5b2c593d552, 0xb6cf078dd6712438, 0x14e528b1154be417,
        0x308f2dc36a033713, 0x1258591c3c9c58d4, 0x5a6f7ce340ff0fce, 0x2d9082313f21ab97,
        1, 0, 0, 0,
        0xeb85cf2edb5beed4, 0x590001dde18fc837, 0x39caa6bef216adbf, 0x5ae6a565800f28a2,
    ],
    [
        0x3780e073b7c05fed, 0x8843e3e88d22b7b8, 0xdb33adf0282d304f, 0x107427e0d5f366cc,
        0x87efe1aeea401f80, 0x3740cfb2289a2723, 0x78466022d2da89b8, 0x12dbb00ded538b74,
        1, 0, 0, 0,
        0x522cdccde8de2f53, 0x5b14aa51eb2e8efc, 0xc5c0dd61cd562338, 0x412806b917be6460,
    ],
    [
        0x90617f3e66a18dc1, 0xd9631374770189cb, 0xdc5ac6f95d20419e, 0x4f162deaec2ec435,
        0x946d4cc4ad2e5cdf, 0xace5af18a19a9aa1, 0x5162f70164d29331, 0x12cbfb2d04ff22f5,
        1, 0, 0, 0,
        0x140d7f335c92bf29, 0xfa63b68fe40ae5f5, 0xab24fd2241760de2, 0x5e33f00e36b77491,
    ],
    [
        0xc5597853a876df6a, 0x8d94985b85a20b4d, 0xb850741ea2fd7291, 0x7dc52d5a7db816e9,
        0xcd6cfe9bec97be04, 0x17b188723b34f901, 0xf24ac245cc919fb7, 0x6f6d2bca60003ef9,
        1, 0, 0, 0,
        0xfdbbb596c3b3053f, 0xb73fdaa20ba9bf68, 0x45590caae076eb00, 0x25031aba502c04a7,
    ],
    [
        0x4f791a3a04a94472, 0xb0e281a5304696e7, 0x22e8c140d763b9c1, 0x1d81f74a5ba45c70,
        0x83fe6102691d55b9, 0x2e1830823f435f30, 0x227c5bb6ddd65cf4, 0x3f185a93d95a4347,
        1, 0, 0, 0,
        0x8bc40427c5001131, 0x41f309e51be53552, 0x7fa48ced0514fef9, 0x66fd9c161a7250de,
    ],
    [
        0xc45e3e7ef9365716, 0xf252cb1dde3d073c, 0x958588f9d47541ed, 0x6f0ac78e5eb90e87,
        0xffc66051336d289e, 0xae06d5c5c7d8a56e, 0xf323e5ddf4f8cc35, 0x6628d116b7975ae5,
        1, 0, 0, 0,
        0x49ebf0b078fc0a26, 0x43ff39d82173f0d5, 0x9ddd0716cdb9f95b, 0x471fb409877912e0,
    ],
    [
        0xab5798b2d2e14d95, 0xcaf91f05d9b7cc2c, 0x25915e05222a391b, 0x2188ac423c67db56,
        0x663d79782b33c0ee, 0x04277b1fa49369ab, 0x4df69a23fc46e505, 0x23240c559c57b79a,
        1, 0, 0, 0,
        0xb5e0fdc89f9d12db, 0x232606ba08e30b11, 0x014451b72b058375, 0x494b54f636077a6b,
    ],
    [
        0x6b19362c36353455, 0xca98552ecb822dc0, 0x09384b370cb8790f, 0x794241471ed9ceb0,
        0x2362bc68d311dcd0, 0x92d79a0a83f37891, 0x07772e8d18ee8f9d, 0x71e918c03cdfca72,
        1, 0, 0, 0,
        0x5e90f270b57a6218, 0x63ae76e58bdb4f5b, 0xc8f5c6f167b5ecca, 0x484e314e6003c9f8,
    ],
    [
        0x29611d8f5a7f8079, 0x3a88b4360aa1d4e7, 0xa23c5c052107bba9, 0x163bc180c22dfc5d,
        0xbae1498677501939, 0x38ca20daf800384d, 0x8194b9766a0a54f6, 0x631107a6ba83f745,
        1, 0, 0, 0,
        0x0abad774fa728050, 0xee4dd99b2d898e67, 0xbc85e83bbd9ab146, 0x337ed9cc25bea461,
    ],
    [
        0x9db663b5db0f7a5d, 0x3890b24b61a3a9e7, 0xeb7e3903b8ace3da, 0x39a32a30f3eb1da0,
        0x6dd203715d67c491, 0x803c16af34582313, 0xa1af9ca0010045dc, 0x4d4c54675dc1f1c9,
        1, 0, 0, 0,
        0x591d58acfa92d128, 0x10efc4c8390ae42a, 0x82261da266bcd8e7, 0x1dc74666facd25ad,
    ],
    [
        0x58e0e4658efac0e9, 0x784d359925f11ff9, 0x59c33fcce7591515, 0x38085391a0e2831f,
        0x55cc31944a19e62a, 0x30e24660669ed919, 0x5634e34ab7fac21b, 0x42918001a829f49b,
        1, 0, 0, 0,
        0x6c352629d89d6076, 0xd414d35c1b056a00, 0x12427b4510938215, 0x1d832bc1670dd8c2,
    ],
    [
        0xe91153eeb75a32a1, 0x4f2455b4a591f719, 0xfbbbbd9a48061743, 0x5e3573b049d6135f,
        0x6566e21a85892871, 0x33bcc2690cd9b37d, 0x1105d53983c1a0fc, 0x54bc665420c789da,
        1, 0, 0, 0,
        0x89b16889c88cea3b, 0x29c07c7b7ecd4f86, 0xabe4288daf7980ce, 0x64f20e09f4af147c,
    ],
    [
        0xd474e5b28270f6eb, 0xacd2f5c3b9330bc8, 0xdc0e46bd80a357f3, 0x7ed068b25b82c05f,
        0x3b97b1db6a21b7d3, 0x1d70df7f943a681c, 0xa704d46557a46255, 0x01da83a187da8ccc,
        1, 0, 0, 0,
        0x23ecc643ad2709ba, 0x2d0566a953409335, 0x5e2f86fec05624bd, 0x001c84c65d03b363,
    ],
    [
        0xe03951c6a14a0aa3, 0x5484407f14b515ad, 0x86111b72650aab4c, 0x05ca3370e7516f66,
        0x011a3611834c6903, 0x04bf7baee091cee6, 0x966e7f0f5e64b869, 0x6f407fc537b95277,
        1, 0, 0, 0,
        0xe6198fcee019d84a, 0xd27b8eef8658106a, 0x91bdfd3be9c25dc8, 0x32a375ad5f1aeee5,
    ],
    [
        0x7c18211f095ab9c3, 0xd8b3ab33c19306e8, 0xdbca79b8d2b53cb5, 0x624cb312b698bbd6,
        0x9395d0e5200bd8a3, 0x6229f6d0bbea6b61, 0x93731ac9b9a2243b, 0x5b3336b2751e97c7,
        1, 0, 0, 0,
        0xd16d5793aa0222e8, 0xe419611ac2297b05, 0xe01fb4881c527b8d, 0x3e32cc8618b44972,
    ],
    [
        0x21b11a31a051b5f9, 0x5e947e293c704d81, 0x1b34b7e4f47cfcb7, 0x1ddf6ece608fe290,
        0x44d52b52112ea94e, 0x96a147a8246d2e98, 0xce5296d229cfb34f, 0x5e2dc58e9a48a749,
        1, 0, 0, 0,
        0xe1b02594a910f33d, 0x4cfe0381c3447a4a, 0x6a395b633ef34916, 0x2cdadf05da1a64a1,
    ],
    [
        0xe08d625f48c0e101, 0x9418e2d9abd81316, 0x60308fbb1c941ebc, 0x396b384f3d61cfc0,
        0x7e0261107e7ad644, 0x18cc60cb8a64a883, 0x4962bac273a7aa66, 0x7223e5f7b66d1ca2,
        1, 0, 0, 0,
        0xd8a7f8a3afb74473, 0x547409ab3ca7cce8, 0x158d39e192cdd07e, 0x2e0677353c70d4d0,
    ],
    [
        0x696cffe7890fbd50, 0x77a99c817170dbc9, 0xb38d75e4ac0dde8e, 0x53cc3dca3410277f,
        0x40e37d23ececbbe1, 0x9845f5ca08f64a0a, 0x69f4de468d5d5aa1, 0x2592a3aafce64d7c,
        1, 0, 0, 0,
        0x0e11523837c2d716, 0x49a51d1d34f8de7e, 0x0ff2e0296bc1b427, 0x36517fc908a70c78,
    ],
    [
        0x50bb7fc889cc1368, 0xd886904156d43dc5, 0x7b29d3eacdffcd45, 0x34705fe600f5aed7,
        0xcf42e158dbe3b01e, 0x2fa39a476200dd4a, 0xfbcc8e9352993e64, 0x299153c141a8950f,
        1, 0, 0, 0,
        0x65ead276a889d46a, 0xabae5a2da846a7ff, 0xd9c89dacb8e6c8ab, 0x1822eb03d3b54d1c,
    ],
    [
        0x18c9c336b8504618, 0x30a14f8a0b061f81, 0x991fce96b1792ba3, 0x5969255bd089181b,
        0x6ca21575bbb4d7a4, 0xd355547e4ab18a9d, 0xa12b193517fb1147, 0x680a805fa0ae93c2,
        1, 0, 0, 0,
        0xdf43aef5c8008dbd, 0x1f90b7c21a34b86c, 0x4e37a7f20a3d5b44, 0x50db591778c21ef5,
    ],
    [
        0x9a92456c59918ecb, 0x7902752163b1fd49, 0x452df14bda4248b3, 0x27d1d57fa8808d3d,
        0xae009c7a1dff09c3, 0x88d31fedb8aad9d8, 0x9e82904f0b4ff639, 0x0a42f1c0f4c5d7de,
        1, 0, 0, 0,
        0x06d3b0f9dc4062c9, 0x2ae3002de3f3ec94, 0xafa48d42f86eb009, 0x203614db4c54769a,
    ],
    [
        0xa82987ad703d9b8a, 0xa9ba17aec3eac8aa, 0x44edd9cf55bce584, 0x0811d14bfdfdcf21,
        0x0c4746b68306376e, 0x56ada2e041592047, 0xf0ec77d24c5495ea, 0x42bea70d46f3ee0d,
        1, 0, 0, 0,
        0x5a80758e51e81332, 0xde143ad516f0dc9e, 0x46341fd950039427, 0x06ed6a79fb4c3282,
    ],
    [
        0x05303d905d527a4a, 0x6d00c5119c38e5dd, 0xf0650297f154a8e6, 0x4de090761b863cb0,
        0x8cf6057b9772baa8, 0xfbe3d70189e63ca6, 0x198a30e09e7e7edf, 0x5eef0efd105361ce,
        1, 0, 0, 0,
        0xec8879019d237bcf, 0xd7f321864ff08562, 0xd2e93bddb06ed74e, 0x7b42c369ac06a0bc,
    ],
    [
        0x0f3e76bfb4fc4817, 0xf3dc9ae3740aed57, 0x6aaee056ebab7e0e, 0x1d45517858ce4555,
        0xe83844f0d4c5c699, 0x6e1bc1138604eb05, 0x4c0a5ef77798a3ec, 0x0b5a9d8fe8b7ccb0,
        1, 0, 0, 0,
        0xe8040bc9f10663af, 0xd18b9f1dcf265057, 0x0507fee7d2156fc0, 0x7bbb9318495c369d,
    ],
    [
        0x701e39324b0eeafc, 0x72106c6b3d7f3ce3, 0xae1ef5ee419eb1d4, 0x4285edbe9117f30a,
        0xedc7173eae04bdbd, 0x0b0caa0fed8db87d, 0x2c0a60c84f4c22b5, 0x503aa6104a682bcf,
        1, 0, 0, 0,
        0x297fb451d87b7b35, 0xd877e476a66039e8, 0xfa43ff89752026e8, 0x1f4082e0455a58b0,
    ],
    [
        0xea1c80351f8687d6, 0xfa56d008d91b9703, 0x39b1b6bd9bb52bbc, 0x3ef830cbeff9b790,
        0x992c7553dc8ee4c8, 0x734bea9240eed623, 0xa874769eec152ef9, 0x62349ff5d8dbd216,
        1, 0, 0, 0,
        0x10a8ed129cf5e85d, 0x89c701d17a5d25d9, 0xdadc3b6c058f0bb7, 0x7223d44476a629a1,
    ],
    [
        0xeaa2fa9830822c1a, 0x34107e03e2fd4648, 0xccb526939ed89291, 0x649a996e6d4d3b60,
        0xc8964cd1acedee9c, 0xaea860d036d2475c, 0x492a1ace5e5235c1, 0x1648311b942fe95d,
        1, 0, 0, 0,
        0x2dbd182f16609f9e, 0x33dfe3294df475a4, 0x8761845f25ff09fa, 0x4b4959d9c3ac599e,
    ],
    [
        0x4ba22c8be73f9d56, 0x5fe6b4b822274053, 0x0d1ecc075d58a74f, 0x3a95596d97770d05,
        0x405c161a34c98fd7, 0x136993e0a797f83b, 0x30fa4a7461de6bac, 0x15a80cdcc03317a8,
        1, 0, 0, 0,
        0xf46747fa8c0f0d02, 0x55434cc43a783afa, 0x124ab811779a0396, 0x216a2e847090b9ec,
    ],
    [
        0xf499d831cbb76ce1, 0xc5af886bf0d9fdb3, 0xca93685209418dee, 0x2d265d3fe1c88903,
        0x5fb2e60a84210b3c, 0x6a1f956622b15a30, 0x20948612b519af4a, 0x08376fb0663d3aa2,
        1, 0, 0, 0,
        0x4f667f96cc1061dd, 0xea59da13473ca6db, 0x75b6c97e2bbef9aa, 0x48cfd55b628f4ef2,
    ],
    [
        0x0a610ed5babb9385, 0x185ac808cbeab5eb, 0x5803f3e56b98e2ea, 0x642cb15498d8c6b2,
        0x3df4b239abeaeb3e, 0x6c909963ffa6e1d9, 0x334c0bee15193ea1, 0x21b5ca5020a9e5a2,
        1, 0, 0, 0,
        0xd0518ca77a2c3d14, 0xed68db3365e2123d, 0x532beb3ca8088ae0, 0x6231758c43d13752,
    ],
    [
        0xb6220f68c6e79bef, 0xd3967e2bada903ab, 0x822a19c6d610d445, 0x38e576301ff6cdd0,
        0xc4f8389eeb60eac0, 0xc1b26ef31699fa36, 0x2d2817dda4349109, 0x458fe689e31a2495,
        1, 0, 0, 0,
        0x885ab7b38a165294, 0x991e4d67cf1cc598, 0x6cc462f00774f7e6, 0x250df0cb741d8f5a,
    ],
    [
        0xd6652678641780db, 0x15c1ec1e3a78cac8, 0xef2233cd08790a7f, 0x372bec78d75011a0,
        0xb67ec97abdb538e8, 0x8476d3562aa88cef, 0xed3e2c2006ea0c0c, 0x32e9e47cf2f48612,
        1, 0, 0, 0,
        0x0a4518030cb981d2, 0x59a3a18597379463, 0xde3f87bac4be7a66, 0x7fbe85454d956845,
    ],
    [
        0xcc6a3ca9ec4d1c77, 0xbfb9fb199eb131f4, 0x5afee34e0a15dd67, 0x1aa3756aabcc3eb6,
        0x3dbdbe03a49159ae, 0xc26dd684758096ee, 0xb49af80e17347c63, 0x42333e27831add6e,
        1, 0, 0, 0,
        0x10d5248180ebc809, 0x8c89f3b2874cab83, 0x53cba54cba326263, 0x04a62d3684e33cda,
    ],
    [
        0xdd4f975ac0537dc5, 0xfbae91a4eed2e5e7, 0x0c4a36e20286bead, 0x38db16447d79d359,
        0x4ef0a0f714f96daa, 0xf1739845df2a857f, 0xe862ea71165bba7d, 0x1c48ccaed60ec12c,
        1, 0, 0, 0,
        0x4e6206b44d20fdde, 0x8e7c9c814a86f0bf, 0x00211b51129ede1f, 0x7ade2d06a404d4c9,
    ],
    [
        0xae7e76b273212fb7, 0x51d9a7ac7d6af218, 0xf90bae619c6a98e9, 0x176b78984cddfdde,
        0x61143f777db85852, 0xaad8536767ec1c58, 0x66e2a127abe12212, 0x7b5b93eda77443f3,
        1, 0, 0, 0,
        0x1fe21742f577c701, 0xd2432da323b9245e, 0x04fbac49d9028474, 0x57ea0e4a71ce9b10,
    ],
    [
        0x4052d3e9d38bb0f6, 0x2ea58d74f8109e8e, 0x73897ae528c6bc55, 0x042d154bf7b4a7bd,
        0xa182de120a71fc90, 0x7edc3245eca5d8ff, 0xf7ee9e3470ba20ca, 0x42d1831323e279f9,
        1, 0, 0, 0,
        0x37695eb884d1bb80, 0xc9be5bcb653eb33d, 0x1db4cae7f87e0622, 0x63a01f5ae70541da,
    ],
    [
        0x75116490c154e108, 0x4bf5874a9550d6e3, 0x0687b626b0120443, 0x1f8d28dd4f286a8d,
        0x9b55a9c43da98bb8, 0xc2c61609139446b0, 0xf41757fd45239f9b, 0x1ce82e2360367e06,
        1, 0, 0, 0,
        0x5cb05739dc41d103, 0x0a657eacf01fa963, 0x642530b3a24371c8, 0x7180d571f3d3d621,
    ],
    [
        0x6e406362e248e5e5, 0xe50b1c87d9e2546f, 0x9ae8356bf508c289, 0x613eb914c015076e,
        0x6bc949e920b97353, 0x2ef0ca4ca2880715, 0xaa18b254137d201a, 0x3edbaafcd8c41ef4,
        1, 0, 0, 0,
        0xb7c372de96e93ed8, 0xfcd91e083f3f7d18, 0x1f6550f28cc9c1b8, 0x6df1fdaf7b5628fa,
    ],
    [
        0x46cff8e193cb03a9, 0x1d77a8d48b048912, 0x4b3e3a405eff790a, 0x27bf43826bf0310b,
        0x4d4c67037514f2ea, 0xaa5869d6db0afa7b, 0xfbe8af9cfd782c3a, 0x16a24d749cc1d234,
        1, 0, 0, 0,
        0x0980f4d5153e9a29, 0xc30ad075d658f906, 0x555fab158f588c3e, 0x0639572e01bdcea1,
    ],
    [
        0x8df7714f57a675c2, 0x1dbd924083ffd9e8, 0xd417bdd9c3b5f5ae, 0x769a6a59746d7bea,
        0xb50748335ec5da25, 0x9af688d0421f2bdf, 0x590abb7dc3df4561, 0x22dc1267cfb2b41c,
        1, 0, 0, 0,
        0x4f42fecae053b13b, 0xfa93135dcabcfcd9, 0x66b52158f9e0055e, 0x0077f066a9ea212f,
    ],
    [
        0x63bff0b158c7224d, 0xdb942f765848e9df, 0x4219d25d41a2889c, 0x795734ee4fcc2419,
        0x4d7b76f7100669b5, 0x7af0e483e08484ea, 0x39d2e79907634a17, 0x756420ab5c71127d,
        1, 0, 0, 0,
        0xba327ee06554f6a3, 0xe17b5202eed840c6, 0xf7db732707d17340, 0x3793198bc4c4c1e4,
    ],
    [
        0x958e6896aefbcf46, 0x99fc59fdd2903f46, 0xaeb5911d8240971a, 0x644d12fc5e7fcac5,
        0xcc8cb572175216dc, 0xad2ee13fa8fc5209, 0x2e8124fea56f7aed, 0x173450789fcd4017,
        1, 0, 0, 0,
        0x8286bfe5a984463d, 0x75ca26b97874646d, 0x8571672dfa7a5ca2, 0x6f42d1c40d5e5520,
    ],
    [
        0xf5210679fd6c1110, 0x50e97a2ed687516b, 0xd4f351f5c8ad1fcc, 0x5deca767ef17b9e8,
        0x52599d67898aa396, 0x307ce5721c9e27c9, 0x708089989da016f3, 0x4ddf2207da12f700,
        1, 0, 0, 0,
        0xc97def380f6cd654, 0xec4f44940a39ce46, 0x8c1858d20b9040c1, 0x4e5f035a58983fec,
    ],
    [
        0xa59d4a689d9d2848, 0xd09fc7050ba8472d, 0x37a94bef93c97cac, 0x296dcb24cb3185d0,
        0x96d3e1dd8b060f7b, 0xc97cd09e57975bd9, 0x33fab728f15abcca, 0x0b17dc85a4acf738,
        1, 0, 0, 0,
        0xac1529b40066f882, 0xee6d2553cb26c1c9, 0x87ec39895e6cf97f, 0x30c5bad4740fdc55,
    ],
    [
        0xfde61c1a6cf1b93f, 0x6abb1002db7bcf15, 0x94f8e225b40dfc14, 0x408a3f1af2e77dfe,
        0x8b68fbcc0954e1c8, 0xc951dcdf04a61408, 0x79e7c7924f048e2e, 0x4f01ec38854c15a8,
        1, 0, 0, 0,
        0x21c6a1fb1668d299, 0x4a321890c48c46b5, 0x80f41066eea7c973, 0x1f3721d5a7831dd2,
    ],
    [
        0x624f90b8fafbbf07, 0x077c440e0a993a1e, 0x483e0a7c5ec52c49, 0x07d2d9234970cdc9,
        0x564c511f703f2295, 0xfba263866ee7831a, 0x3e07b9239f6ee7af, 0x6ac2190030c210ae,
        1, 0, 0, 0,
        0x164bff2b5daaa417, 0x88fb2cc5229b914b, 0x4e3e545473226a69, 0x6a8917ad98392f4d,
    ],
    [
        0x9795d93d58452873, 0xdedf11868fa93168, 0x0aa899b9b6887e40, 0x2982d55300208232,
        0xb2a26e980dc349b6, 0x4eca914425ee275d, 0x4cad0ea6bf45aada, 0x215e16ca44797862,
        1, 0, 0, 0,
        0xc74cde8802a6dec8, 0x019313e220e570ac, 0x57e98eb61f93018a, 0x759ee3cd9be57ac8,
    ],
    [
        0x3daaa8d0e7b42d1a, 0xc711fe1a343eeb5a, 0x6d2895b6276569e5, 0x1d8649515cb49e13,
        0xcbf6c26c1bb7fb6c, 0xf3b55f34afa5fc3f, 0x3e9ec3316cdc111a, 0x5b21e2f2978f343a,
        1, 0, 0, 0,
        0xe69c083c2e827437, 0x5dfaf17dd18549cc, 0x39728720fef091cd, 0x171d8d681ab45d88,
    ],
    [
        0x67213a23ee724a97, 0x37c5eafdd501b50a, 0x9cdbc04dbdcbdffd, 0x5460df4d60714793,
        0x9cdc16d71b9abcd8, 0xb3030273999739cb, 0x2487d34ab134b80b, 0x69dfc7004263ccb5,
        1, 0, 0, 0,
        0x697b8bb4cf5474e5, 0xd9a2d8754a429cc2, 0x9a07b3b0167a3b4a, 0x208b54aebd49637d,
    ],
    [
        0xe8175486598125bb, 0xaf5ed9dc4d2b44f7, 0xca15a0697ad23abe, 0x24623476f0af9f42,
        0x9329849b8c042687, 0x77dda15c22b2ecba, 0x194dcde6d33ff3af, 0x6aebe4a1a22d9e31,
        1, 0, 0, 0,
        0x359705c8ae4f1e03, 0x781dba3de7f45db5, 0xca8d59d346f8dff1, 0x28bdae94f16c122c,
    ],
    [
        0x2da0de6a651dd538, 0x4b2911681ebc07c9, 0x13117bac253b17f9, 0x64e507a02bfd8a84,
        0xe95fab2d1caa03a4, 0x590248a0507d845e, 0xa110afb612fbae36, 0x513ac992d72b463d,
        1, 0, 0, 0,
        0x29a7493a9c6166ad, 0x79217f7de15f6752, 0x1c4b302320a26404, 0x0aaec80320e9ff94,
    ],
    [
        0xfaeef894a654bf0e, 0xddbc0473b810689e, 0x230a22a5bb06a3cc, 0x47f3bd11324f6bee,
        0x18060e4285c492be, 0x1e2e2ef230e7c756, 0x32608dfc8d14eaa9, 0x7e05db9b3ff886bf,
        1, 0, 0, 0,
        0x02e9d712f0d1de7e, 0x50b69b92e558e9fb, 0x53204019a5acfee5, 0x4e1825367e1f1c3e,
    ],
    [
        0xe4fd87b3e55c5e0f, 0x85d42963a739a895, 0x2d656015ea2d1683, 0x4a6d22703a7045d0,
        0xa868d8cccf61776d, 0x37a87aa5defb119b, 0x1798e51f16ffa5b6, 0x4c58d7a8c6ded045,
        1, 0, 0, 0,
        0xe8cf95e9f69bf873, 0x148836327b92c26a, 0x4f58478584173c79, 0x26e271016b418847,
    ],
    [
        0xea7af283ba368eb5, 0xa90391f84c59b04c, 0x44d7798964598172, 0x3e22af70a5480972,
        0xe292b5b6519a2968, 0xdd4b59a36cc283db, 0xa197c5119fbbbd81, 0x689d8b7cda23b8de,
        1, 0, 0, 0,
        0x654c5806fe512f61, 0x57a60dfcb8933b0c, 0xa507ff1d8e3cc763, 0x17b031d3e5587958,
    ],
    [
        0x7431a302bc065a10, 0xb8fc40192d31ff63, 0x7b3a2ff0867c1b8b, 0x61a6ba2ca42d9d55,
        0x852b25579b63721d, 0x2e0255212a1bd3c8, 0xa2915a25cf0a8cab, 0x63d805f5a79f845e,
        1, 0, 0, 0,
        0xa8c999507e152816, 0x957240335bd9940b, 0xd269e7d79c9ee07b, 0x6f20c04f509dbb21,
    ],
    [
        0x884ec8621e8cb414, 0xd2168c346b9ba185, 0x88305f91c478efcf, 0x03d963eeae48556e,
        0xabec7a9ec1e7e183, 0x8d2099ef24c8633e, 0x8c639719d20fd9d4, 0x74b75cc839a944ad,
        1, 0, 0, 0,
        0xcf0602ce8d1e424d, 0x3cba6c323d8d772c, 0xcf58485e6597062a, 0x08596a58821d7aec,
    ],
    [
        0xf2152d6b93a58ae9, 0xa0599951fedb17e7, 0x44c58b103c88de09, 0x0f04da69e0202f7b,
        0x46f91070c800b8c4, 0xe8036587eade0383, 0x46e8e90019debf86, 0x1fbc1c9cd03c4cfd,
        1, 0, 0, 0,
        0x052557e493cef8fe, 0xe9e51d4cc12c9ed6, 0x74b8cb69f95733a5, 0x41d7a80b34727193,
    ],
    [
        0xb2a68cbc671a9cfe, 0xbe0190833766e809, 0xc6666aff11913b33, 0x797899e488353ed0,
        0xf985ce424b8909cc, 0xe86b5c846689265b, 0x3fe660f7070e6179, 0x5dd70a33ff94a84b,
        1, 0, 0, 0,
        0x5377e6e320b1beb0, 0x461dea13805573f6, 0xab36550a084667c1, 0x48ea70d558697ba1,
    ],
    [
        0x806be68379f77cdd, 0xdc4aa0dbaa242439, 0x0e4e7d57833eb7ff, 0x735b64bb87260651,
        0x77d287bc1a2bce2c, 0xec30c10af11df7d7, 0x36fcb65910859ca5, 0x384aaaee3ca7ba24,
        1, 0, 0, 0,
        0x8a1325052953d265, 0x8bf2cba58b8b2ad2, 0xe64f3354285f9ba3, 0x169ea362ca1ebb0a,
    ],
];

/// `[B', 3B', ..., 127B']` for `B' = [2^128]B`, with `Z = 1`.
#[rustfmt::skip]
static BASE128_ODD_MULTIPLES: [[u64; 16]; 64] = [
    [
        0xfc8047ae60b7e824, 0x98e685c9c2e723e5, 0x952d3984e14e29a0, 0x4c27afff3c45f32c,
        0x5bbabd114bf5a66b, 0x90d0be1e51a4c49e, 0x95f11eb626c29c3a, 0x5f2c99e6526dc87d,
        1, 0, 0, 0,
        0xe9e731c946f1338a, 0x147864826663ada9, 0xd4e1560007924b6a, 0x05a164fd0bf4602f,
    ],
    [
        0x3125ca89f193c7c7, 0xaea4bacc8756d94b, 0xa2fd3aa58b84f09b, 0x09c186afb833951c,
        0x1a349a357f7b062f, 0x02a82a6bbed54ff1, 0x934695b149864a1e, 0x6137b0746027b353,
        1, 0, 0, 0,
        0x8b1d62410e8ef362, 0x2ee83b43f388ad23, 0xede0546de38c20ae, 0x572c78d37f263d8a,
    ],
    [
        0x4919e3a2b12d4f17, 0xeda10ce5973c9955, 0xb813e0365c89c9e8, 0x4a2e1f96eee4e082,
        0x44d4b832ac846fc4, 0xdc229e517335a664, 0x8c951188bfdf0da8, 0x6c3f24822e185c5b,
        1, 0, 0, 0,
        0x52b0b2d34c797678, 0xe465a2b5bda47841, 0xb29b6cf120c82249, 0x2ddebaccef8dd261,
    ],
    [
        0x9370badc76ed5685, 0xb58e011afd275e11, 0xf1f2d57df9771ceb, 0x4b3702044575d3c0,
        0x482027acd289b820, 0xe36dcb0fafcce292, 0x2f427a80e5606aaf, 0x54333c50acf332f5,
        1, 0, 0, 0,
        0x3d4a71da3c1535e8, 0x3cf023a8404594ec, 0x8a4a79fb8004594f, 0x1d1cecdf260f81dc,
    ],
    [
        0xcbfb5c8de42dce20, 0x4e05ff679c81f96a, 0x9ec4431722f7616c, 0x3df71993fb635339,
        0x7bc722692a09fa98, 0x7b6caaaa1cf0010e, 0xc9164fb0641471ca, 0x7dcf8776aa205d39,
        1, 0, 0, 0,
        0xc250cb8d6970e9b5, 0x51a9118f148d8a02, 0x9f458a457d81de11, 0x46c49dfefb5be1ee,
    ],
    [
        0x116ae9ccb983430c, 0x9d9fc32646ccccca, 0x2ae0422c77d526e4, 0x4cf0cb74c7099d1e,
        0xb0bd07c5e74f9735, 0x58ba9a4e280b50a4, 0x85f4a2c049f289a9, 0x005df4e013e6461b,
        1, 0, 0, 0,
        0xb6468bbe81be9cc8, 0x915aa3f6c39437ba, 0x58573c491c0fe01e, 0x25e0b22e23b82e03,
    ],
    [
        0x7d814382c7d59993, 0x639e993d74eccc63, 0x4cfa98b2e49667af, 0x390414491821b00d,
        0x13cbfacbdff0df5a, 0x4980e855a5f06f32, 0x7770406917b7a7fc, 0x69710b1edcd36f1d,
        1, 0, 0, 0,
        0xbc404e273fb7ae6b, 0x92ccc35a4d5df515, 0xaa2672dfce92939a, 0x7eb4c6c7e917718e,
    ],
    [
        0xbcffd1ff333057e4, 0x4354fa2abb7efad5, 0x257f7f65adace168, 0x29b0c323e8469811,
        0xc77860930c75ce1c, 0x1c10ad6e6a1584ad, 0x8dc152a5d19b226c, 0x39a797181bd8a5cb,
        1, 0, 0, 0,
        0x33625af544a9a94b, 0x60c1b63abc581db6, 0x75813621a214af52, 0x4446f2c6af9232a9,
    ],
    [
        0x3816315d794ce449, 0x651c042e84636dee, 0x7bc15830a6ed16bd, 0x1974e7e5800281d7,
        0xe6f9c1891ec3a767, 0xbd8b23a1b085aa17, 0xe9f017017c0ab3b7, 0x67db93f67d13560b,
        1, 0, 0, 0,
        0x28a3f025c4691136, 0xe0161afd979634d9, 0x413452b9a029425c, 0x23eb7cd4eebf0e6e,
    ],
    [
        0xdae0ff28f075ee7e, 0xcef8c3876eb0d88c, 0xdae8a9115cd4046b, 0x600b8453481ee257,
        0x11515934bc57389e, 0x78d0d37cce77b2be, 0x4b8113f03493023c, 0x21508a9fe0f928b8,
        1, 0, 0, 0,
        0x15a00c0d234e543d, 0x5151143a1e0d6db8, 0x1499bc9013034406, 0x7592074d449c00b4,
    ],
    [
        0xa3415e9be7208ace, 0x7f0fed14cc9c92a2, 0x863d02144c922d27, 0x5b50fba2e89257c2,
        0x0cc0741c1b4afac2, 0xfd2cf739ae80bf85, 0x51e85d9830d93fef, 0x07db5a3a278a332c,
        1, 0, 0, 0,
        0x567ad7de83b55c0c, 0x7d4365a3eee918c9, 0x53b14d4c18496d21, 0x6c5286433031cf20,
    ],
    [
        0x2bf1cfd1253d942b, 0x90431d84246eb7d8, 0xd03a235233cc2db2, 0x7e29c4cfce35bcf5,
        0xdbdfcc71d58f8342, 0x44fbbeda3d0744fd, 0x87f96034a4ddc3bb, 0x17cee97f0668cd4d,
        1, 0, 0, 0,
        0x9fbeda18be212774, 0x0270e7c53d873743, 0xf0de52b13dcb13d1, 0x0bf2e522ee6d4837,
    ],
    [
        0x147cc5e94a5623bb, 0xd5461ed17183d2ec, 0xc74982358748b957, 0x2c4c2e96dee40eca,
        0x210bd6ba03bac92d, 0x783c06075bf9984c, 0xb97dc21cfc0c649e, 0x709978c301a76a76,
        1, 0, 0, 0,
        0x2d7fdb2a616f1b8e, 0xfc0fdc0c1924690b, 0x03d71211fde1e60d, 0x4f81abf131bf5960,
    ],
    [
        0x3932fd0caced13dd, 0xb0866f583175ef64, 0x1d71f309a8bb616d, 0x2688463651aab41a,
        0xdbc8cba6aa1231b0, 0x88fd180142e3ae68, 0x899696bbbe3f8253, 0x58b6b2c163ab526c,
        1, 0, 0, 0,
        0x261e702f8480929a, 0xeba216ce44da1149, 0xf4b715d52faefff7, 0x50253095d822d3a8,
    ],
    [
        0xab45e65aa0f67ff2, 0x111b00bcb0980dde, 0x0ff3dcc88ef31d64, 0x0956a6ab13dec2da,
        0xd1fb594081cfd845, 0xdaa6c47fd8511f11, 0x906449dc366ddf0d, 0x2c2f2068eff13a61,
        1, 0, 0, 0,
        0x074634234dbc6bb8, 0x8591d34a57c5550f, 0xac5e36227aed335c, 0x19c7b49b7a487c3e,
    ],
    [
        0xf7c216a18a426e84, 0xb2a4ece3f573f6ae, 0x62bd1e69ac5cb7b6, 0x5064c5ddc32b33ef,
        0xb3fc0ecd5a3b74df, 0x978c821575104033, 0x170f5590f2bdb180, 0x53e9015440523235,
        1, 0, 0, 0,
        0x5a4cfda7fca6d564, 0xfb4a0ea4aaa6ed15, 0x363c142ce5bd79ca, 0x40f84a16df67af38,
    ],
    [
        0xb990b2c235b83d56, 0x64d0552850487621, 0x94474fe28889c4d5, 0x3b1b6c8e05773834,
        0x9fa9097a7baa6565, 0xe1f9457c0e4321aa, 0x10d70a2b68f2fa20, 0x1cc8cfc5fbd2f59b,
        1, 0, 0, 0,
        0x542dd4328526c39c, 0xfae342bdb4896dfb, 0xed3725b6866a6e76, 0x53f3e776ae787da0,
    ],
    [
        0x55d5cc412a3464ec, 0x6ec4d29e35519348, 0xcba612dbb4a771b1, 0x09962aae5eeb3e03,
        0x37d62155718c0bb5, 0xd374cc3d8c6b3925, 0xf7c394d27777f797, 0x04e85c402858a112,
        1, 0, 0, 0,
        0x4ec94b912ba31e9f, 0xe65436bd6e0afa78, 0xf80e92396a15ddd1, 0x3aa3d02a659614f9,
    ],
    [
        0xac7d965847d19f58, 0xf1ff44fb9cd00731, 0x1ce7ca6c488b6d70, 0x04fa8815edebbd4f,
        0x3eb5281ca2627da6, 0xb03dcc920c8e1c41, 0x0b76d3d514178a08, 0x293334e3009f5f8a,
        1, 0, 0, 0,
        0xf9bb8d9a2c5c2eb0, 0x33a91709af55a1c2, 0xe89fd2fef0b1d148, 0x3e838cc58b8df939,
    ],
    [
        0x58076beac27b48f0, 0xe70f12efc684304c, 0x603c035a3152015b, 0x6ed323d73606abc6,
        0x92c523503b2b2ec5, 0x2acd82a243d51717, 0x4a706b970b0df76a, 0x2a4736a2d0866968,
        1, 0, 0, 0,
        0xf6670bb12fa5587b, 0x01d77510ef49553a, 0x44e5fd07e3201825, 0x5e3896329044e400,
    ],
    [
        0xd6fbe07aee1e7084, 0x79dd8724ba6e4f92, 0x07699f53c5d000ff, 0x18474a7d03e89380,
        0xa57430b1b6d28472, 0xe38bd3908f668f78, 0xac5e94bf56f2a569, 0x2b41dda0fbce512d,
        1, 0, 0, 0,
        0xc09fc4797ea47052, 0x49efdc20555913fd, 0xa0b2a1bb430c8c08, 0x75f524eafb5a693c,
    ],
    [
        0xeddaa33400b19e2c, 0x35bab6e8e8ff9b33, 0xeb7d5b1de24dbd1c, 0x1997f4b4f9d6fd4c,
        0x445b4e70813c4d6f, 0x5dd34a67e36231f7, 0x8b6b3faa5025c245, 0x3f031c0750f1a122,
        1, 0, 0, 0,
        0xbadbdddaeb12de83, 0x0d1594f5188c6da0, 0x1871dcee5cbbc105, 0x4b3f1629d26f4c25,
    ],
    [
        0xad67d94353f5fcd5, 0x4d422ca9a1251ccd, 0x47bc11c6d13b8d18, 0x7ac0fde9b67bcb23,
        0x0d67d7676576684b, 0x2499d2c228ac7ca8, 0x2e79eabcb4846eb7, 0x5105516f1c3cfbf5,
        1, 0, 0, 0,
        0x3bc6e884a4603f55, 0xaaec171b5ece4453, 0x491e2853efa18bd5, 0x0cefe646baed9ab0,
    ],
    [
        0x6b8b5e36d938d296, 0x2235ea2e9c7cef29, 0x9f474d3e3b094cf6, 0x59f25f3d6fb0f0cd,
        0xec86c3f5e797a902, 0x24c6c78c08b7c3a5, 0x76cc5d58ca9cfbd7, 0x3bbb86d576bf69bb,
        1, 0, 0, 0,
        0xe0c69ed1600d84a1, 0x03c341ee0d04e028, 0xce06ab2ddc49663e, 0x187f66282c64dbee,
    ],
    [
        0xc9e9f3a0a1dff859, 0x4af025673ef9e320, 0x7a953553a221c805, 0x3c9508986b67fdb7,
        0x2398329f63fc8d2d, 0xc9eca553a21c519a, 0xd60e01852ab4a044, 0x2a470a3f6a12aeb2,
        1, 0, 0, 0,
        0x8770bb582e430d1c, 0xc73840cdfbe42f3f, 0x28aec6c2920d43b2, 0x57f84b801f5af20a,
    ],
    [
        0xab75fea5b082ef86, 0xdeddf698e681e163, 0xdbf385239443a94a, 0x368e21350523fa13,
        0xdd8b015fed1ed5e4, 0x7c282f7488a711b1, 0x0fa101a3c1f67d86, 0x03355449d052818c,
        1, 0, 0, 0,
        0x5332f5c3be8cd29a, 0x80f576ee098ded74, 0x7b1729538e18cce4, 0x3b59e88682781e0c,
    ],
    [
        0x73f33d1a2546389a, 0xa4d18d76471ec980, 0x843837a073e141cf, 0x36d7abe12df90d9c,
        0x7de7a7ffc5f58c9f, 0xe2b07c48abe34526, 0x4847d6d5e31e6e85, 0x50a319f767fa3f00,
        1, 0, 0, 0,
        0xacb576ec0ebb315f, 0xd42632942c1304ad, 0xcfc3d505b5fc62e1, 0x704e3b590b1e2d25,
    ],
    [
        0x29d99ba4de56156c, 0xecb467d15faaa1f7, 0x753c65bbdd707fd3, 0x59344cd336c6d738,
        0xa888556997c606f9, 0x6dc4ac282f8bae42, 0x0ea5516f6040da14, 0x6d021a641b6c00b8,
        1, 0, 0, 0,
        0x101fb57fdbad201f, 0x0b7f803189f50a37, 0x2cf3d7c6e439ad9c, 0x242c3700f66ce346,
    ],
    [
        0x121dc4388f0101f0, 0x9efdb54ec098bc1e, 0x1448a43ea0f71dda, 0x2e2c56341bd1865d,
        0x22272723d0faeeb0, 0x3d057783e2225024, 0x3a91e45761513326, 0x5cb19acd672624e9,
        1, 0, 0, 0,
        0xa9296f5565aaec41, 0xfc0c4d4c2b96ca51, 0x87c43e6ce80a2b08, 0x0ea50c82d886c811,
    ],
    [
        0xa7962d55d422863f, 0x75f08cfe814d5d7f, 0xc9e730583d65801b, 0x05877fe948b312bb,
        0x9676fbafb8799c53, 0xf59543eaa964d372, 0x5ccb62c083a0785d, 0x59c894134e4670f6,
        1, 0, 0, 0,
        0x0319d3d5bfb90e45, 0x80edc409b38ed02c, 0x1b5bf8225f5ec651, 0x314e0c2475da90e3,
    ],
    [
        0xec31f958fb60175f, 0xc9a82692077a2ae4, 0x07345dfa2b7c6673, 0x5564bd36b7b2f98c,
        0xae2950d5b2e384b8, 0x04208ab9667a1e95, 0x5c17a24d3e8e530c, 0x0a974ad7308a2af7,
        1, 0, 0, 0,
        0x0925231155debe60, 0x50a3a7c2ec1038cb, 0x3f02d49b1be1c2bb, 0x77bb287c2b2cbfd0,
    ],
    [
        0x13941dc8a26e7a31, 0xda4aa82bd5189597, 0x199a1be4acdcbbbc, 0x5d8912cee1eba468,
        0x53ebfb6cdd0a4140, 0xf8c2f72301a86021, 0x96aaf7f3f99a056d, 0x0b4f4ac2cffe4046,
        1, 0, 0, 0,
        0x7ecb23a853caabb6, 0x4e719335e2e71961, 0x5f18a1e1db4ee70d, 0x55500ae8b9f087af,
    ],
    [
        0xe0104e8d0eab4408, 0x252a5db05996f47d, 0x545d303d04f794f1, 0x259f99554418c223,
        0xc109bcd424cbf866, 0x0558c664d544544e, 0x39eea0f0a98c1d77, 0x010f7b793cd6d1dd,
        1, 0, 0, 0,
        0xcde070aa0c20fb61, 0xe85d40af660a39ba, 0x38e2b547ad1cc930, 0x0b0cf8147441c9d8,
    ],
    [
        0xd4737d0da956fee0, 0x143cbb46c6a7eb11, 0x1fce3d924e86ba6a, 0x0ec32eb76c5a25dd,
        0x11dae84e2fcb6951, 0x3d4da19c983ac94c, 0xde8940265c9ec3a1, 0x5ff9d29327662fca,
        1, 0, 0, 0,
        0xb0da1254aa747166, 0xa3c847e855d845b2, 0x90b17fbda6ea84da, 0x24ccaaa956b8ceb8,
    ],
    [
        0x3ba13aafc1845943, 0x09bed19968b7a057, 0x2209effd22a34a05, 0x5b40edc5c9e3e125,
        0x5d7ecd999da0e5ab, 0xc62acadf69d9a5c2, 0x4436f7a997cacc29, 0x5be61f4c2ab1a3de,
        1, 0, 0, 0,
        0x9961d3e4b02c541c, 0x90b852dcdc1ca93a, 0xbb707f2d79290995, 0x51c09979b5c3365a,
    ],
    [
        0x59bc0d1c580332e9, 0x4d9d471436990188, 0xfc5225b496e4cff5, 0x2a21813c359bf64f,
        0xc376fe099318693c, 0xf81a96dbd0727dac, 0x96114b743a201bdc, 0x422ad2e1dbe08bac,
        1, 0, 0, 0,
        0xc7e84597eaf97a81, 0xab786a20fe1958d5, 0xbb16dd76995888a7, 0x69aa548bce80ddc5,
    ],
    [
        0x1fb4a107b7ad5db3, 0xd3833f9fa08e16f8, 0xbb2e7ab167e3771e, 0x53fe28e8594e0bed,
        0x5788bf1ca832190d, 0x462fd71aa872c360, 0x3a2294725562b236, 0x545a1c014ef5c82b,
        1, 0, 0, 0,
        0xcf1d3c11397e42a4, 0x1bde15f775c3ad7c, 0x3acc51c611b306ac, 0x3afdba3ff32062d3,
    ],
    [
        0x81a90c1bd19eaae4, 0x4cac8ee825840873, 0x490b85c646128d6d, 0x0225a6dac51c18c0,
        0x2c1526b1c6a24791, 0x5d12c58ffa44199a, 0x66a55e09e451f423, 0x37b8bb533cb35c5b,
        1, 0, 0, 0,
        0x62869f361b90cf04, 0xfc2c00bf29f7e4bc, 0x4ec5ca7f31e938fd, 0x0c333528c89b3fc9,
    ],
    [
        0xa4737b5ec1561bcf, 0x94e293a37e745ce5, 0x25e61baab99ee37d, 0x1ebdfd84ab220a4d,
        0xf0b16e5a47dab3d7, 0x77389aab48c0adba, 0xf14a165429e7ce99, 0x5bbd47f216a92350,
        1, 0, 0, 0,
        0xfb82fa13879e3aa2, 0x9b529255e69c9df0, 0xdd85a0cd4a79b14c, 0x0060aadaad8f4c9d,
    ],
    [
        0xf608db596ef185bd, 0xe6ddb9f8163439a0, 0x4987017492a0cf5c, 0x5bafd1489869aff2,
        0xf43b4ac2b9f57f18, 0x02f455f02c58b6d6, 0xcaf3ca3fd914b8f6, 0x1720ee2ca4cdfcce,
        1, 0, 0, 0,
        0x819c1e79e94cded1, 0x36aac9d8c3427eb6, 0x87025339e9026012, 0x6817009ef1125b5d,
    ],
    [
        0xcdd71117bfe24182, 0x87fcacb080c08c4f, 0x4b47fc4e5d07eb06, 0x1d8a9586a3f7387e,
        0xcaac1c4e8db2c436, 0xb0dbfd9a059281d1, 0xba25a2d1ff1cb1a6, 0x61f524e4cd7caf50,
        1, 0, 0, 0,
        0x2bfb03d0e717f496, 0x4b64b4f60ded16d1, 0xaf0b91ccf2e89e2d, 0x598a698aadb30714,
    ],
    [
        0x174fcffb4b59b274, 0x9af3287d80e685a2, 0xd64ebc75ae73d6de, 0x3b2d15befd65ca61,
        0x8a4a50499cc7cdd4, 0x409dd84d74e95435, 0x89d06ef1cb674172, 0x3683113815403aa9,
        1, 0, 0, 0,
        0xcf33a09cc9c17d71, 0x251f06986adae3f5, 0x6b4d291cdae11345, 0x59c14dd7c2738ff9,
    ],
    [
        0x1ea0254a759b4e85, 0xbe472c99360acce3, 0x95200d81f0b8552f, 0x7558377ddb901dfe,
        0xd26abadda4ab7bd8, 0xfd7c1fa8d85421b7, 0x0d9ad4c6c1085d64, 0x24094c2c9dcfa2b4,
        1, 0, 0, 0,
        0x50c2383528697b15, 0x1a3066de9811b041, 0x49699e1063f835a4, 0x2f4654f8a83bebb8,
    ],
    [
        0xd7ac258c748550b3, 0x11b74942313e7c3d, 0x9c4b062bf13ad824, 0x58b53a253bb865f8,
        0x29b031a296d8aac6, 0x3f419a1208091d64, 0x263f92669ca0f566, 0x267ad28821f416b5,
        1, 0, 0, 0,
        0xfef7f76f0d582fec, 0x186b1b50098d08da, 0xc692db8906ff4689, 0x2575ca7a6c244c46,
    ],
    [
        0xe8e7c8211e4b8429, 0xca73029420b56e6b, 0x01771febc39aad6c, 0x34cbb64bb1ac1fa5,
        0x82326e3e989da0a5, 0x2dc100be065c2347, 0xc00b6bfe5b244c47, 0x1a068c3dee089716,
        1, 0, 0, 0,
        0x6c2a3c1db361c4fb, 0xa760fbbdc0f6db06, 0xab7a020c97decc29, 0x687a7ab64ff3c87e,
    ],
    [
        0xa47c3a43811b101f, 0xf45ecb19663b7a17, 0xf73343a418b365dc, 0x748bf4d819f83189,
        0xe0c931210b37b057, 0x9c0f4880f45374e6, 0x60be5e71b9a62748, 0x092126e19175a289,
        1, 0, 0, 0,
        0xfdff943f189bcb0c, 0x7d9e401f39a81009, 0xd3d3e6d686092110, 0x34e80bf485144916,
    ],
    [
        0x27d2d3bd3be74053, 0xa0732622a4ba8bc9, 0xef565e3f43518b53, 0x2c2b281a6ab48c9c,
        0x6780157aee8e46ee, 0x7505a1bbb0d145b7, 0x0654c8eab69dd056, 0x3b301220a50fd8b8,
        1, 0, 0, 0,
        0xea3d3e762749e6c3, 0x6298274eb5580938, 0xe30bc778dc6e188e, 0x301f606b42e99044,
    ],
    [
        0xaf658794c09a6288, 0x7f980b6db7a1fe68, 0xf01ca50bf330a9cb, 0x3388f6010c175add,
        0xb14d61b7b5b4535f, 0xc532e4ba3f3b1932, 0xbac335af14002c42, 0x3e6edf5c7b400321,
        1, 0, 0, 0,
        0x653c30443abeef8f, 0x58ab2fbe412b816d, 0xa84e47eb8ce02982, 0x017022114423713c,
    ],
    [
        0x63233499ea4991fb, 0xb9b7f6b29655b090, 0xe1d39c558554748f, 0x3965ad4b28429b87,
        0xee6028f5e61a9826, 0x2bd3e4734947eba6, 0x8dec124f4a0b7cce, 0x7b590600dde6d9a5,
        1, 0, 0, 0,
        0xbf41ce00190915db, 0x9940270cc19656af, 0x9226a8c276892411, 0x663fd99a7aa90f34,
    ],
    [
        0x324bab467dc33cc6, 0x2b5f7675a8a111ad, 0xbf42265c4be80824, 0x5a921616a30d718a,
        0x702e978b23bb4943, 0xf5d5433733a9b8af, 0x7191497e9e30f837, 0x4f81a933bd2711db,
        1, 0, 0, 0,
        0xafc256819c470c2f, 0xac1cc724984e34e1, 0x60a3c007d8be512e, 0x200f8d91e4039fa2,
    ],
    [
        0x350d2c17969d024c, 0xee07398c41c27604, 0xc4381f120c7b4b84, 0x7fcfd10800e19439,
        0x09c0f9d276798277, 0xac6094f01f44c5b9, 0xfe7d3bbbb593caa2, 0x0816c238e3a14f6b,
        1, 0, 0, 0,
        0x1ddcbf854eeac5e9, 0xdac9223c7b661d7c, 0xde12182274351585, 0x7bb4b153fbf8b268,
    ],
    [
        0x2137ac403013e43e, 0x931615fee2b7d4a5, 0x1532c4190c2c806e, 0x2ddfbdfd1c179d0e,
        0x1959f2a9fcf5fe2b, 0x46c1cdac2e08b030, 0x66f96022f8f64de2, 0x000d32d294ccfcae,
        1, 0, 0, 0,
        0x600addd6a0f8027b, 0xd8af0c70d659a575, 0xee0d4ab0b9872796, 0x4b0c9977bf8b5ad0,
    ],
    [
        0xaf5da89e2d6bbeba, 0x40c6cd331a46dc91, 0x0d0a54c72c598aa9, 0x56c0ee7ae8fd5a27,
        0x7149863c7c7dec07, 0xa86df639b554ea2f, 0x80cff800e5e8a2f6, 0x100d6fedbfbc5e11,
        1, 0, 0, 0,
        0x167b7cffab5a9534, 0x266d741dd4618307, 0x40088628d5812b65, 0x36f72dab6314f4f4,
    ],
    [
        0xbe2439edcbdf3445, 0x246993ded471319b, 0x8d6cf8b765ae977a, 0x707a744a1e0c418d,
        0x15c7aaedf95423a9, 0xc07afc7033c433c9, 0x7e7baa3c94b9a3df, 0x39ae715837d139c9,
        1, 0, 0, 0,
        0x8d54476963fca74c, 0x995c1bafbd7f94ca, 0x2224dfa954c97f57, 0x317873630b5b314b,
    ],
    [
        0x1eabd5437663f4b2, 0x8792eea951acc307, 0xce5924745c82a169, 0x5bdabdc566ef42f5,
        0xed334fadf4915d3f, 0x40a5247c981a3ed3, 0xbf3495d303ae4356, 0x4cc22a3f4eb10a08,
        1, 0, 0, 0,
        0x96eff1f1e2564869, 0x71aff0348d804fc2, 0x0d82f1bf66332b63, 0x21b3416ebbe71041,
    ],
    [
        0xb40565bec9fb3684, 0xd29a78c7afafeb64, 0x5f62115a554eaed5, 0x385039e258d2180d,
        0x4e88300334f1913b, 0x3f0127d26b18f0cf, 0x2e2b81d6999562ea, 0x798ce64520b5f872,
        1, 0, 0, 0,
        0xacf1875a93d64fe5, 0x0850f6cceec4620d, 0x4053db1011b8e735, 0x4eb1ed1da9c4f461,
    ],
    [
        0xfd801ab3a3eea302, 0x52005a3f340899a9, 0xed1404d8ae7078cd, 0x419a4e40176e1b44,
        0xafc3e8d7270126dd, 0xc30126c6aeda8c57, 0x661a6c4b39dd5098, 0x49c7a0c73567524e,
        1, 0, 0, 0,
        0xddf99c9ea6a4c166, 0x93365846e4932f56, 0x57275273f7e990c0, 0x397de751116d92ef,
    ],
    [
        0x227f6c5641df0c48, 0x82b0c8709e11394e, 0xc838cc9b9d82ecd9, 0x0c85304298e3581c,
        0xc4699fcbd48cd57d, 0x9eb7dc69d1282805, 0x19966fdcc6af0b90, 0x633de03795e44bd8,
        1, 0, 0, 0,
        0x1dd0760b59e724a2, 0x17e99af6177207a0, 0xf14918e2ade73e97, 0x3f776a0aac6eee3f,
    ],
    [
        0x0951ae27a6c4e279, 0x153b38f477acb230, 0x9e3fc52e75bd6e1e, 0x50e41bbfbeda41f2,
        0x419dfb6a1d6076f4, 0x08b39e0b8c838a4a, 0x0a0d756461890021, 0x6945b58be02a1e41,
        1, 0, 0, 0,
        0x222fbd1df79674fd, 0x5b086a3e19a22a03, 0x88bc155e5f041258, 0x4a2ecc60120763f2,
    ],
    [
        0x54bb9738d7f1f817, 0x887ad89c9fd0bda0, 0x9910c2b0bff3a5d4, 0x04e2901fc0059f05,
        0xbe1b11eb49bb8277, 0x0b1c1fab97c67eef, 0x923d363000798855, 0x6cc0fc50ebebbb93,
        1, 0, 0, 0,
        0x7419f9f8483ff967, 0x10fd2bb2cbea9305, 0xa873ebce59b2d27b, 0x36cbaea49788a1a9,
    ],
    [
        0x6f67f94c6cdded0b, 0xa5319d3341658350, 0x0901c3c851904b43, 0x655bb97cdd6cd324,
        0xf8538462412b76da, 0x670ed0112f89748d, 0x8ad9be7e69cfb3ee, 0x53f9ea987f11574b,
        1, 0, 0, 0,
        0x673f47097949ae7d, 0xe2acf2b0b498ccf5, 0x5ea52853ddcfbd21, 0x1854ad663f5597c2,
    ],
    [
        0x5ed3c954b0f812de, 0x0d22deb53c46ae89, 0x3db64448d2381a4f, 0x081543e51113d4b4,
        0x43cc5b50d3bd1a71, 0xd4115e8cb2379430, 0x2b2c82be7a64d1c8, 0x02ee5a73d9388848,
        1, 0, 0, 0,
        0xaa95e7c708361285, 0x6a0215bbc1df3c4b, 0x2c4681563bc8b687, 0x0b3ea030c71167b9,
    ],
    [
        0xc04c105f71251944, 0x5f5dd87ac7995f3b, 0xdde6882e5035ed07, 0x405bce70d5b62985,
        0x4bec143fdff284ce, 0x609db300bd14213e, 0xb9366d3fbd684d44, 0x46b08cd88c886ea5,
        1, 0, 0, 0,
        0xf8b098ebd774a6c1, 0xf827e4e07ddde8bd, 0x23aeb7405554acde, 0x3ad8d3051936383a,
    ],
    [
        0x9fa2e1537f005fb2, 0x28520543f84b3a0f, 0xd23cb14ec738a027, 0x0409279cd536b4eb,
        0x31f0d0e5b619c590, 0xf3814fbfcc19b616, 0x31f1e557054743d5, 0x29f4912aeaaeaab7,
        1, 0, 0, 0,
        0x4cd1571a264d8123, 0xde4214ad20581b9d, 0x68c5daf049a1944a, 0x233a02154a4a444c,
    ],
];

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::{bignum_mul_p25519, edwards25519_scalarmulbase};

    /// A xorshift generator, for reproducible inputs.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        /// A random number below 2^bits.
        fn words(&mut self, bits: u32) -> [u64; 4] {
            core::array::from_fn(|i| match (bits as usize).saturating_sub(64 * i) {
                0 => 0,
                b if b >= 64 => self.next(),
                b => self.next() >> (64 - b),
            })
        }
    }

    fn mul(x: &[u64; 4], y: &[u64; 4]) -> [u64; 4] {
        let mut z = [0; 4];
        bignum_mul_p25519(&mut z, x, y);
        z
    }

    /// `[scalar]B` in extended coordinates.
    fn base_mul(scalar: &[u64; 4]) -> [u64; 16] {
        let mut affine = [0; 8];
        edwards25519_scalarmulbase(&mut affine, scalar);
        let (x, y) = (
            affine[..4].try_into().unwrap(),
            affine[4..].try_into().unwrap(),
        );
        let mut p = IDENTITY;
        p[..8].copy_from_slice(&affine);
        p[12..].copy_from_slice(&mul(x, y));
        p
    }

    fn add(p: &[u64; 16], q: &[u64; 16]) -> [u64; 16] {
        let mut r = [0; 16];
        edwards25519_epadd(&mut r, p, q);
        r
    }

    /// `[scalar]point` by double-and-add from the top bit.
    fn point_mul(scalar: &[u64; 4], point: &[u64; 16]) -> [u64; 16] {
        let mut acc = IDENTITY;
        for i in (0..256).rev() {
            let doubled = acc;
            edwards25519_epdouble(&mut acc, projective(&doubled));
            if scalar[i / 64] >> (i % 64) & 1 == 1 {
                acc = add(&acc, point);
            }
        }
        acc
    }

    /// Whether two projective points are the same: `X1 Z2 = X2 Z1` and
    /// `Y1 Z2 = Y2 Z1`.
    fn same(p: &[u64; 12], q: &[u64; 12]) -> bool {
        let c = |p: &[u64; 12], i: usize| -> [u64; 4] { p[4 * i..4 * i + 4].try_into().unwrap() };
        mul(&c(p, 0), &c(q, 2)) == mul(&c(q, 0), &c(p, 2))
            && mul(&c(p, 1), &c(q, 2)) == mul(&c(q, 1), &c(p, 2))
    }

    #[test]
    fn base_tables() {
        for (table, scalar) in [
            (&BASE_ODD_MULTIPLES, [1, 0, 0, 0]),
            (&BASE128_ODD_MULTIPLES, [0, 0, 1, 0]),
        ] {
            for (i, entry) in table.iter().enumerate() {
                let multiple = point_mul(&[2 * i as u64 + 1, 0, 0, 0], &base_mul(&scalar));
                assert!(same(projective(entry), projective(&multiple)), "{i}");
                // Z = 1, so X and Y are affine, and T = XY.
                assert_eq!(entry[8..12], [1, 0, 0, 0]);
                let (x, y) = (
                    entry[..4].try_into().unwrap(),
                    entry[4..8].try_into().unwrap(),
                );
                assert_eq!(entry[12..], mul(x, y));
            }
        }
    }

    #[test]
    fn matches_double_and_add() {
        let mut rng = Rng(0x243f_6a88_85a3_08d3);
        // Scalars of every length the loop sees, and the edges of each
        // table's digits.
        let edges = [
            [0; 4],
            [1, 0, 0, 0],
            [u64::MAX, u64::MAX, 0, 0],
            [0, 0, 1, 0],
            [u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1],
        ];
        // A point of order 8, so torsion components are exercised too:
        // (sqrt(-1) * ..., ...) is awkward to write, so take a random
        // point plus the order-2 point (0, -1) instead.
        let order2 = {
            let mut p = IDENTITY;
            p[4..8].copy_from_slice(&[
                0xffff_ffff_ffff_ffec,
                u64::MAX,
                u64::MAX,
                0x7fff_ffff_ffff_ffff,
            ]);
            p
        };
        for round in 0..48 {
            let p0 = base_mul(&rng.words(253));
            let p1 = match round % 2 {
                0 => base_mul(&rng.words(253)),
                _ => add(&base_mul(&rng.words(253)), &order2),
            };
            let bits = [0, 1, 64, 127, 128, 129, 200, 255][round % 8];
            let mut cases = vec![(rng.words(253), [rng.words(bits), rng.words(128)])];
            for edge in edges {
                cases.push((edge, [rng.words(128), edge]));
                cases.push((rng.words(253), [edge, edge]));
            }
            for (base, scalars) in cases {
                let mut got = [0; 12];
                edwards25519_msm(&mut got, &base, &scalars, &[p0, p1]);
                let want = add(
                    &add(&base_mul(&base), &point_mul(&scalars[0], &p0)),
                    &point_mul(&scalars[1], &p1),
                );
                assert!(same(&got, projective(&want)), "{base:x?} {scalars:x?}");
            }
        }
    }

    #[test]
    fn non_adjacent_form_sums_to_the_scalar() {
        let mut rng = Rng(0x1319_8a2e_0370_7344);
        for w in [5, 8] {
            for _ in 0..256 {
                let x = rng.words(255);
                let naf = non_adjacent_form(&x, w);
                // sum(naf[i] 2^i), in 2^256 wrapping arithmetic.
                let mut sum = [0u64; 4];
                for (i, &digit) in naf.iter().enumerate().rev() {
                    let mut carry = 0;
                    for word in &mut sum {
                        let next = *word >> 63;
                        *word = *word << 1 | carry;
                        carry = next;
                    }
                    let add = (digit as i64) as u64;
                    let mut carry = 0u64;
                    for (j, word) in sum.iter_mut().enumerate() {
                        let addend = if j == 0 {
                            add
                        } else {
                            (digit >> 7) as i64 as u64
                        };
                        let (s, c1) = word.overflowing_add(addend);
                        let (s, c2) = s.overflowing_add(carry);
                        *word = s;
                        carry = u64::from(c1 | c2);
                    }
                    assert!(
                        digit == 0 || (digit & 1 == 1 && digit.unsigned_abs() < 1 << (w - 1)),
                        "{i}"
                    );
                }
                assert_eq!(sum, x);
            }
        }
    }
}
