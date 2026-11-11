// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// Calls an `extern` assembly routine, through `abi`'s trampoline in tests,
/// which checks it preserves what its ABI says it must.
#[cfg(all(
    test,
    any(
        rind_backend = "x86_64",
        rind_backend = "aarch64",
        rind_backend = "arm"
    )
))]
macro_rules! asm_call {
    (unsafe extern $abi:tt $f:tt($($arg:expr),* $(,)?)) => {
        $crate::low::abi::call!(unsafe extern $abi $f, $($arg),*)
    };
}

#[cfg(all(
    not(test),
    any(
        rind_backend = "x86_64",
        rind_backend = "aarch64",
        rind_backend = "arm"
    )
))]
macro_rules! asm_call {
    (unsafe extern $abi:tt $f:tt($($arg:expr),* $(,)?)) => {
        $f($($arg),*)
    };
}

#[cfg(any(rind_backend = "x86_64", rind_backend = "aarch64"))]
#[macro_use]
mod macros;

pub(crate) mod ct;
#[cfg(test)]
pub(crate) mod ct_binsec;

#[cfg(rind_vartime_planted)]
mod vartime_planted;

#[cfg(doc)]
pub mod inline_assembly_safety;

mod generic {
    // The portable backend's RSA arithmetic, which armv7 shares, also built
    // in tests elsewhere to check it against s2n-bignum.
    pub(crate) mod argon2;
    #[cfg(any(rind_backend = "arm", rind_backend = "portable", test))]
    pub(crate) mod bignum;
    pub(crate) mod blake2b;
    pub(super) mod blockwise;
    pub(crate) mod chacha20;
    // Where no one-pass routine runs, and in aarch64 tests to check it
    // against.
    #[cfg(any(not(rind_backend = "aarch64"), test))]
    pub(crate) mod chacha20poly1305;
    pub(super) mod ct_copy;
    pub(super) mod ct_equal;
    pub(super) mod ctr;
    #[cfg(test)]
    pub(crate) mod ghash;
    // Every target's MD5: no CPU has instructions for it.
    pub(super) mod md5;
    pub(crate) mod mlkem;
    #[cfg(not(rind_backend = "x86_64"))]
    pub(crate) mod mlkem768;
    // ML-KEM arithmetic for the portable backend and x86_64 CPUs without
    // AVX2.
    #[cfg(not(rind_backend = "aarch64"))]
    pub(crate) mod mlkem_poly;
    // The portable backend's group orders, picked from by modulus.
    #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
    pub(crate) mod order;
    // The portable backend's P-256, P-384, and P-521, also built in tests
    // elsewhere to check them against s2n-bignum.
    #[cfg(any(rind_backend = "arm", rind_backend = "portable", test))]
    pub(crate) mod p256;
    #[cfg(any(rind_backend = "arm", rind_backend = "portable", test))]
    pub(crate) mod p384;
    #[cfg(any(rind_backend = "arm", rind_backend = "portable", test))]
    pub(crate) mod p521;
    // x86_64's separate-pass Poly1305 and the 64-bit portable backend's.
    // aarch64 runs Poly1305 only in aws-lc's one-pass ChaCha20-Poly1305,
    // whose tests check it against this.
    #[cfg(any(
        rind_backend = "x86_64",
        all(rind_backend = "portable", target_pointer_width = "64"),
        all(rind_backend = "aarch64", test)
    ))]
    pub(crate) mod poly1305;
    pub(super) mod reuse_cache;
    // The portable backend's SHA1 and SHA256, also built in x86_64 tests to
    // check the vector paths against.
    #[cfg(any(
        rind_backend = "arm",
        rind_backend = "portable",
        all(test, rind_backend = "x86_64")
    ))]
    pub(super) mod sha1;
    #[cfg(any(rind_backend = "arm", all(test, rind_backend = "x86_64")))]
    pub(super) mod sha256;
    pub(super) mod zeroise;
}

pub(crate) mod cpu;
mod entry;
mod posint;

#[cfg(rind_backend = "aarch64")]
pub(crate) use aarch64::argon2::{Fill as Argon2Fill, compress as argon2_compress};
pub(crate) use entry::Entry;
pub(crate) use generic::argon2;
#[cfg(not(any(rind_backend = "x86_64", rind_backend = "aarch64")))]
pub(crate) use generic::argon2::{Fill as Argon2Fill, compress_selected as argon2_compress};
pub(crate) use generic::blake2b;
pub(crate) use generic::blockwise::{Blockwise, UpdateBlocks, pad, sha256_digest, split_tail};
pub(crate) use generic::chacha20::{chacha20_block, hchacha20};
pub(crate) use generic::ct_copy::{ct_copy, ct_select_i16};
pub(crate) use generic::ct_equal::ct_equal;
#[cfg(all(test, any(rind_backend = "arm", rind_backend = "portable")))]
pub(crate) use generic::ghash::gcm_model;
pub(crate) use generic::md5::md5_compress_blocks;
#[cfg(any(rind_backend = "x86_64", all(rind_backend = "aarch64", test)))]
pub(crate) use generic::poly1305;
pub(crate) use generic::reuse_cache::ReuseCache;
pub(crate) use generic::zeroise::{Zeroable, ZeroableRef, zeroise, zeroise_value};
#[cfg(rind_backend = "portable")]
pub(crate) use portable::poly1305;
pub(crate) use posint::{ModExp, PosInt, SecretPosInt};
#[cfg(rind_backend = "x86_64")]
pub(crate) use x86_64::argon2::{Fill as Argon2Fill, compress as argon2_compress};

#[cfg(all(test, any(rind_backend = "x86_64", rind_backend = "aarch64")))]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests;

#[cfg(all(
    test,
    any(
        rind_backend = "x86_64",
        rind_backend = "aarch64",
        rind_backend = "arm"
    )
))]
#[cfg_attr(coverage_nightly, coverage(off))]
pub(crate) mod abi;

// A bounds test, not a constant-time one: valgrind does not fault guard
// pages on every target, so ctgrind builds leave it out.
#[cfg(all(test, unix, not(feature = "__ctgrind")))]
#[cfg_attr(coverage_nightly, coverage(off))]
mod guard_pages;

// The portable backend, which armv7 builds on, and what both run alike.
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
mod portable;
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
pub(crate) use generic::{
    bignum::{
        bignum_add, bignum_bitsize, bignum_cmp_lt, bignum_coprime, bignum_copy_row_from_table,
        bignum_ctz, bignum_digitsize, bignum_modsub, bignum_montifier, bignum_montredc, bignum_mul,
        bignum_negmodinv, bignum_optsub,
    },
    chacha20poly1305,
    mlkem::{mlkem_compress_d4, mlkem_compress_d10, mlkem_frombytes, mlkem_unpack},
    mlkem_poly::{
        mlkem_basemul_k3, mlkem_intt, mlkem_mulcache_compute, mlkem_ntt, mlkem_reduce,
        mlkem_rej_uniform_vartime, mlkem_tobytes, mlkem_tomont,
    },
    mlkem768::mlkem768_sample_poly_ntt_8x,
    // libcrux's P-256 runs 64-bit limbs and recomputes the nonce's point to
    // sign, it exports P-384 only as ECDH, and it has no P-521, so rind
    // composes their arithmetic itself.
    order::{bignum_demont, bignum_modadd, bignum_modinv, bignum_montmul},
    p256::{
        bignum_add_p256, bignum_demont_p256, bignum_inv_p256, bignum_mod_n256, bignum_montmul_p256,
        bignum_montsqr_p256, bignum_neg_p256, bignum_tomont_p256, p256_montjadd, p256_montjdouble,
        p256_montjmixadd, p256_montjscalarmul, p256_scalarmulbase,
    },
    p384::{
        bignum_add_p384, bignum_aff_point_select_p384, bignum_demont_p384, bignum_inv_p384,
        bignum_jac_point_select_p384, bignum_mod_n384, bignum_montmul_p384, bignum_montsqr_p384,
        bignum_mux, bignum_neg_p384, bignum_tomont_p384, p384_montjadd, p384_montjdouble,
        p384_montjmixadd,
    },
    p521::{
        bignum_add_p521, bignum_aff_point_select_p521, bignum_inv_p521, bignum_mod_n521,
        bignum_mul_p521, bignum_neg_p521, bignum_sqr_p521, p521_jadd, p521_jdouble, p521_jmixadd,
        p521_jscalarmul,
    },
};
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
pub(crate) use portable::{
    bignum_eq::bignum_eq, curve25519::curve25519_x25519base, ghash_nohw::NohwTable,
};

// Declared outside `cfg_if!`, which cargo-mutants cannot see into.
#[cfg(rind_backend = "aarch64")]
mod aarch64;
#[cfg(rind_backend = "arm")]
mod arm;
#[cfg(rind_backend = "x86_64")]
mod x86_64;

cfg_if::cfg_if! {
    if #[cfg(rind_backend = "x86_64")] {
        pub(in crate::low) use x86_64::cpu::{enter_cpu_state, zero_bytes, ct_compare_bytes, ct_compare_16, leave_cpu_state, missing_cpu_feature};
        pub(crate) use x86_64::chacha20;
        pub(crate) use x86_64::chacha20poly1305;
        pub(crate) use x86_64::aes::{AesDecKey, AesKey};
        pub(crate) use x86_64::aes_cbc;
        pub(crate) use x86_64::aes_ctr;
        pub(crate) use x86_64::aes_gcm;
        #[cfg(test)]
        pub(crate) use x86_64::ct_sde;
        pub(crate) use x86_64::bignum_add::bignum_add;
        pub(crate) use x86_64::bignum_add_p256::bignum_add_p256;
        pub(crate) use x86_64::bignum_add_p384::bignum_add_p384;
        pub(crate) use x86_64::bignum_add_p521::bignum_add_p521;
        pub(crate) use x86_64::bignum_bitsize::bignum_bitsize;
        pub(crate) use x86_64::bignum_cmp_lt::bignum_cmp_lt;
        pub(crate) use x86_64::bignum_coprime::bignum_coprime;
        #[cfg(test)]
        pub(crate) use x86_64::bignum_copy_row_from_table::bignum_copy_row_from_table;
        pub(crate) use x86_64::bignum_ctz::bignum_ctz;
        pub(crate) use x86_64::bignum_demont::bignum_demont;
        pub(crate) use x86_64::bignum_point_select::{bignum_aff_point_select_p384, bignum_aff_point_select_p521};
        pub(crate) use x86_64::adx_mux::bignum_demont_p256;
        pub(crate) use x86_64::adx_mux::bignum_demont_p384;
        pub(crate) use x86_64::bignum_digitsize::bignum_digitsize;
        pub(crate) use x86_64::bignum_eq::bignum_eq;
        pub(crate) use x86_64::bignum_inv_p256::bignum_inv_p256;
        pub(crate) use x86_64::bignum_inv_p384::bignum_inv_p384;
        pub(crate) use x86_64::bignum_inv_p521::bignum_inv_p521;
        pub(crate) use x86_64::adx_mux::bignum_madd_n25519;
        pub(crate) use x86_64::bignum_mod_n25519::bignum_mod_n25519;
        pub(crate) use x86_64::bignum_mod_n256::bignum_mod_n256;
        pub(crate) use x86_64::bignum_mod_n384::bignum_mod_n384;
        pub(crate) use x86_64::adx_mux::bignum_mod_n521;
        pub(crate) use x86_64::bignum_modadd::bignum_modadd;
        pub(crate) use x86_64::bignum_modinv::bignum_modinv;
        pub(crate) use x86_64::bignum_modsub::bignum_modsub;
        pub(crate) use x86_64::bignum_montifier::bignum_montifier;
        pub(crate) use x86_64::bignum_montmul::bignum_montmul;
        pub(crate) use x86_64::adx_mux::bignum_montmul_p256;
        pub(crate) use x86_64::adx_mux::bignum_montmul_p384;
        pub(crate) use x86_64::bignum_montredc::bignum_montredc;
        pub(crate) use x86_64::adx_mux::bignum_montsqr_p256;
        pub(crate) use x86_64::adx_mux::bignum_montsqr_p384;
        pub(crate) use x86_64::bignum_mul::bignum_mul;
        pub(crate) use x86_64::adx_mux::bignum_mul_p521;
        pub(crate) use x86_64::bignum_mux::bignum_mux;
        pub(crate) use x86_64::bignum_neg_p25519::bignum_neg_p25519;
        pub(crate) use x86_64::bignum_neg_p256::bignum_neg_p256;
        pub(crate) use x86_64::bignum_neg_p384::bignum_neg_p384;
        pub(crate) use x86_64::bignum_neg_p521::bignum_neg_p521;
        pub(crate) use x86_64::bignum_negmodinv::bignum_negmodinv;
        pub(crate) use x86_64::bignum_optsub::bignum_optsub;
        pub(crate) use x86_64::adx_mux::bignum_sqr_p521;
        pub(crate) use x86_64::adx_mux::bignum_tomont_p256;
        pub(crate) use x86_64::adx_mux::bignum_tomont_p384;
        pub(crate) use x86_64::adx_mux::curve25519_x25519;
        pub(crate) use x86_64::adx_mux::curve25519_x25519base;
        pub(crate) use x86_64::adx_mux::edwards25519_decode;
        pub(crate) use x86_64::adx_mux::edwards25519_scalarmulbase;
        pub(crate) use x86_64::adx_mux::edwards25519_scalarmuldouble;
        pub(crate) use x86_64::ghash;
        pub(crate) use x86_64::mlkem::{
            mlkem_ntt,
            mlkem_intt,
            mlkem_mulcache_compute,
            mlkem_rej_uniform_vartime,
            mlkem_basemul_k3,
            mlkem_reduce,
            mlkem_compress_d4,
            mlkem_compress_d10,
            mlkem_frombytes,
            mlkem_tobytes,
            mlkem_tomont,
            mlkem_unpack,
        };
        pub(crate) use x86_64::mont::{mont_mul, mont_sqr};
        pub(crate) use x86_64::mont_exp::mont_exp;
        pub(crate) use x86_64::rsaz::Rsaz;
        pub(crate) use x86_64::rsaz_avx512::{Operands, RsazAvx512};
        pub(crate) use x86_64::mlkem768_sample_poly_ntt_8x::mlkem768_sample_poly_ntt_8x;

        pub(crate) use x86_64::adx_mux::p256_montjadd;
        pub(crate) use x86_64::adx_mux::p256_montjdouble;
        pub(crate) use x86_64::adx_mux::p256_montjmixadd;
        pub(crate) use x86_64::adx_mux::p256_montjscalarmul;
        pub(crate) use x86_64::ecp_nistz256::{P256GeneratorRow, p256_point_add_affine, p256_select_w7};
        pub(crate) use x86_64::adx_mux::p384_montjadd;
        pub(crate) use x86_64::adx_mux::p384_montjmixadd;
        pub(crate) use x86_64::adx_mux::p384_montjdouble;
        pub(crate) use x86_64::adx_mux::p384_montjscalarmul;
        pub(crate) use x86_64::adx_mux::p521_jadd;
        pub(crate) use x86_64::adx_mux::p521_jdouble;
        pub(crate) use x86_64::adx_mux::p521_jmixadd;
        pub(crate) use x86_64::adx_mux::p521_jscalarmul;
        pub(crate) use x86_64::sha1_mux::{sha1_compress_blocks, sha1_compress_padded};
        pub(crate) use x86_64::sha256_mux::{sha256_compress_blocks, sha256_finish};
        pub(crate) use x86_64::sha512::sha512_compress_blocks;
        pub(crate) use x86_64::sha3_keccak_f1600::sha3_keccak_f1600;
        pub(crate) use x86_64::sha3_keccak4_f1600_shim::sha3_keccak4_f1600;
        pub(crate) use x86_64::sha3_keccak_nof4_f1600::sha3_keccak_nof4_f1600;

    } else if #[cfg(rind_backend = "aarch64")] {
        pub(in crate::low) use aarch64::cpu::{enter_cpu_state, zero_bytes, ct_compare_bytes, ct_compare_16, leave_cpu_state, missing_cpu_feature};
        pub(crate) use aarch64::aes::{AesDecKey, AesKey};
        pub(crate) use aarch64::aes_cbc;
        pub(crate) use aarch64::aes_ctr;
        pub(crate) use aarch64::cpu::HaveCryptoExt;
        #[cfg(test)]
        pub(crate) use aarch64::ct_qemu;
        pub(crate) use aarch64::aes_gcm;
        pub(crate) use aarch64::bignum_add::bignum_add;
        pub(crate) use aarch64::bignum_add_p256::bignum_add_p256;
        pub(crate) use aarch64::bignum_add_p384::bignum_add_p384;
        pub(crate) use aarch64::bignum_add_p521::bignum_add_p521;
        pub(crate) use aarch64::bignum_bitsize::bignum_bitsize;
        pub(crate) use aarch64::bignum_cmp_lt::bignum_cmp_lt;
        pub(crate) use aarch64::bignum_coprime::bignum_coprime;
        pub(crate) use aarch64::bignum_copy_row_from_table_mux::bignum_copy_row_from_table;
        pub(crate) use aarch64::bignum_ctz::bignum_ctz;
        pub(crate) use aarch64::bignum_point_select::{bignum_aff_point_select_p384, bignum_aff_point_select_p521};
        pub(crate) use aarch64::bignum_demont::bignum_demont;
        pub(crate) use aarch64::bignum_demont_p256::bignum_demont_p256;
        pub(crate) use aarch64::bignum_demont_p384::bignum_demont_p384;
        pub(crate) use aarch64::bignum_digitsize::bignum_digitsize;
        pub(crate) use aarch64::bignum_eq::bignum_eq;
        pub(crate) use aarch64::bignum_inv_p256::bignum_inv_p256;
        pub(crate) use aarch64::bignum_inv_p384::bignum_inv_p384;
        pub(crate) use aarch64::bignum_inv_p521::bignum_inv_p521;
        pub(crate) use aarch64::bignum_madd_n25519::bignum_madd_n25519;
        pub(crate) use aarch64::bignum_mod_n25519::bignum_mod_n25519;
        pub(crate) use aarch64::bignum_mod_n256::bignum_mod_n256;
        pub(crate) use aarch64::bignum_mod_n384::bignum_mod_n384;
        pub(crate) use aarch64::bignum_mod_n521::bignum_mod_n521;
        pub(crate) use aarch64::bignum_modadd::bignum_modadd;
        pub(crate) use aarch64::bignum_modinv::bignum_modinv;
        pub(crate) use aarch64::bignum_modsub::bignum_modsub;
        pub(crate) use aarch64::bignum_montifier::bignum_montifier;
        pub(crate) use aarch64::bignum_montmul::bignum_montmul;
        pub(crate) use aarch64::bignum_montmul_p256::bignum_montmul_p256;
        pub(crate) use aarch64::bignum_montmul_p384::bignum_montmul_p384;
        pub(crate) use aarch64::bignum_montredc::bignum_montredc;
        pub(crate) use aarch64::bignum_montsqr_p256::bignum_montsqr_p256;
        pub(crate) use aarch64::bignum_montsqr_p384::bignum_montsqr_p384;
        pub(crate) use aarch64::bignum_mul::bignum_mul;
        pub(crate) use aarch64::bignum_mul_p521::bignum_mul_p521;
        pub(crate) use aarch64::bignum_mux::bignum_mux;
        pub(crate) use aarch64::bignum_neg_p25519::bignum_neg_p25519;
        pub(crate) use aarch64::bignum_neg_p256::bignum_neg_p256;
        pub(crate) use aarch64::bignum_neg_p384::bignum_neg_p384;
        pub(crate) use aarch64::bignum_neg_p521::bignum_neg_p521;
        pub(crate) use aarch64::bignum_negmodinv::bignum_negmodinv;
        pub(crate) use aarch64::bignum_optsub::bignum_optsub;
        pub(crate) use aarch64::bignum_sqr_p521::bignum_sqr_p521;
        pub(crate) use aarch64::bignum_tomont_p256::bignum_tomont_p256;
        pub(crate) use aarch64::bignum_tomont_p384::bignum_tomont_p384;
        pub(crate) use aarch64::curve25519_x25519::curve25519_x25519;
        pub(crate) use aarch64::curve25519_x25519base::curve25519_x25519base;
        pub(crate) use aarch64::edwards25519_decode::edwards25519_decode;
        pub(crate) use aarch64::edwards25519_scalarmulbase::edwards25519_scalarmulbase;
        pub(crate) use aarch64::edwards25519_scalarmuldouble::edwards25519_scalarmuldouble;
        pub(crate) use aarch64::mlkem::{
            mlkem_ntt,
            mlkem_intt,
            mlkem_mulcache_compute,
            mlkem_rej_uniform_vartime,
        };
        pub(crate) use aarch64::mlkem_basemul_k3::mlkem_basemul_k3;
        pub(crate) use aarch64::mlkem_reduce::mlkem_reduce;
        pub(crate) use aarch64::mlkem_tobytes::mlkem_tobytes;
        pub(crate) use aarch64::mlkem_tomont::mlkem_tomont;
        pub(crate) use aarch64::mont::{mont_mul, mont_sqr};
        pub(crate) use aarch64::ghash;
        pub(crate) use aarch64::p256_montjadd::p256_montjadd;
        pub(crate) use aarch64::p256_montjdouble::p256_montjdouble;
        pub(crate) use aarch64::p256_montjmixadd::p256_montjmixadd;
        pub(crate) use aarch64::p256_scalarmul::p256_scalarmul;
        pub(crate) use aarch64::p256_scalarmulbase::p256_scalarmulbase;
        pub(crate) use aarch64::p384_montjadd::p384_montjadd;
        pub(crate) use aarch64::p384_montjmixadd::p384_montjmixadd;
        pub(crate) use aarch64::p384_montjdouble::p384_montjdouble;
        pub(crate) use aarch64::p384_montjscalarmul::p384_montjscalarmul;
        pub(crate) use aarch64::p521_jadd::p521_jadd;
        pub(crate) use aarch64::p521_jdouble::p521_jdouble;
        pub(crate) use aarch64::p521_jmixadd::p521_jmixadd;
        pub(crate) use aarch64::p521_jscalarmul::p521_jscalarmul;
        pub(crate) use aarch64::sha1::{sha1_compress_blocks, sha1_compress_padded};
        pub(crate) use aarch64::sha256::{sha256_compress_blocks, sha256_finish};
        pub(crate) use aarch64::sha3_keccak_f1600_mux::sha3_keccak_f1600;
        pub(crate) use aarch64::sha3_keccak4_f1600_mux::sha3_keccak4_f1600;
        pub(crate) use aarch64::sha3_keccak_nof4_f1600::sha3_keccak_nof4_f1600;
        pub(crate) use aarch64::sha512::sha512_compress_blocks;

        pub(crate) use aarch64::chacha20;
        pub(crate) use aarch64::chacha20poly1305;
        pub(crate) use generic::mlkem::{mlkem_compress_d4, mlkem_compress_d10, mlkem_frombytes, mlkem_unpack};
        pub(crate) use generic::mlkem768::mlkem768_sample_poly_ntt_8x;
    } else if #[cfg(rind_backend = "arm")] {
        pub(in crate::low) use arm::cpu::{enter_cpu_state, zero_bytes, ct_compare_bytes, ct_compare_16, leave_cpu_state, missing_cpu_feature};
        pub(crate) use arm::aes::{AesDecKey, AesKey};
        pub(crate) use arm::aes_cbc;
        pub(crate) use arm::aes_ctr;
        pub(crate) use arm::aesv8_armx::AesHwKey;
        pub(crate) use arm::cpu::HaveCryptoExt;
        #[cfg(test)]
        pub(crate) use arm::ct_qemu;
        pub(crate) use arm::ghashv8_armx::GhashTable;
        pub(crate) use arm::chacha20;
        pub(crate) use arm::poly1305;
        pub(crate) use arm::curve25519::curve25519_x25519;
        pub(crate) use arm::mont::{mont_mul, mont_sqr};
        // SHA-1 and SHA-256 use the crypto extension where present, else rind's
        // portable SHA, since libcrux has no SHA-1 and rind's SHA-256 is faster
        // than libcrux's. SHA-512 is aws-lc's, NEON or scalar.
        pub(crate) use arm::keccak1600_armv4::{
            sha3_keccak4_f1600, sha3_keccak_f1600, sha3_keccak_nof4_f1600,
        };
        pub(crate) use arm::sha_armv4::{
            sha1_compress_blocks, sha1_compress_padded, sha256_compress_blocks, sha256_finish,
            sha512_compress_blocks,
        };
    } else if #[cfg(rind_backend = "portable")] {
        pub(in crate::low) use portable::cpu::{enter_cpu_state, zero_bytes, ct_compare_bytes, ct_compare_16, leave_cpu_state, missing_cpu_feature};
        pub(crate) use portable::aes::{AesDecKey, AesKey};
        pub(crate) use portable::aes_cbc;
        pub(crate) use portable::aes_ctr;
        pub(crate) use portable::chacha20;
        pub(crate) use portable::curve25519::curve25519_x25519;
        pub(crate) use generic::bignum::{mont_mul, mont_sqr};
        pub(crate) use portable::keccak::{
            sha3_keccak4_f1600, sha3_keccak_f1600, sha3_keccak_nof4_f1600,
        };
        pub(crate) use portable::sha::{
            sha1_compress_blocks, sha1_compress_padded, sha256_compress_blocks, sha256_finish,
            sha512_compress_blocks,
        };
    } else {
        compile_error!("build.rs sets rind_backend");
    }
}
