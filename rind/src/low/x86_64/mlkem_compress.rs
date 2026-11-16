// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-KEM's ciphertext compression with mlkem-native's AVX2 routines, which
//! `admin/import-aws-lc` takes from aws-lc's copy. mlkem-native's HOL Light
//! proofs cover them, as it builds them.

/// `ByteEncode_4(Compress_4(a))`, for `a` in `[0, Q)`.
pub(crate) fn mlkem_compress_d4(r: &mut [u8; 128], a: &[i16; 256]) {
    assert!((a.as_ptr() as usize).is_multiple_of(32));
    // SAFETY: `r` and `a` are the sizes the routine writes and reads, `a` and
    // the table are 32-byte aligned for its aligned loads, and `super::mlkem`
    // calls this only with AVX2.
    unsafe {
        asm_call!(unsafe extern "sysv64" mlkem_poly_compress_d4_avx2_asm(r, a, &COMPRESS_D4_DATA))
    }
}

/// `ByteEncode_5(Compress_5(a))`, for `a` in `[0, Q)`.
pub(crate) fn mlkem_compress_d5(r: &mut [u8; 160], a: &[i16; 256]) {
    assert!((a.as_ptr() as usize).is_multiple_of(32));
    // SAFETY: as for `mlkem_compress_d4`.
    unsafe {
        asm_call!(unsafe extern "sysv64" mlkem_poly_compress_d5_avx2_asm(r, a, &COMPRESS_D5_DATA))
    }
}

/// `ByteEncode_10(Compress_10(a))`, for `a` in `[0, Q)`.
pub(crate) fn mlkem_compress_d10(r: &mut [u8; 320], a: &[i16; 256]) {
    assert!((a.as_ptr() as usize).is_multiple_of(32));
    // SAFETY: as for `mlkem_compress_d4`.
    unsafe {
        asm_call!(unsafe extern "sysv64" mlkem_poly_compress_d10_avx2_asm(r, a, &COMPRESS_D10_DATA))
    }
}

/// `ByteEncode_11(Compress_11(a))`, for `a` in `[0, Q)`.
pub(crate) fn mlkem_compress_d11(r: &mut [u8; 352], a: &[i16; 256]) {
    assert!((a.as_ptr() as usize).is_multiple_of(32));
    // SAFETY: as for `mlkem_compress_d4`.
    unsafe {
        asm_call!(unsafe extern "sysv64" mlkem_poly_compress_d11_avx2_asm(r, a, &COMPRESS_D11_DATA))
    }
}

#[repr(C, align(32))]
struct Table<const N: usize>([u8; N]);

/// mlkem-native's `mlk_compress_d4_data`: the dword permutation that packs.
static COMPRESS_D4_DATA: Table<32> = Table([
    0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 7, 0, 0, 0,
]);

/// mlkem-native's `mlk_compress_d5_data`: the byte shuffle that packs.
static COMPRESS_D5_DATA: Table<32> = Table([
    0, 1, 2, 3, 4, 255, 255, 255, 255, 255, 8, 9, 10, 11, 12, 255, 9, 10, 11, 12, 255, 0, 1, 2, 3,
    4, 255, 255, 255, 255, 255, 8,
]);

/// mlkem-native's `mlk_compress_d10_data`: the byte shuffle that packs.
static COMPRESS_D10_DATA: Table<32> = Table([
    0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 255, 255, 255, 255, 255, 255, 9, 10, 11, 12, 255, 255, 255,
    255, 255, 255, 0, 1, 2, 3, 4, 8,
]);

/// mlkem-native's `mlk_compress_d11_data`: the qword shifts, then the byte
/// shuffle that packs.
static COMPRESS_D11_DATA: Table<64> = Table([
    10, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 255, 255, 255, 255, 255, 5, 6, 7, 8, 9, 10, 255, 255,
    255, 255, 0, 0, 1, 2, 3, 4,
]);

// Every routine takes the System V ABI on every OS, since its text is
// aws-lc's ELF and Mach-O flavors, which read their arguments from its
// registers.

macro_rules! compress_routine {
    ($name:ident, $out:literal, $table:literal) => {
        #[unsafe(naked)]
        unsafe extern "sysv64" fn $name(
            r: *mut [u8; $out],
            a: *const [i16; 256],
            data: *const Table<$table>,
        ) {
            #[cfg(not(target_vendor = "apple"))]
            core::arch::naked_asm!(
                include_str!(concat!("aws_lc/", stringify!($name), ".linux.s")),
                options(att_syntax),
            );
            #[cfg(target_vendor = "apple")]
            core::arch::naked_asm!(
                include_str!(concat!("aws_lc/", stringify!($name), ".apple.s")),
                options(att_syntax),
            );
        }
    };
}

compress_routine!(mlkem_poly_compress_d4_avx2_asm, 128, 32);
compress_routine!(mlkem_poly_compress_d5_avx2_asm, 160, 32);
compress_routine!(mlkem_poly_compress_d10_avx2_asm, 320, 32);
compress_routine!(mlkem_poly_compress_d11_avx2_asm, 352, 64);
