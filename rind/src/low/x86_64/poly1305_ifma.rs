// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Poly1305 on AVX-512 IFMA: OpenSSL's base 2^44 routines from
//! `poly1305-x86_64.pl`, eight blocks at a time on `vpmadd52luq` and
//! `vpmadd52huq`, imported by `admin/import-openssl`. OpenSSL runs them
//! wherever the CPU has AVX-512 F, VL, and IFMA; aws-lc and BoringSSL have
//! no vector Poly1305 for x86_64.
//!
//! The OpenSSL assembly is not formally verified: its correctness rests on
//! its use and testing in OpenSSL, and on rind's tests of it against RFC
//! 8439, Wycheproof, aws-lc-rs, and the scalar Poly1305.

use core::arch::x86_64::_mm256_zeroupper;

use super::cpu::HaveAvx512Ifma;

/// OpenSSL's opaque state for the base 2^44 routines: the hash `h`, the key
/// times 20 `s`, the key `r`, then the first four powers of the key, which
/// the first call long enough fills in.
#[repr(C, align(64))]
struct State([u64; 24]);

pub(crate) struct Poly1305 {
    state: State,
    /// The second half of the key, added to the result.
    s: [u8; 16],
    ifma: HaveAvx512Ifma,
}

impl Poly1305 {
    pub(crate) fn new(ifma: HaveAvx512Ifma, key: &[u8; 32]) -> Self {
        let mut state = State([0; 24]);
        // SAFETY: `state` is the routine's 192-byte state and `key` is 16
        // readable bytes of `r`. It runs only scalar instructions.
        unsafe {
            asm_call!(unsafe extern "sysv64" poly1305_init_base2_44(&mut state, key.as_ptr()))
        };
        Self {
            state,
            s: key[16..].try_into().unwrap(),
            ifma,
        }
    }

    /// Hashes `bytes`, zero-padded to a whole number of 16-byte blocks, as
    /// ChaCha20-Poly1305 pads the AAD and the ciphertext.
    pub(crate) fn add_padded(&mut self, bytes: &[u8]) {
        let (blocks, rest) = bytes.as_chunks::<16>();
        self.blocks(blocks.as_flattened());
        if !rest.is_empty() {
            let mut block = [0u8; 16];
            block[..rest.len()].copy_from_slice(rest);
            self.blocks(&block);
        }
    }

    /// Hashes `blocks`, a whole number of 16-byte blocks, each with the
    /// 2^128 bit set.
    fn blocks(&mut self, blocks: &[u8]) {
        // SAFETY: `state` is the routine's state, which `new` initialised,
        // and `blocks` is `blocks.len()` readable bytes, of which it reads
        // the whole blocks. The token proves AVX-512 F, VL, and IFMA.
        unsafe {
            asm_call!(unsafe extern "sysv64" poly1305_blocks_vpmadd52(&mut self.state, blocks.as_ptr(), blocks.len(), 1))
        };
        // Its one- to three-block path returns without clearing the upper
        // halves of the ymm registers it used, which slows the SSE code
        // after it on Intel's cores until something does.
        // SAFETY: the token proves AVX.
        unsafe { zero_upper(self.ifma) };
    }

    pub(crate) fn finish(mut self) -> [u8; 16] {
        let mut tag = [0u8; 16];
        // SAFETY: `state` is the routine's state, `tag` is 16 writable
        // bytes, and `s` is 16 readable bytes. It runs only scalar
        // instructions.
        unsafe {
            asm_call!(unsafe extern "sysv64" poly1305_emit_base2_44(&mut self.state, tag.as_mut_ptr(), self.s.as_ptr()))
        };
        tag
    }
}

#[target_feature(enable = "avx")]
fn zero_upper(_: HaveAvx512Ifma) {
    _mm256_zeroupper();
}

/// The input permutation, shifts, and masks the one-block path loads, as
/// one table it addresses by offset.
#[repr(C, align(64))]
struct Table2_44([u8; 160]);

/// The 44- and 42-bit masks the four- and eight-block paths load.
#[repr(C, align(64))]
struct MaskTable([u64; 16]);

static POLY1305_2_44: Table2_44 = Table2_44(include!("openssl/poly1305-x86_64.poly1305_2_44.rs"));
static POLY1305_X_MASK: MaskTable =
    MaskTable(include!("openssl/poly1305-x86_64.poly1305_x_mask.rs"));

// The routines take the System V ABI on every OS, since their text is
// OpenSSL's ELF and Mach-O flavors, which read their arguments from its
// registers.

#[unsafe(naked)]
unsafe extern "sysv64" fn poly1305_init_base2_44(state: *mut State, key: *const u8) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("openssl/poly1305_init_base2_44.linux.s"),
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("openssl/poly1305_init_base2_44.apple.s"),
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn poly1305_blocks_vpmadd52(
    state: *mut State,
    input: *const u8,
    len: usize,
    padbit: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("openssl/poly1305_blocks_vpmadd52.linux.s"),
        poly1305_2_44 = sym POLY1305_2_44,
        poly1305_x_mask = sym POLY1305_X_MASK,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("openssl/poly1305_blocks_vpmadd52.apple.s"),
        poly1305_2_44 = sym POLY1305_2_44,
        poly1305_x_mask = sym POLY1305_X_MASK,
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn poly1305_emit_base2_44(state: *mut State, mac: *mut u8, s: *const u8) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("openssl/poly1305_emit_base2_44.linux.s"),
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("openssl/poly1305_emit_base2_44.apple.s"),
        options(att_syntax),
    );
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;
    use crate::low::generic::poly1305 as scalar;

    // Every length through the one-block path, the 4- and 8-block paths and
    // their tails, split across calls at each block boundary of a prefix,
    // under a key `admin/ctgrind` keeps secret, against the scalar Poly1305.
    #[test]
    fn matches_scalar() {
        let Some(ifma) = HaveAvx512Ifma::check() else {
            return;
        };
        let input: Vec<u8> = (0..4096 + 15).map(|i| (i * 13 + 5) as u8).collect();
        for k in 0..3u8 {
            let key: [u8; 32] =
                core::array::from_fn(|i| (i as u8).wrapping_mul(29).wrapping_add(k));
            ct::secret_slice(&key);
            for len in (0..=600).chain([1024, 2048, 4096 + 15]) {
                let message = &input[..len];
                let mut padded = message.to_vec();
                padded.resize(len.next_multiple_of(16), 0);
                let mut want = scalar::Poly1305::new(&key);
                want.add_bytes(&padded);
                let want = ct::into_public(want.finish());

                for split in [0, 16, 48, 64, 128, 144] {
                    let split = split.min(padded.len());
                    let mut ours = Poly1305::new(ifma, &key);
                    ours.add_padded(&padded[..split]);
                    ours.add_padded(&message[split.min(len)..]);
                    let ours = ct::into_public(ours.finish());
                    assert_eq!(ours, want, "{len} bytes, split at {split}");
                }
            }
        }
    }
}
