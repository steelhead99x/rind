// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES-GCM on AVX and MOVBE, with HACL*'s Vale AES-GCM, imported by
//! `admin/import-hacl`, which interleaves AES-CTR and GHASH over six blocks
//! at a time as OpenSSL's `aesni_gcm` does. It runs every message without
//! VAES, and short ones with it.
//!
//! Vale proves that `gcm{128,256}_{encrypt,decrypt}_opt` compute AES-GCM, tag
//! check included, for every AAD and message under 2^32 bytes, in place, from
//! the counter block of its `compute_iv`, which rind runs for them, and from
//! round keys and GHASH key powers in the layout its own key expansion and
//! `keyhash_init` write. rind computes those two itself, since Vale's setup
//! takes about twice as long; `proofs/` proves them so, and the tests check
//! them against Vale's byte for byte. The rest of the Rust here does what
//! EverCrypt's proven Low* wrapper, `Vale.Wrapper.X64.GCMencryptOpt`, does
//! around the routines: it zero-pads the partial blocks of the message and
//! AAD, and picks the six-block loop's share of the message.
//! `proofs/` proves that too, over `counter_block` and `aead`, the only code
//! here that calls a routine.
//!
//! The layout the proof assumes, from that wrapper's preconditions and
//! `Vale.AES.OptPublic.hkeys_reqs_pub`:
//! - the round keys are FIPS 197's, each as its 16 bytes in order, as
//!   [`HwKey`] holds them;
//! - the eight GHASH key powers are H, H^2, E_K(0) byte-reversed, H^3, H^4,
//!   zero, H^5, and H^6, each H^n as Vale's `gf128_power h n` (`shift_key_1`
//!   of H^n), the form [`ClmulTable`] holds.

use core::arch::x86_64::__m128i;

use super::aes::HwKey;
use super::cpu::HaveAvxMovbeForAesGcm;
use super::ghash::{self, ClmulTable};

/// The routines with the GHASH key powers they read.
pub(crate) struct AvxKernel {
    hkeys: [__m128i; 8],
    token: HaveAvxMovbeForAesGcm,
}

impl AvxKernel {
    /// The kernel for the GHASH key `h`, whose powers `table` holds.
    pub(crate) fn new(table: &ClmulTable, h: u128, token: HaveAvxMovbeForAesGcm) -> Self {
        Self {
            hkeys: table.vale_hkeys(h),
            token,
        }
    }

    /// Encrypts `inout` in place under `nonce`, and returns its tag. `aad`
    /// and `inout` are each shorter than 2^32 bytes.
    pub(crate) fn seal(
        &self,
        key: &HwKey,
        nonce: &[u8; 12],
        aad: &[u8],
        inout: &mut [u8],
    ) -> [u8; 16] {
        let mut tag = [0u8; 16];
        self.cipher::<true>(key, nonce, aad, inout, &mut tag);
        tag
    }

    /// Decrypts `inout` in place under `nonce`, and returns whether `tag` is
    /// its tag. `aad` and `inout` are each shorter than 2^32 bytes.
    pub(crate) fn open(
        &self,
        key: &HwKey,
        nonce: &[u8; 12],
        aad: &[u8],
        inout: &mut [u8],
        tag: &[u8; 16],
    ) -> bool {
        let mut tag = *tag;
        self.cipher::<false>(key, nonce, aad, inout, &mut tag) == 0
    }

    /// Runs the encrypting or decrypting routine, which writes the tag to, or
    /// checks it against, `tag`, and returns the decrypting one's result.
    fn cipher<const ENC: bool>(
        &self,
        key: &HwKey,
        nonce: &[u8; 12],
        aad: &[u8],
        inout: &mut [u8],
        tag: &mut [u8; 16],
    ) -> u64 {
        assert!(u32::try_from(aad.len()).is_ok() && u32::try_from(inout.len()).is_ok());

        // The counter block, which `compute_iv` reads a 96-bit nonce from
        // and writes over.
        let mut iv = [0u8; 16];
        iv[..12].copy_from_slice(nonce);
        counter_block(nonce, &mut iv, &self.hkeys, self.token);

        // The AAD's and message's partial blocks, zero-padded in registers:
        // copying them to a zeroed block instead calls `memcpy`, whose narrow
        // stores stall the routine's 16-byte load of the block.
        let aad_whole = aad.len() / 16 * 16;
        let aad_partial = ghash::load_partial(&aad[aad_whole..]);
        let len = inout.len();
        let (blocks, tail) = inout.split_at_mut(len / 16 * 16);
        let mut partial = ghash::load_partial(tail);
        let mut scratch = [0u8; 144];

        // The six-block loop's share, which must be 18 blocks or more to
        // encrypt, or 6 to decrypt.
        let six = match blocks.len() / 96 * 6 {
            n if n >= if ENC { 18 } else { 6 } => n,
            _ => 0,
        };
        let result = aead::<ENC>(
            key,
            &self.hkeys,
            Buffers {
                aad,
                aad_whole,
                iv: &mut iv,
                aad_partial: &aad_partial,
                blocks,
                six,
                partial: &mut partial,
                len,
                scratch: &mut scratch,
                tag,
            },
            self.token,
        );
        ghash::store_partial(tail, partial);
        result
    }
}

/// Runs `compute_iv`, which writes the counter block for the 96-bit `nonce`
/// over `iv`, which holds `nonce` in its first 12 bytes.
#[inline(always)]
fn counter_block(
    nonce: &[u8; 12],
    iv: &mut [u8; 16],
    hkeys: &[__m128i; 8],
    _: HaveAvxMovbeForAesGcm,
) {
    let iv = iv.as_mut_ptr();
    // SAFETY: `nonce` is 12 bytes, `iv` 16 writable ones, and `hkeys` the
    // GHASH key powers. The token proves the CPU has PCLMULQDQ and AVX.
    unsafe {
        asm_call!(unsafe extern "sysv64" compute_iv_stdcall(nonce.as_ptr(), 12, 0, iv, iv, hkeys.as_ptr().cast()))
    };
}

/// What an AEAD routine reads and writes besides its keys.
struct Buffers<'a> {
    /// The AAD, and the length of its whole blocks.
    aad: &'a [u8],
    aad_whole: usize,
    /// The counter block, which the routine writes over.
    iv: &'a mut [u8; 16],
    /// The AAD's partial block, zero-padded.
    aad_partial: &'a __m128i,
    /// The message's whole blocks, the first `six` for the six-block loop.
    blocks: &'a mut [u8],
    six: usize,
    /// The message's partial block, zero-padded, and the message's length.
    partial: &'a mut __m128i,
    len: usize,
    /// The 144 bytes the routine may write, and the tag it writes or reads.
    scratch: &'a mut [u8],
    tag: &'a mut [u8; 16],
}

/// Runs the encrypting or decrypting routine for `key`'s size, in place on
/// `b`'s blocks, and returns the decrypting one's result.
#[inline(always)]
fn aead<const ENC: bool>(
    key: &HwKey,
    hkeys: &[__m128i; 8],
    b: Buffers<'_>,
    _: HaveAvxMovbeForAesGcm,
) -> u64 {
    let ones = b.blocks.len() / 16 - b.six;
    let blocks = b.blocks.as_mut_ptr();
    let routine: Aead = match (ENC, key) {
        (true, HwKey::Aes128(_)) => gcm128_encrypt_opt,
        (true, HwKey::Aes256(_)) => gcm256_encrypt_opt,
        (false, HwKey::Aes128(_)) => gcm128_decrypt_opt,
        (false, HwKey::Aes256(_)) => gcm256_decrypt_opt,
        (_, HwKey::Aes192(_)) => unreachable!("Vale has no AES-192 routine"),
    };
    // SAFETY: the routine reads `aad`'s whole blocks and `aad_partial`, and
    // reads and writes in place the message's whole blocks, the first `six`
    // in its six-block loop and the `ones` after them one at a time, then
    // `partial`. `key` is its round keys, `iv` the counter block, and
    // `hkeys` the GHASH key powers; `scratch` is the 144 bytes it may write,
    // and `tag` the 16 it writes or reads. The token proves the CPU has
    // AES-NI, PCLMULQDQ, AVX, and MOVBE.
    unsafe {
        let rest = blocks.add(b.six * 16);
        asm_call!(unsafe extern "sysv64" routine(
            b.aad.as_ptr(),
            b.aad.len() as u64,
            (b.aad_whole / 16) as u64,
            key.as_aes_key(),
            b.iv.as_mut_ptr(),
            hkeys.as_ptr().cast(),
            (b.aad_partial as *const __m128i).cast(),
            blocks,
            blocks,
            b.six as u64,
            rest,
            rest,
            ones as u64,
            (b.partial as *mut __m128i).cast(),
            b.len as u64,
            b.scratch.as_mut_ptr(),
            b.tag.as_mut_ptr(),
        ))
    }
}

/// Declares a routine as a naked function over Vale's text. Each takes the
/// System V ABI on every OS, since its text is Vale's ELF and Mach-O flavors.
macro_rules! routine {
    ($name:ident($($arg:ident: $ty:ty),* $(,)?) $(-> $ret:ty)?) => {
        #[unsafe(naked)]
        unsafe extern "sysv64" fn $name($($arg: $ty),*) $(-> $ret)? {
            #[cfg(not(target_vendor = "apple"))]
            core::arch::naked_asm!(
                include_str!(concat!("hacl/", stringify!($name), ".linux.s")),
                options(att_syntax),
            );
            #[cfg(target_vendor = "apple")]
            core::arch::naked_asm!(
                include_str!(concat!("hacl/", stringify!($name), ".apple.s")),
                options(att_syntax),
            );
        }
    };
}

// Vale's own setup, which the tests check rind's against.
#[cfg(test)]
routine!(aes128_key_expansion(key: *const u8, round_keys: *mut u8));
#[cfg(test)]
routine!(aes256_key_expansion(key: *const u8, round_keys: *mut u8));
#[cfg(test)]
routine!(aes128_keyhash_init(round_keys: *const u8, hkeys: *mut u8));
#[cfg(test)]
routine!(aes256_keyhash_init(round_keys: *const u8, hkeys: *mut u8));
routine!(
    compute_iv_stdcall(
        iv: *const u8,
        iv_len: u64,
        iv_blocks: u64,
        j0: *mut u8,
        extra: *const u8,
        hkeys: *const u8,
    )
);

/// The AEAD routines' arguments: the AAD, its length and whole blocks, the
/// round keys, the counter block, the GHASH key powers, and the AAD's
/// partial block; the six-block loop's input, output, and blocks, then the
/// one-block loop's; the message's partial block, the message's length,
/// scratch, and the tag. Decryption returns zero if the tag matches.
type Aead = unsafe extern "sysv64" fn(
    *const u8,
    u64,
    u64,
    *const u8,
    *mut u8,
    *const u8,
    *const u8,
    *mut u8,
    *mut u8,
    u64,
    *mut u8,
    *mut u8,
    u64,
    *mut u8,
    u64,
    *mut u8,
    *mut u8,
) -> u64;

macro_rules! aead {
    ($($name:ident),*) => {$(
        routine!($name(
            aad: *const u8,
            aad_len: u64,
            aad_blocks: u64,
            round_keys: *const u8,
            iv: *mut u8,
            hkeys: *const u8,
            aad_partial: *const u8,
            six_in: *mut u8,
            six_out: *mut u8,
            six_blocks: u64,
            one_in: *mut u8,
            one_out: *mut u8,
            one_blocks: u64,
            partial: *mut u8,
            len: u64,
            scratch: *mut u8,
            tag: *mut u8
        ) -> u64);
    )*};
}

aead!(
    gcm128_encrypt_opt,
    gcm256_encrypt_opt,
    gcm128_decrypt_opt,
    gcm256_decrypt_opt
);

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::x86_64::adx_mux::tests::Rng;
    use crate::low::x86_64::aes::AesKey;
    use crate::low::x86_64::cpu::HaveAesHardware;

    // rind's round keys and GHASH key powers are the bytes Vale's own setup
    // writes, the layout its proof assumes: for each key size, the all-zero
    // and all-ones keys and random ones, whose H spans both values of the
    // top bit the multiply by x carries out.
    #[test]
    fn setup_matches_vale() {
        let (Some(token), Some(hw)) = (HaveAvxMovbeForAesGcm::check(), HaveAesHardware::check())
        else {
            return;
        };
        let mut rng = Rng(1);
        for key_len in [16, 32] {
            let mut keys = vec![vec![0u8; key_len], vec![0xff; key_len]];
            keys.extend((0..64).map(|_| (0..key_len).map(|_| rng.next() as u8).collect()));
            for key in keys {
                let key_schedule = AesKey::new(&key);
                let AesKey::Hw(hw_key) = &key_schedule else {
                    unreachable!()
                };
                let mut vale_keys = [0u8; 240];
                let mut vale_hkeys = [0u8; 128];
                // SAFETY: `key` is `key_len` readable bytes, `vale_keys` the
                // round keys' 16 * (rounds + 1) bytes, and `vale_hkeys` the
                // 128 bytes `keyhash_init` writes. The token proves the CPU
                // has AES-NI, PCLMULQDQ, and AVX.
                unsafe {
                    let (rk, hk) = (vale_keys.as_mut_ptr(), vale_hkeys.as_mut_ptr());
                    match key_len {
                        16 => {
                            asm_call!(unsafe extern "sysv64" aes128_key_expansion(key.as_ptr(), rk));
                            asm_call!(unsafe extern "sysv64" aes128_keyhash_init(rk, hk));
                        }
                        _ => {
                            asm_call!(unsafe extern "sysv64" aes256_key_expansion(key.as_ptr(), rk));
                            asm_call!(unsafe extern "sysv64" aes256_keyhash_init(rk, hk));
                        }
                    }
                }
                let round_keys_len = 16 * (key_len / 4 + 7);
                // SAFETY: `hw_key` begins with its round keys.
                let ours =
                    unsafe { core::slice::from_raw_parts(hw_key.as_aes_key(), round_keys_len) };
                assert_eq!(ours, &vale_keys[..round_keys_len], "{key:02x?}");

                let h = u128::from_be_bytes(hw_key.encrypt_block(&[0; 16]));
                let kernel = AvxKernel::new(&ClmulTable::new(h, hw), h, token);
                // SAFETY: any eight vectors are 128 bytes.
                let ours = unsafe { core::mem::transmute::<[__m128i; 8], [u8; 128]>(kernel.hkeys) };
                assert_eq!(ours, vale_hkeys, "{key:02x?}");
            }
        }
    }
}
