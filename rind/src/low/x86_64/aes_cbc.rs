// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::aes::{AesDecKey, AesKey, HwDecKey, HwKey};

/// Encrypts whole blocks in place in CBC mode, the first chained from `iv`.
pub(crate) fn encrypt(key: &AesKey, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
    match key {
        AesKey::Hw(key) => hw_encrypt(key, iv, blocks),
        AesKey::Vpaes(key) => key.cbc_encrypt(iv, blocks),
        AesKey::Nohw(key) => key.cbc_encrypt(iv, blocks),
    }
}

/// Decrypts whole blocks in place in CBC mode, the first chained from `iv`.
pub(crate) fn decrypt(key: &AesDecKey, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
    match key {
        AesDecKey::Hw(key) => hw_decrypt(key, iv, blocks),
        AesDecKey::Vpaes(key) => key.cbc_decrypt(iv, blocks),
        AesDecKey::Nohw(key) => key.cbc_decrypt(iv, blocks),
    }
}

/// Encrypts whole blocks in place in CBC mode with aws-lc's AES-NI routine.
fn hw_encrypt(key: &HwKey, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
    hw_cbc(key.as_aes_key(), iv, blocks, true)
}

/// Decrypts whole blocks in place in CBC mode with aws-lc's AES-NI routine.
fn hw_decrypt(key: &HwDecKey, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
    hw_cbc(key.as_aes_key(), iv, blocks, false)
}

/// CBC with aws-lc's AES-NI routine: serial encryption, and decryption eight
/// blocks at a time.
///
/// `key` is an `AES_KEY` from a `HwKey` to encrypt, or a `HwDecKey` to
/// decrypt.
fn hw_cbc(key: *const u8, iv: &[u8; 16], blocks: &mut [[u8; 16]], encrypt: bool) {
    // The routine leaves the next IV here; CBC callers here start afresh.
    let mut ivec = *iv;
    // SAFETY: `blocks` is `16 * blocks.len()` readable and writable bytes,
    // which aws-lc allows to alias, and `key` the `AES_KEY` for the
    // direction. Only a `HaveAesHardware` token builds it, proving the AES-NI
    // and SSSE3 the routine uses. It returns at once for zero bytes.
    unsafe {
        asm_call!(unsafe extern "sysv64" aes_hw_cbc_encrypt(
            blocks.as_ptr().cast(),
            blocks.as_mut_ptr().cast(),
            16 * blocks.len(),
            key,
            &mut ivec,
            i32::from(encrypt),
        ))
    }
}

// It takes the System V ABI on every OS, since its text is aws-lc's ELF and
// Mach-O flavors, which read their arguments from its registers.
#[unsafe(naked)]
unsafe extern "sysv64" fn aes_hw_cbc_encrypt(
    input: *const u8,
    output: *mut u8,
    len: usize,
    key: *const u8,
    ivec: *mut [u8; 16],
    enc: i32,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/aes_hw_cbc_encrypt.linux.s"),
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/aes_hw_cbc_encrypt.apple.s"),
        options(att_syntax),
    );
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::x86_64::aes_nohw::NohwKey;
    use crate::low::x86_64::cpu::HaveSsse3;
    use crate::low::x86_64::vpaes_x86_64::{VpaesDecKey, VpaesKey};

    // Every other test sees only the path the CPU picks, so each path is
    // compared here with a model chaining single blocks, for each key size,
    // at lengths around aws-lc's eight-block loop and each of its tails.
    #[test]
    fn paths_match() {
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for (key_len, seed) in [16, 24, 32].into_iter().zip(1..) {
            let key = bytes(key_len, seed);
            let mut paths = vec![(
                AesKey::Nohw(NohwKey::new(&key)),
                AesDecKey::Nohw(NohwKey::new(&key)),
            )];
            if let Some(ssse3) = HaveSsse3::check() {
                paths.push((
                    AesKey::Vpaes(VpaesKey::new(&key, ssse3)),
                    AesDecKey::Vpaes(VpaesDecKey::new(&key, ssse3)),
                ));
            }
            let enc = AesKey::new(&key);
            if matches!(enc, AesKey::Hw(_)) {
                paths.push((enc, AesDecKey::new(&key)));
            }
            let model = NohwKey::new(&key);
            let iv: [u8; 16] = bytes(16, seed + 7).try_into().unwrap();
            for blocks in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 23] {
                let what = format!("{key_len}-byte key, {blocks} blocks");
                let msg: Vec<[u8; 16]> = bytes(16 * blocks, blocks as u32).as_chunks().0.to_vec();
                let mut want = msg.clone();
                let mut prev = iv;
                for block in &mut want {
                    for (b, p) in block.iter_mut().zip(prev) {
                        *b ^= p;
                    }
                    *block = model.encrypt_block(block);
                    prev = *block;
                }

                for (i, (enc, dec)) in paths.iter().enumerate() {
                    let mut got = msg.clone();
                    encrypt(enc, &iv, &mut got);
                    assert_eq!(got, want, "{what}, path {i} encrypts");
                    decrypt(dec, &iv, &mut got);
                    assert_eq!(got, msg, "{what}, path {i} decrypts");
                }
            }
        }
    }
}
