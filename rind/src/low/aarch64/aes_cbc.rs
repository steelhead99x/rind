// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::arch::aarch64::*;

use super::aes::{AesDecKey, AesKey, HwDecKey, HwKey, load, store};

/// Encrypts whole blocks in place in CBC mode, the first chained from `iv`.
pub(crate) fn encrypt(key: &AesKey, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
    match key {
        // SAFETY: only a `HaveCryptoExt` token builds the round keys, and
        // rind requires NEON.
        AesKey::Hw(HwKey::Aes128(key)) => unsafe { hw_encrypt(key.round_keys(), iv, blocks) },
        // SAFETY: as above.
        AesKey::Hw(HwKey::Aes192(key)) => unsafe { hw_encrypt(key.round_keys(), iv, blocks) },
        // SAFETY: as above.
        AesKey::Hw(HwKey::Aes256(key)) => unsafe { hw_encrypt(key.round_keys(), iv, blocks) },
        AesKey::Vpaes(key) => key.cbc_encrypt(iv, blocks),
    }
}

/// Decrypts whole blocks in place in CBC mode, the first chained from `iv`.
pub(crate) fn decrypt(key: &AesDecKey, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
    match key {
        // SAFETY: only a `HaveCryptoExt` token builds the round keys, and
        // rind requires NEON.
        AesDecKey::Hw(HwDecKey::Aes128(round_keys)) => unsafe {
            hw_decrypt(round_keys, iv, blocks)
        },
        // SAFETY: as above.
        AesDecKey::Hw(HwDecKey::Aes192(round_keys)) => unsafe {
            hw_decrypt(round_keys, iv, blocks)
        },
        // SAFETY: as above.
        AesDecKey::Hw(HwDecKey::Aes256(round_keys)) => unsafe {
            hw_decrypt(round_keys, iv, blocks)
        },
        AesDecKey::Vpaes(key) => key.cbc_decrypt(iv, blocks),
    }
}

/// Each block's encryption waits on the last, so this keeps the chain to
/// the `aese`/`aesmc` pairs, as aws-lc's `aesv8-armx` does: the plaintext
/// and the first round key join the last round key off the chain, since
/// `aese` XORs its key in first. `y` is each ciphertext block less the last
/// round key.
// Loops by index, each in its own function: Aeneas translates no loop that
// writes through an iterator's references, nor one nested in another.
#[allow(clippy::needless_range_loop)]
#[target_feature(enable = "aes,neon")]
fn hw_encrypt<const N: usize>(
    round_keys: &[uint8x16_t; N],
    iv: &[u8; 16],
    blocks: &mut [[u8; 16]],
) {
    let last = round_keys[N - 1];
    let first_last = veorq_u8(round_keys[0], last);
    let mut y = veorq_u8(load(iv), last);
    for i in 0..blocks.len() {
        let b = veorq_u8(load(&blocks[i]), first_last);
        y = encrypt_rounds(round_keys, vaesmcq_u8(aese_chained(y, b)));
        blocks[i] = store(veorq_u8(y, last));
    }
}

/// The middle rounds of [`hw_encrypt`]'s block, `b` after its first, and
/// the `aese` of the second-last round key.
#[inline]
#[target_feature(enable = "aes,neon")]
fn encrypt_rounds<const N: usize>(round_keys: &[uint8x16_t; N], mut b: uint8x16_t) -> uint8x16_t {
    for round_key in &round_keys[1..N - 2] {
        b = vaesmcq_u8(vaeseq_u8(b, *round_key));
    }
    vaeseq_u8(b, round_keys[N - 2])
}

/// `vaeseq_u8(y, b)`, with `y`'s register its destination.
///
/// LLVM takes `aese` as commutative and makes the fresh operand its
/// destination, which puts a `mov` of `y` on the chain each block, costing
/// about a tenth of the throughput on Neoverse N2.
#[inline]
#[target_feature(enable = "aes,neon")]
fn aese_chained(y: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    let out;
    // SAFETY: `aese` only reads and writes the two registers named, and the
    // target feature enables it.
    unsafe {
        core::arch::asm!(
            "aese {y:v}.16b, {b:v}.16b",
            y = inout(vreg) y => out,
            b = in(vreg) b,
            options(pure, nomem, nostack, preserves_flags),
        );
    }
    out
}

/// Decrypts eight blocks at a time, which are independent, so the AES
/// units pipeline them; the rest go one at a time. The round keys are the
/// equivalent inverse cipher's, as `hw_decrypt_block` takes them, and the
/// last joins the chaining block off the critical path.
#[allow(clippy::needless_range_loop)]
#[target_feature(enable = "aes,neon")]
fn hw_decrypt<const N: usize>(
    round_keys: &[uint8x16_t; N],
    iv: &[u8; 16],
    blocks: &mut [[u8; 16]],
) {
    let last = round_keys[N - 1];
    let mut prev = load(iv);
    let (chunks, tail) = blocks.as_chunks_mut::<8>();
    for c in 0..chunks.len() {
        prev = decrypt_8(round_keys, prev, &mut chunks[c]);
    }

    for t in 0..tail.len() {
        let c = load(&tail[t]);
        let b = decrypt_rounds(round_keys, c);
        tail[t] = store(veorq_u8(b, veorq_u8(last, prev)));
        prev = c;
    }
}

/// [`hw_decrypt`] of eight blocks chained from `prev`, returning the last
/// ciphertext block, the next chaining block.
#[allow(clippy::needless_range_loop)]
#[inline]
#[target_feature(enable = "aes,neon")]
fn decrypt_8<const N: usize>(
    round_keys: &[uint8x16_t; N],
    prev: uint8x16_t,
    chunk: &mut [[u8; 16]; 8],
) -> uint8x16_t {
    let last = round_keys[N - 1];
    let mut b = [prev; 8];
    for j in 0..8 {
        b[j] = load(&chunk[j]);
    }
    let next = b[7];
    for r in 0..N - 2 {
        b = decrypt_round_8(b, round_keys[r]);
    }
    // Go backwards, so each block's ciphertext is read before it is
    // overwritten.
    for k in 0..8 {
        let i = 7 - k;
        let chain = if i == 0 { prev } else { load(&chunk[i - 1]) };
        let out = veorq_u8(vaesdq_u8(b[i], round_keys[N - 2]), veorq_u8(last, chain));
        chunk[i] = store(out);
    }
    next
}

/// An `aesd` and `aesimc` round of each of eight blocks.
#[allow(clippy::needless_range_loop)]
#[inline]
#[target_feature(enable = "aes,neon")]
fn decrypt_round_8(mut b: [uint8x16_t; 8], round_key: uint8x16_t) -> [uint8x16_t; 8] {
    for j in 0..8 {
        b[j] = vaesimcq_u8(vaesdq_u8(b[j], round_key));
    }
    b
}

/// All but the last round key's XOR of [`hw_decrypt`]'s block `b`.
#[inline]
#[target_feature(enable = "aes,neon")]
fn decrypt_rounds<const N: usize>(round_keys: &[uint8x16_t; N], mut b: uint8x16_t) -> uint8x16_t {
    for round_key in &round_keys[..N - 2] {
        b = vaesimcq_u8(vaesdq_u8(b, *round_key));
    }
    vaesdq_u8(b, round_keys[N - 2])
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::aarch64::vpaes_armv8::{VpaesDecKey, VpaesKey};

    // Every other test sees only the path the CPU picks, so each path is
    // compared here with a model chaining single blocks, for each key size,
    // at lengths around the eight-block loop and its tail.
    #[test]
    fn paths_match() {
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for (key_len, seed) in [16, 24, 32].into_iter().zip(1..) {
            let key = bytes(key_len, seed);
            let model = VpaesKey::new(&key);
            let mut paths = vec![(
                AesKey::Vpaes(VpaesKey::new(&key)),
                AesDecKey::Vpaes(VpaesDecKey::new(&key)),
            )];
            let enc = AesKey::new(&key);
            if matches!(enc, AesKey::Hw(_)) {
                paths.push((enc, AesDecKey::new(&key)));
            }
            let iv: [u8; 16] = bytes(16, seed + 7).try_into().unwrap();
            for blocks in [0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 23] {
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
