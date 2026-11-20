// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// Keccak-f1600 on four states kept interleaved, lane `i` of state `j` at
/// `s[i][j]`, as SLH-DSA's four-way SHAKE holds them: in place with AVX2 on
/// x86_64, else moved into four separate states and back around the
/// backend's four-way permutation.
pub(crate) fn sha3_keccak4x_f1600(s: &mut [[u64; 4]; 25], rc: &[u64; 24]) {
    #[cfg(rind_backend = "x86_64")]
    if let Some(avx2) = super::super::x86_64::cpu::HaveAvx2::check() {
        return super::super::x86_64::sha3_keccak4x_avx2::sha3_keccak4x_f1600(avx2, s, rc);
    }
    let mut states: [[u64; 25]; 4] = core::array::from_fn(|j| core::array::from_fn(|i| s[i][j]));
    super::super::sha3_keccak4_f1600(&mut states, rc);
    *s = core::array::from_fn(|i| core::array::from_fn(|j| states[j][i]));
}

/// Four states that each absorb one block, `blocks[j]` (the padded SHAKE256
/// rate of state `j`, the capacity zero), are permuted once, and the first 32
/// bytes of each are returned: only with AVX2, which builds and unbuilds the
/// interleaved states in registers; otherwise `None`.
pub(crate) fn sha3_keccak4x_hash_blocks(
    blocks: &[[u8; 136]; 4],
    rc: &[u64; 24],
) -> Option<[[u8; 32]; 4]> {
    #[cfg(rind_backend = "x86_64")]
    if let Some(avx2) = super::super::x86_64::cpu::HaveAvx2::check() {
        return Some(
            super::super::x86_64::sha3_keccak4x_avx2::sha3_keccak4x_hash_blocks(avx2, blocks, rc),
        );
    }
    let _ = (blocks, rc);
    None
}

/// Whether eight SHAKE256 blocks hash at once: with AVX-512 on cores other
/// than Intel's, which may lower their clock for 512-bit vectors (the
/// avoid-zmm quest) and where eight-way is unmeasured.
pub(crate) fn sha3_keccak8x_available() -> bool {
    #[cfg(rind_backend = "x86_64")]
    {
        use super::super::x86_64::cpu;
        cpu::HaveAvx512Vl::check().is_some() && (!cpu::is_intel() || forced_for_test())
    }
    #[cfg(not(rind_backend = "x86_64"))]
    false
}

#[cfg(all(test, rind_backend = "x86_64"))]
std::thread_local! {
    static FORCED: core::cell::Cell<bool> = const { core::cell::Cell::new(false) };
}

/// Whether a test on this thread has [`with_keccak8x_forced`], so the eight-way
/// path runs on an Intel core too, as under Intel SDE's models, which are all
/// Intel's. Never true outside a test build, so the selection rule above is
/// what ships.
#[cfg(rind_backend = "x86_64")]
#[inline(always)]
fn forced_for_test() -> bool {
    #[cfg(test)]
    return FORCED.with(core::cell::Cell::get);
    #[cfg(not(test))]
    false
}

/// Runs `f` with [`sha3_keccak8x_available`] true wherever the CPU has AVX-512
/// VL, Intel's cores included, for the tests that check the eight-way path
/// against the interleaved one under SDE.
#[cfg(all(test, rind_backend = "x86_64"))]
pub(crate) fn with_keccak8x_forced<R>(f: impl FnOnce() -> R) -> R {
    struct Reset(bool);
    impl Drop for Reset {
        fn drop(&mut self) {
            FORCED.with(|forced| forced.set(self.0));
        }
    }
    let _reset = Reset(FORCED.with(|forced| forced.replace(true)));
    f()
}

/// Eight states that each absorb one block, `blocks[j]` (the padded SHAKE256
/// rate of state `j`, the capacity zero), are permuted once, and the first 32
/// bytes of each are returned, where [`sha3_keccak8x_available`]; otherwise
/// `None`.
pub(crate) fn sha3_keccak8x_hash_blocks(
    blocks: &[[u8; 136]; 8],
    rc: &[u64; 24],
) -> Option<[[u8; 32]; 8]> {
    #[cfg(rind_backend = "x86_64")]
    if sha3_keccak8x_available() {
        let vl = super::super::x86_64::cpu::HaveAvx512Vl::check()?;
        return Some(
            super::super::x86_64::sha3_keccak8x_avx512::sha3_keccak8x_hash_blocks(vl, blocks, rc),
        );
    }
    let _ = (blocks, rc);
    None
}
