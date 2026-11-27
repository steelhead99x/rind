module
public import Aeneas
public import Rind.X86_64.Types
public import Rind.X86_64.PointSelectModel
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# RSA's AVX2 gather, modelled by hand

`mont_exp`'s AVX2 gather loads through raw pointers, splits `z` with
`chunks_mut`, and picks a const generic by each block's length, which Aeneas
cannot translate, so the translation leaves `gather_avx2` opaque and this file
models it over `Rind.X86_64.Simd`'s intrinsics. `admin/prove` fails unless
these quotes are still that Rust, so a change to it is a change to this model:

```rust
fn gather_avx2(z: &mut [u64], powers: &[u64], i: u64, _token: HaveAvx2) {
    let w = z.len();
    assert!(w.is_multiple_of(4) && powers.len() == 32 * w);
    // Each block of up to 16 words holds its vectors in registers across
    // all 32 rows.
    for (b, block) in z.chunks_mut(16).enumerate() {
        // SAFETY: `_token` proves the CPU has AVX2.
        unsafe {
            match block.len() {
                16 => gather_columns::<4>(block, powers, 16 * b, i),
                12 => gather_columns::<3>(block, powers, 16 * b, i),
                8 => gather_columns::<2>(block, powers, 16 * b, i),
                _ => gather_columns::<1>(block, powers, 16 * b, i),
            }
        }
    }
}

#[target_feature(enable = "avx,avx2")]
fn gather_columns<const V: usize>(z: &mut [u64], powers: &[u64], col: usize, i: u64) {
    let w = powers.len() / 32;
    assert!(z.len() == 4 * V && col + 4 * V <= w);
    let want = _mm256_set1_epi64x(i as i64);
    let one = _mm256_set1_epi64x(1);
    let mut index = _mm256_setzero_si256();
    let mut acc = [_mm256_setzero_si256(); V];
    let mut words = powers[col..].as_ptr();
    for _ in 0..32 {
        let mask = _mm256_cmpeq_epi64(index, want);
        index = _mm256_add_epi64(index, one);
        for (j, acc) in acc.iter_mut().enumerate() {
            // SAFETY: `words` is column `col` of one of the 32 rows of `w`
            // words, and `col + 4 * j + 4 <= w`.
            let word = unsafe { _mm256_loadu_si256(words.add(4 * j).cast()) };
            *acc = _mm256_or_si256(*acc, _mm256_and_si256(word, mask));
        }
        words = words.wrapping_add(w);
    }
    for (j, acc) in acc.iter().enumerate() {
        // SAFETY: `z` holds `4 * V` words, and `4 * j + 4 <= 4 * V`.
        unsafe { _mm256_storeu_si256(z.as_mut_ptr().add(4 * j).cast(), *acc) };
    }
}

```

The model differs from that Rust only in form:

- `words` is the word `powers[r * w + col]` in pass `r`, so an unaligned load
  of 256 bits from `words.add(4 * j)` is `load256 powers (r * w + col + 4 * j)`:
  the 4 words from there, lowest first. A store writes an accumulator's 64-bit
  lanes to `z` in order, lane 0 first, and the stores write every word of the
  block, so the model builds the block from them.
- The loop over the 32 rows is a fold, and the inner loop over the
  accumulators a `mapM`.
- `chunks_mut(16).enumerate()` is block `b` below `⌈w / 16⌉`, the up to 16
  words of `z` from `16 * b`.
- `i as i64` keeps its bits.

`Rind.X86_64.RsaGather` proves it.
-/

namespace rind.x86_64

open rind.simd

/-- One pass `r` of `gather_columns::<V>`'s loop over the rows of `w` words:
the row's mask, where the counter `index` equals `want`, picks its `4 * V`
words from column `col` into the accumulators, and the counter steps by
`one`. -/
def low.x86_64.mont_exp.gather_row (V w col : Nat) (powers : List U64)
    (want one : core.core_arch.x86.__m256i)
    (st : core.core_arch.x86.__m256i × List core.core_arch.x86.__m256i) (r : Nat) :
    Result (core.core_arch.x86.__m256i × List core.core_arch.x86.__m256i) := do
  let mask ← core.core_arch.x86.avx2._mm256_cmpeq_epi64 st.1 want
  let index ← core.core_arch.x86.avx2._mm256_add_epi64 st.1 one
  let acc ← (List.range V).mapM fun j => do
    let word ← core.core_arch.x86.avx2._mm256_and_si256 (load256 powers (r * w + col + 4 * j)) mask
    core.core_arch.x86.avx2._mm256_or_si256 (st.2.getD j 0) word
  ok (index, acc)

/-- `gather_columns::<V>`: the `4 * V` words it stores into `z`. -/
def low.x86_64.mont_exp.gather_columns (V : Nat) (z powers : List U64) (col : Nat) (i : U64) :
    Result (List U64) :=
  let w := powers.length / 32
  if z.length = 4 * V ∧ col + 4 * V ≤ w then do
    let want ← core.core_arch.x86.avx._mm256_set1_epi64x ⟨i.bv⟩
    let one ← core.core_arch.x86.avx._mm256_set1_epi64x 1#i64
    let zero ← core.core_arch.x86.avx._mm256_setzero_si256
    let st ← (List.range 32).foldlM (low.x86_64.mont_exp.gather_row V w col powers want one)
      (zero, List.replicate V zero)
    ok (st.2.flatMap store256)
  else fail .panic

/-- The vectors `gather_avx2`'s `match` takes for a block of `len` words. -/
def low.x86_64.mont_exp.gather_vectors : Nat → Nat
  | 16 => 4
  | 12 => 3
  | 8 => 2
  | _ => 1

/-- `gather_avx2`, with `gather_columns`'s blocks joined into `z`. -/
def low.x86_64.mont_exp.gather_avx2 (z powers : Slice U64) (i : U64)
    (_token : low.x86_64.cpu.HaveAvx2) : Result (Slice U64) :=
  if z.length % 4 = 0 ∧ powers.length = 32 * z.length then do
    let blocks ← (List.range ((z.length + 15) / 16)).mapM fun b =>
      let block := (z.val.drop (16 * b)).take 16
      low.x86_64.mont_exp.gather_columns (low.x86_64.mont_exp.gather_vectors block.length) block
        powers.val (16 * b) i
    let out := blocks.flatten
    if h : out.length = z.length then ok (Slice.from out (by rw [h]; exact z.property)) else fail .panic
  else fail .panic

end rind.x86_64
