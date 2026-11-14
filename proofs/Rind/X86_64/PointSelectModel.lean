module
public import Aeneas
public import Rind.X86_64.Types
public import Rind.X86_64.AesGcmModel
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# rind's x86_64 point select, modelled by hand

The P-256, P-384, and P-521 generator tables' row selects load through raw
pointers and split the table with `as_chunks`, which Aeneas cannot translate,
so the translation leaves them opaque and this file models them over
`Rind.X86_64.Simd`'s intrinsics. `admin/prove` fails unless these quotes are
still that Rust, so a change to it is a change to this model:

```rust
pub(crate) fn bignum_aff_point_select_p384(z: &mut [u64; 12], table: &[u64], index: u8) {
    match HaveAvx2::check() {
        Some(token) => select_avx2::<12, 3>(z, table, index, token),
        // SAFETY: every x86_64 CPU has SSE2
        None => unsafe { select_sse2::<12, 6>(z, table, index) },
    }
}

pub(crate) fn bignum_aff_point_select_p256(z: &mut [u64; 8], table: &[u64], index: u8) {
    match HaveAvx2::check() {
        Some(token) => select_avx2::<8, 2>(z, table, index, token),
        // SAFETY: every x86_64 CPU has SSE2
        None => unsafe { select_sse2::<8, 4>(z, table, index) },
    }
}

pub(crate) fn bignum_aff_point_select_p521(z: &mut [u64; 18], table: &[u64], index: u8) {
    match HaveAvx2::check() {
        Some(token) => select_avx2::<18, 4>(z, table, index, token),
        // SAFETY: every x86_64 CPU has SSE2
        None => unsafe { select_sse2::<18, 9>(z, table, index) },
    }
}

fn select_avx2<const N: usize, const V: usize>(
    z: &mut [u64; N],
    table: &[u64],
    index: u8,
    _token: HaveAvx2,
) {
    const { assert!(N == 4 * V || N == 4 * V + 2) };
    // SAFETY: `_token` proves the `avx` and `avx2` cpu features
    unsafe { _select_avx2::<N, V>(z, table, index) }
}

#[target_feature(enable = "avx,avx2")]
fn _select_avx2<const N: usize, const V: usize>(z: &mut [u64; N], table: &[u64], index: u8) {
    super::cpu::prefetch(table, N);

    let mut acc = [_mm256_setzero_si256(); V];
    let mut tail = _mm_setzero_si128();

    let desired_index = _mm256_set1_epi32(index as i32);
    let ones = _mm256_set1_epi32(1);
    let mut index = ones;

    let (rows, _) = table.as_chunks::<N>();
    for row in rows {
        let mask = _mm256_cmpeq_epi32(index, desired_index);
        index = _mm256_add_epi32(index, ones);

        for (i, acc) in acc.iter_mut().enumerate() {
            // SAFETY: `row` is `N` readable words, and `4 * i + 4 <= N`
            let word = unsafe { _mm256_loadu_si256(row.as_ptr().add(4 * i).cast()) };
            *acc = _mm256_xor_si256(*acc, _mm256_and_si256(word, mask));
        }
        if N > 4 * V {
            // SAFETY: `row` is `N` readable words, and `N == 4 * V + 2`
            let word = unsafe { _mm_loadu_si128(row.as_ptr().add(4 * V).cast()) };
            tail = _mm_xor_si128(tail, _mm_and_si128(word, _mm256_castsi256_si128(mask)));
        }
    }

    for (i, acc) in acc.iter().enumerate() {
        // SAFETY: `z` is `N` writable words, and `4 * i + 4 <= N`
        unsafe { _mm256_storeu_si256(z.as_mut_ptr().add(4 * i).cast(), *acc) };
    }
    if N > 4 * V {
        // SAFETY: `z` is `N` writable words, and `N == 4 * V + 2`
        unsafe { _mm_storeu_si128(z.as_mut_ptr().add(4 * V).cast(), tail) };
    }
}

#[target_feature(enable = "sse2")]
fn select_sse2<const N: usize, const V: usize>(z: &mut [u64; N], table: &[u64], index: u8) {
    const { assert!(N == 2 * V) };
    super::cpu::prefetch(table, N);

    let mut acc = [_mm_setzero_si128(); V];

    let desired_index = _mm_set1_epi32(index as i32);
    let ones = _mm_set1_epi32(1);
    let mut index = ones;

    let (rows, _) = table.as_chunks::<N>();
    for row in rows {
        let mask = _mm_cmpeq_epi32(index, desired_index);
        index = _mm_add_epi32(index, ones);

        for (i, acc) in acc.iter_mut().enumerate() {
            // SAFETY: `row` is `N` readable words, and `2 * i + 2 <= N`
            let word = unsafe { _mm_loadu_si128(row.as_ptr().add(2 * i).cast()) };
            *acc = _mm_xor_si128(*acc, _mm_and_si128(word, mask));
        }
    }

    for (i, acc) in acc.iter().enumerate() {
        // SAFETY: `z` is `N` writable words, and `2 * i + 2 <= N`
        unsafe { _mm_storeu_si128(z.as_mut_ptr().add(2 * i).cast(), *acc) };
    }
}

pub(crate) fn prefetch<T>(table: &[T], stride: usize) {
    // `_mm_prefetch` is safe on newer Rust but `unsafe` on the 1.90 MSRV.
    #[allow(unused_unsafe)]
    // SAFETY: a prefetch never faults and is not architecturally visible.
    unsafe {
        _mm_prefetch(table.as_ptr().cast(), _MM_HINT_T0);
        _mm_prefetch(table.as_ptr().wrapping_add(stride).cast(), _MM_HINT_T0);
    }
}

```

The model differs from that Rust only in form:

- An unaligned load of 256 or 128 bits from `row.as_ptr().add(k)` is the 4
  or 2 words from `row[k]`, `row[k]` lowest, and a store of an accumulator
  writes its 64-bit lanes to `z` in order, lane 0 first. The stores write
  every word of `z`, where the `const` assertion holds, so the model builds
  `z` from them; where it does not, the Rust does not compile, and the model
  panics.
- `as_chunks` is `chunksOf`, and the loop over the rows, with the inner loop
  over the accumulators, is a fold.
- `prefetch`, which changes no state, is left out.
- `index as i32` zero-extends.

`bignum_aff_point_select_p256`, `_p384`, and `_p521`, which dispatch on
`HaveAvx2::check`, are defined in `Rind.X86_64.FunsExternal`, after the check
they call; `Rind.X86_64.PointSelect` proves them.
-/

namespace rind.x86_64

open rind.simd

/-- The four words of `row` from `row[k]`, as `_mm256_loadu_si256` loads them:
`row[k]` lowest. -/
def load256 (row : List U64) (k : Nat) : core.core_arch.x86.__m256i :=
  (row.getD (k + 3) 0#u64).bv ++ (row.getD (k + 2) 0#u64).bv ++ (row.getD (k + 1) 0#u64).bv ++
    (row.getD k 0#u64).bv

/-- The two words of `row` from `row[k]`, as `_mm_loadu_si128` loads them:
`row[k]` lowest. -/
def load128 (row : List U64) (k : Nat) : core.core_arch.x86.__m128i :=
  (row.getD (k + 1) 0#u64).bv ++ (row.getD k 0#u64).bv

/-- A 256-bit vector's words, as `_mm256_storeu_si256` writes them: lane 0
first. -/
def store256 (v : core.core_arch.x86.__m256i) : List U64 :=
  (List.range 4).map fun j => ⟨v.extractLsb' (64 * j) 64⟩

/-- A 128-bit vector's words, as `_mm_storeu_si128` writes them: lane 0
first. -/
def store128 (v : core.core_arch.x86.__m128i) : List U64 :=
  (List.range 2).map fun j => ⟨v.extractLsb' (64 * j) 64⟩

/-- `_select_avx2`'s state between rows: the counter, the `V` accumulators,
and the tail. -/
abbrev Avx2State := core.core_arch.x86.__m256i × List core.core_arch.x86.__m256i ×
  core.core_arch.x86.__m128i

/-- One pass of `_select_avx2`'s loop over the rows: the row's mask, where the
counter `index` equals `desired`, picks its words into the accumulators and,
where `N` is not a multiple of 4, the tail, and the counter steps by `ones`. -/
def low.x86_64.bignum_point_select.select_avx2_row (N V : Nat)
    (desired ones : core.core_arch.x86.__m256i) (st : Avx2State) (row : List U64) :
    Result Avx2State := do
  let mask ← core.core_arch.x86.avx2._mm256_cmpeq_epi32 st.1 desired
  let index ← core.core_arch.x86.avx2._mm256_add_epi32 st.1 ones
  let acc ← (List.range V).mapM fun i => do
    let word ← core.core_arch.x86.avx2._mm256_and_si256 (load256 row (4 * i)) mask
    core.core_arch.x86.avx2._mm256_xor_si256 (st.2.1.getD i 0) word
  let tail ← if N > 4 * V then do
      let low ← core.core_arch.x86.avx._mm256_castsi256_si128 mask
      let word ← core.core_arch.x86.sse2._mm_and_si128 (load128 row (4 * V)) low
      core.core_arch.x86.sse2._mm_xor_si128 st.2.2 word
    else ok st.2.2
  ok (index, acc, tail)

/-- `select_avx2::<N, V>`, with `_select_avx2` inlined. `N = 0` panics, as
`as_chunks::<0>` does. -/
def low.x86_64.bignum_point_select.select_avx2 (N : Std.Usize) (V : Nat)
    (_z : Std.Array U64 N) (table : Slice U64) (index : U8) (_token : low.x86_64.cpu.HaveAvx2) :
    Result (Std.Array U64 N) :=
  if 0 < N.val ∧ (N.val = 4 * V ∨ N.val = 4 * V + 2) then do
    let zero ← core.core_arch.x86.avx._mm256_setzero_si256
    let tail ← core.core_arch.x86.sse2._mm_setzero_si128
    let desired ← core.core_arch.x86.avx._mm256_set1_epi32 ⟨index.bv.setWidth 32⟩
    let ones ← core.core_arch.x86.avx._mm256_set1_epi32 1#i32
    let st ← (chunksOf N.val table.val).foldlM
      (low.x86_64.bignum_point_select.select_avx2_row N.val V desired ones)
      (ones, List.replicate V zero, tail)
    let out := st.2.1.flatMap store256 ++ if N.val > 4 * V then store128 st.2.2 else []
    if h : out.length = N.val then ok (Std.Array.from out h) else fail .panic
  else fail .panic

/-- One pass of `select_sse2`'s loop over the rows, as
`select_avx2_row`'s without a tail. -/
def low.x86_64.bignum_point_select.select_sse2_row (V : Nat)
    (desired ones : core.core_arch.x86.__m128i)
    (st : core.core_arch.x86.__m128i × List core.core_arch.x86.__m128i) (row : List U64) :
    Result (core.core_arch.x86.__m128i × List core.core_arch.x86.__m128i) := do
  let mask ← core.core_arch.x86.sse2._mm_cmpeq_epi32 st.1 desired
  let index ← core.core_arch.x86.sse2._mm_add_epi32 st.1 ones
  let acc ← (List.range V).mapM fun i => do
    let word ← core.core_arch.x86.sse2._mm_and_si128 (load128 row (2 * i)) mask
    core.core_arch.x86.sse2._mm_xor_si128 (st.2.getD i 0) word
  ok (index, acc)

/-- `select_sse2::<N, V>`. `N = 0` panics, as `as_chunks::<0>` does. -/
def low.x86_64.bignum_point_select.select_sse2 (N : Std.Usize) (V : Nat)
    (_z : Std.Array U64 N) (table : Slice U64) (index : U8) : Result (Std.Array U64 N) :=
  if 0 < N.val ∧ N.val = 2 * V then do
    let zero ← core.core_arch.x86.sse2._mm_setzero_si128
    let desired ← core.core_arch.x86.sse2._mm_set1_epi32 ⟨index.bv.setWidth 32⟩
    let ones ← core.core_arch.x86.sse2._mm_set1_epi32 1#i32
    let st ← (chunksOf N.val table.val).foldlM
      (low.x86_64.bignum_point_select.select_sse2_row V desired ones) (ones, List.replicate V zero)
    let out := st.2.flatMap store128
    if h : out.length = N.val then ok (Std.Array.from out h) else fail .panic
  else fail .panic

end rind.x86_64
