module
public import Aeneas
public import Rind.Aarch64.Types
public import Rind.Aarch64.Neon
public import Rind.RowSelect
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# rind's aarch64 point select, modelled by hand

P-384's comb table's row select loads through raw pointers and splits the
table with `as_chunks`, which Aeneas cannot translate, so the translation
leaves it opaque and this file models it over `Rind.Aarch64.Neon`'s
intrinsics. `admin/prove` fails unless these quotes are still that Rust, so
a change to it is a change to this model:

```rust
pub(crate) fn bignum_aff_point_select_p384(z: &mut [u64; 12], table: &[u64], index: u8) {
    select::<12, 6>(z, table, index)
}

fn select<const N: usize, const V: usize>(z: &mut [u64; N], table: &[u64], index: u8) {
    const { assert!(N == 2 * V) };
    // SAFETY: crate requires `neon` cpu feature
    unsafe { _select::<N, V>(z, table, index) }
}

#[target_feature(enable = "neon")]
fn _select<const N: usize, const V: usize>(z: &mut [u64; N], table: &[u64], index: u8) {
    // SAFETY: uint32x4_t and u128 have the same number and meaning of bits
    let mut acc: [uint32x4_t; V] = [unsafe { mem::transmute::<u128, uint32x4_t>(0) }; V];

    let desired_index = vdupq_n_u32(index as u32);
    let ones = vdupq_n_u32(1);
    let mut index = ones;

    let (rows, _) = table.as_chunks::<N>();
    for row in rows {
        let mask = vceqq_u32(index, desired_index);
        index = vaddq_u32(index, ones);

        for (i, acc) in acc.iter_mut().enumerate() {
            // SAFETY: `row` is `N` readable words, and `2 * i + 2 <= N`
            let word = unsafe { vld1q_u32(row.as_ptr().add(2 * i).cast()) };
            *acc = veorq_u32(*acc, vandq_u32(word, mask));
        }
    }

    for (i, acc) in acc.iter().enumerate() {
        // SAFETY: `z` is `N` writable words, and `2 * i + 2 <= N`
        unsafe { vst1q_u32(z.as_mut_ptr().add(2 * i).cast(), *acc) };
    }
}

```

The model differs from that Rust only in form:

- `vld1q_u32` from `row.as_ptr().add(k)` is the 2 words from `row[k]`,
  `row[k]` lowest, as aarch64 is little-endian, and `vst1q_u32` writes an
  accumulator's 64-bit lanes to `z` in order, lane 0 first. The stores write
  every word of `z`, where the `const` assertion holds, so the model builds
  `z` from them; where it does not, the Rust does not compile, and the model
  panics.
- The zero `transmute` is the zero vector.
- `as_chunks` is the list of whole rows, and the loop over the rows, with the
  inner loop over the accumulators, is a fold.
- `index as u32` zero-extends.

`Rind.Aarch64.PointSelect` proves it.
-/

namespace rind.aarch64

open rind.simd rind.select

/-- One pass of `_select`'s loop over the rows: the row's mask, where the
counter `index` equals `desired`, picks its words into the accumulators, and
the counter steps by `ones`. -/
def low.aarch64.bignum_point_select.select_row (V : Nat)
    (desired ones : core.core_arch.arm_shared.neon.uint32x4_t)
    (st : core.core_arch.arm_shared.neon.uint32x4_t × List core.core_arch.arm_shared.neon.uint32x4_t)
    (row : List U64) :
    Result (core.core_arch.arm_shared.neon.uint32x4_t × List core.core_arch.arm_shared.neon.uint32x4_t) := do
  let mask ← core.core_arch.arm_shared.neon.generated.vceqq_u32 st.1 desired
  let index ← core.core_arch.arm_shared.neon.generated.vaddq_u32 st.1 ones
  let acc ← (List.range V).mapM fun i => do
    let word ← core.core_arch.arm_shared.neon.generated.vandq_u32 (load128 row (2 * i)) mask
    core.core_arch.arm_shared.neon.generated.veorq_u32 (st.2.getD i 0) word
  ok (index, acc)

/-- `select::<N, V>`, with `_select` inlined. `N = 0` panics, as
`as_chunks::<0>` does. -/
def low.aarch64.bignum_point_select.select (N : Std.Usize) (V : Nat)
    (_z : Std.Array U64 N) (table : Slice U64) (index : U8) : Result (Std.Array U64 N) :=
  if 0 < N.val ∧ N.val = 2 * V then do
    let desired ← core.core_arch.arm_shared.neon.generated.vdupq_n_u32 ⟨index.bv.setWidth 32⟩
    let ones ← core.core_arch.arm_shared.neon.generated.vdupq_n_u32 1#u32
    let rows := (List.range (table.val.length / N.val)).map (row N.val table.val)
    let st ← rows.foldlM (low.aarch64.bignum_point_select.select_row V desired ones)
      (ones, List.replicate V 0)
    let out := st.2.flatMap store128
    if h : out.length = N.val then ok (Std.Array.from out h) else fail .panic
  else fail .panic

/-- `bignum_aff_point_select_p384`. -/
def low.aarch64.bignum_point_select.bignum_aff_point_select_p384 (z : Std.Array U64 12#usize)
    (table : Slice U64) (index : U8) : Result (Std.Array U64 12#usize) :=
  low.aarch64.bignum_point_select.select 12#usize 6 z table index

end rind.aarch64
