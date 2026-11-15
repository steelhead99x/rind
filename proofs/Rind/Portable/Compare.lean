module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# The portable backend's constant-time compares, modelled by hand

`low::generic::ct_equal` compares two slices through these. The first reads
through raw pointers, and the second folds its difference behind
`black_box`, which Aeneas cannot translate, so this file models them.
`admin/prove` fails unless these quotes are still that Rust, so a change to
it is a change to this model:

```rust
pub(in crate::low) fn ct_compare_bytes(a: &[u8], b: &[u8]) -> u8 {
    let (len, a, b) = (a.len().min(b.len()), a.as_ptr(), b.as_ptr());
    let mut acc = 0;
    for i in 0..len {
        // SAFETY: both hold `len` readable bytes, and a
        // volatile read is one the compiler must keep, so it cannot stop
        // early once `acc` has every bit set.
        acc |= unsafe { a.add(i).read_volatile() ^ b.add(i).read_volatile() };
    }
    acc
}

pub(in crate::low) fn ct_compare_16(a: &[u8; 16], b: &[u8; 16]) -> usize {
    let diff = core::hint::black_box(u128::from_ne_bytes(*a) ^ u128::from_ne_bytes(*b));
    let diff = diff as u64 | (diff >> 64) as u64;
    (diff as u32 | (diff >> 32) as u32) as usize
}

```

The model departs from the Rust in two ways, and adds no axiom:

- The volatile reads and `black_box` are the values they read and pass on:
  they keep the compiler from changing the code, not what it computes.
- `u128::from_ne_bytes` reads little-endian, as on x86_64, which the
  translation targets. A big-endian target reads both blocks the other way,
  which changes the value but not whether it is zero, all a caller reads.
-/

namespace rind.portable

/-- `ct_compare_bytes`: the OR of the XORs of the byte pairs up to the shorter
length. -/
def low.portable.cpu.ct_compare_bytes (a b : Slice Std.U8) : Result Std.U8 :=
  ok ((List.zipWith (· ^^^ ·) a.val b.val).foldl (· ||| ·) 0#u8)

/-- `ct_compare_16`: the XOR of the blocks as little-endian 128-bit words,
folded to 64 bits, then to 32. -/
def low.portable.cpu.ct_compare_16 (a b : Std.Array Std.U8 16#usize) : Result Std.Usize :=
  let diff : BitVec 128 :=
    (BitVec.fromLEBytes (a.val.map (·.bv))).setWidth 128 ^^^
      (BitVec.fromLEBytes (b.val.map (·.bv))).setWidth 128
  let diff : BitVec 64 := diff.setWidth 64 ||| (diff >>> 64).setWidth 64
  ok ⟨(diff.setWidth 32 ||| (diff >>> 32).setWidth 32).setWidth _⟩

end rind.portable
