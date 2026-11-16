import Rind.X86_64.Funs
open Aeneas Aeneas.Std Result

/-!
# The signature modules' `Buffer::write`, modelled by hand

`Buffer::write` takes a closure that returns a borrow of its argument, which
Aeneas cannot translate, so this file models it for the ECDSA and RSA models.
`admin/prove` fails unless this quote is still that Rust, so a change to it is
a change to this model:

```rust
impl<const N: usize> Buffer<N> {
    fn new() -> Self {
        Self {
            bytes: [0; N],
            len: 0,
        }
    }

    /// Runs `write`, which writes to the start of its argument and returns
    /// the written span.
    pub(super) fn write(
        write: impl FnOnce(&mut [u8]) -> Result<&[u8], Error>,
    ) -> Result<Self, Error> {
        let mut buffer = Self::new();
        buffer.len = write(&mut buffer.bytes)?.len();
        Ok(buffer)
    }

    /// Runs `encode` as [`Self::write`] does, for an encoder `N` is sized
    /// for.
    ///
    /// Every `N` holds the encoding of the largest key a loader accepts, so
    /// an encoder that runs out of room is a bug in rind, not bad input.
    pub(super) fn encode(encode: impl FnOnce(&mut [u8]) -> Result<&[u8], Error>) -> Self {
        Self::write(encode).expect("sized for the largest key")
    }
}

```

`write` is a Lean function that returns its result and its argument's final
bytes, as the translation returns those of a function taking `&mut [u8]`.
`Buffer::new` is translated, and `encode`, which no theorem here is about, is
quoted only because it shares the `impl`. `?` is a `match`, since the error it
passes on is already an `Error`.
-/

namespace rind.x86_64

/-- `Buffer::write`, with `write` a Lean function. -/
def high.signature.Buffer.write (N : Std.Usize)
    (write : Slice Std.U8 → Result (core.result.Result (Slice Std.U8) error.Error × Slice Std.U8)) :
    Result (core.result.Result (high.signature.Buffer N) error.Error) := do
  let buffer ← high.signature.Buffer.new N
  let (s, to_slice_mut_back) ← lift (Array.to_slice_mut buffer.bytes)
  let r ← write s
  match r.1 with
  | .Ok span => ok (.Ok { bytes := to_slice_mut_back r.2, len := span.len })
  | .Err e => ok (.Err e)

/-- `Buffer`'s `AsRef<[u8]>` returns the first `len` bytes. -/
@[step]
theorem buffer_as_ref_spec {M : Usize} (w : high.signature.Buffer M) (h : w.len.val ≤ M.val) :
    high.signature.Buffer.Insts.CoreConvertAsRefSliceU8.as_ref w ⦃ s =>
      s.val = w.bytes.val.take w.len.val ⦄ := by
  unfold high.signature.Buffer.Insts.CoreConvertAsRefSliceU8.as_ref
  step*
  simp [s_post, List.slice, Array.val_to_slice]

end rind.x86_64
