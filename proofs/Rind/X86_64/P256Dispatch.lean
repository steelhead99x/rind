module
public import Rind.X86_64.Funs
@[expose] public section
open Aeneas Aeneas.Std Result

/-!
# P-256's key generation, modelled by hand

`p256::PrivateKey::generate` draws through a `dyn RandomSource`, which Aeneas
cannot translate, so the translation leaves it and `new_random` opaque, and
this file models them above the translated `PrivateKey::from_bytes`, for
`Rind.X86_64.Dispatch` to use as P-256's `Agree::random`. `admin/prove` fails
unless this quote is still that Rust, so a change to it is a change to this
model:

```rust
    pub(crate) fn new_random() -> Result<Self, Error> {
        Self::generate(&mut SystemRandom)
    }

    pub(crate) fn generate(rng: &mut dyn RandomSource) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        for _ in 0..64 {
            let mut r = [0u8; Scalar::BYTES];
            rng.fill(&mut r)?;
            low::ct::secret_slice(&r);
            if let Ok(p) = Self::from_bytes(&r) {
                return Ok(p);
            }
        }

        Err(Error::RngFailed)
    }

impl RandomSource for SystemRandom {
    fn fill(&mut self, out: &mut [u8]) -> Result<(), Error> {
        getrandom::fill(out).map_err(|_| Error::RngFailed)
    }
}

```

The model departs from the Rust in three ways, and adds no axiom:

- `rng` is the `SystemRandom` that `new_random` passes, the only source key
  agreement draws from.
- Its `fill` calls on the system source, `getrandom::fill`, which the
  translation models as a function of its buffer alone, so each call would
  return the same bytes. The loop's `i`th call is instead `draw i`, opaque, so
  successive draws are independent.
- `low::ct::secret_slice`, a ctgrind marker that computes nothing, is left out.
-/

namespace rind.x86_64

/-- What the system source, `getrandom::fill`, writes to the buffer it is
given on the `i`th draw of one key generation, and whether it failed. Opaque:
the functional spec leaves the draws out. -/
opaque mid.p256.PrivateKey.draw :
    Nat → Slice Std.U8 → Result ((core.result.Result Unit getrandom.error.Error) × Slice Std.U8)

/-- The loop of `p256::PrivateKey::generate`, from its `i`th draw, with `n`
draws left. -/
def mid.p256.PrivateKey.generate_loop (i : Nat) :
    Nat → Result (core.result.Result mid.p256.PrivateKey error.Error)
  | 0 => ok (.Err .RngFailed)
  | n + 1 => do
    let r := Array.repeat 32#usize 0#u8
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut r)
    let (r1, s1) ← mid.p256.PrivateKey.draw i s
    match r1 with
    | .Err _ => ok (.Err .RngFailed)
    | .Ok () =>
      let p ← mid.p256.PrivateKey.from_bytes (to_slice_mut_back s1).to_slice
      match p with
      | .Ok p => ok (.Ok p)
      | .Err _ => mid.p256.PrivateKey.generate_loop (i + 1) n

/-- `p256::PrivateKey::generate(&mut SystemRandom)`, which `new_random` is. -/
def mid.p256.PrivateKey.generate :
    Result (core.result.Result mid.p256.PrivateKey error.Error) := do
  let _ ← low.entry.Entry.new_secret
  mid.p256.PrivateKey.generate_loop 0 64

end rind.x86_64
