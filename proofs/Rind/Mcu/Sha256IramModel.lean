module
public import Aeneas
public import Rind.Mcu.Types
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# The IRAM SHA-256's cursors and window, modelled by hand

`low/portable/sha256_iram.rs` reads SHA-256's constants and the message's
blocks through raw pointers, and keeps its schedule window in `MaybeUninit`
slots, which Aeneas cannot translate, so the translation leaves these types'
methods opaque and this file models them. `admin/prove` fails unless these
quotes are still that Rust, so a change to it is a change to this model:

```rust
struct RoundConstants(*const u32);

impl RoundConstants {
    /// The first sixteen words of `k`, which is always `K`: a parameter so
    /// that the translation passes its own `K` to the model.
    #[inline(always)]
    fn first(k: &'static [u32; 64]) -> Self {
        Self(k.as_ptr())
    }

    /// Word `I` of the sixteen from `self`.
    ///
    /// # Safety
    ///
    /// `self` is at `k[0]`, `k[16]`, `k[32]`, or `k[48]` of the table it
    /// started at, and `I < 16`.
    #[inline(always)]
    unsafe fn get<const I: usize>(self) -> u32 {
        // SAFETY: `self.0.add(I)` stays inside `K`, as the caller promises.
        // `K` is aligned for `u32`, and `I` is a constant. The load does
        // not depend on the message or the state.
        unsafe { self.0.add(I).read() }
    }

    /// The next sixteen words.
    ///
    /// # Safety
    ///
    /// `self` is at `K[0]`, `K[16]`, `K[32]`, or `K[48]`. The result may be
    /// one past the end of `K`, which is not read.
    #[inline(always)]
    unsafe fn next(self) -> Self {
        // SAFETY: the caller's start plus 16 is at most 64, `K`'s length.
        Self(unsafe { self.0.add(16) })
    }
}

struct Window([core::mem::MaybeUninit<u32>; 16]);

impl Window {
    #[inline(always)]
    fn new() -> Self {
        Self([const { core::mem::MaybeUninit::uninit() }; 16])
    }

    #[inline(always)]
    fn set(&mut self, slot: usize, w: u32) {
        self.0[slot].write(w);
    }

    /// The word in `slot`.
    ///
    /// # Safety
    ///
    /// `slot` has been written.
    #[inline(always)]
    unsafe fn get(&self, slot: usize) -> u32 {
        // SAFETY: the caller's promise.
        unsafe { self.0[slot].assume_init() }
    }
}

struct Blocks<'a> {
    ptr: *const u8,
    _blocks: core::marker::PhantomData<&'a [u8]>,
}

impl<'a> Blocks<'a> {
    #[inline(always)]
    fn new(blocks: &'a [u8]) -> Self {
        Self {
            ptr: blocks.as_ptr(),
            _blocks: core::marker::PhantomData,
        }
    }

    /// The block at `self`.
    ///
    /// # Safety
    ///
    /// The 64 bytes at `self` are inside the slice.
    #[inline(always)]
    unsafe fn block(&self) -> &'a [u8; 64] {
        // SAFETY: the caller's promise. The block may be unaligned. On
        // Xtensa, `message_word` loads it with `l32i`, which these cores
        // perform unaligned in hardware; other targets read it as bytes.
        // The slice is borrowed for `'a` and not mutated through this.
        unsafe { &*self.ptr.cast::<[u8; 64]>() }
    }

    /// Steps to the next block.
    ///
    /// # Safety
    ///
    /// The 64 bytes at `self` are inside the slice, so the next block
    /// starts inside it or exactly one past its end.
    #[inline(always)]
    unsafe fn next(&mut self) {
        // SAFETY: the caller's promise.
        self.ptr = unsafe { self.ptr.add(64) };
    }
}

```

Each model fails where the Rust would be undefined, so a proof that the code
using them succeeds shows that it keeps their safety contracts:

- A `RoundConstants` is its table and the index it points to. `get` fails past
  the table's end, and `next` past one beyond it.
- A `Window` slot holds `none` until written, and `get` fails on one, as
  `assume_init` would be undefined.
- A `Blocks` is its slice and the offset it points to. `block` fails unless
  the 64 bytes there are inside the slice, and `next` likewise.
-/

namespace rind.mcu

/-- `RoundConstants::first`: the table, at index 0. -/
def low.portable.sha.iram.RoundConstants.first (k : Std.Array Std.U32 64#usize) :
    Result low.portable.sha.iram.RoundConstants :=
  ok (k, 0)

/-- `RoundConstants::get::<I>`: the word `I` past the cursor. -/
def low.portable.sha.iram.RoundConstants.get (I : Std.Usize) (c : low.portable.sha.iram.RoundConstants) :
    Result Std.U32 :=
  if h : c.2 + I.val < 64 then ok (c.1.val[c.2 + I.val]'(by simp; omega)) else fail .undef

/-- `RoundConstants::next`: sixteen words on, at most one past the end. -/
def low.portable.sha.iram.RoundConstants.next (c : low.portable.sha.iram.RoundConstants) :
    Result low.portable.sha.iram.RoundConstants :=
  if c.2 + 16 ≤ 64 then ok (c.1, c.2 + 16) else fail .undef

/-- `Window::new`: sixteen slots not yet written. -/
def low.portable.sha.iram.Window.new : Result low.portable.sha.iram.Window :=
  ok (Std.Array.repeat 16#usize none)

/-- `Window::set`: `w` written into `slot`, which panics past the end. -/
def low.portable.sha.iram.Window.set (x : low.portable.sha.iram.Window) (slot : Std.Usize)
    (w : Std.U32) : Result low.portable.sha.iram.Window :=
  Std.Array.update x slot (some w)

/-- `Window::get`: the word in `slot`, which panics past the end and is
undefined before it is written. -/
def low.portable.sha.iram.Window.get (x : low.portable.sha.iram.Window) (slot : Std.Usize) :
    Result Std.U32 := do
  let o ← Std.Array.index_usize x slot
  match o with
  | some w => ok w
  | none => fail .undef

/-- `Blocks::new`: the slice, at offset 0. -/
def low.portable.sha.iram.Blocks.new (blocks : Slice Std.U8) : Result low.portable.sha.iram.Blocks :=
  ok (blocks, 0)

/-- `Blocks::block`: the 64 bytes at the cursor. -/
def low.portable.sha.iram.Blocks.block (c : low.portable.sha.iram.Blocks) :
    Result (Std.Array Std.U8 64#usize) :=
  if h : c.2 + 64 ≤ c.1.length then
    ok (Array.from ((c.1.val.drop c.2).take 64) (by simp [Slice.length] at h ⊢; omega))
  else fail .undef

/-- `Blocks::next`: 64 bytes on, still inside the slice or one past it. -/
def low.portable.sha.iram.Blocks.next (c : low.portable.sha.iram.Blocks) :
    Result low.portable.sha.iram.Blocks :=
  if c.2 + 64 ≤ c.1.length then ok (c.1, c.2 + 64) else fail .undef

end rind.mcu
