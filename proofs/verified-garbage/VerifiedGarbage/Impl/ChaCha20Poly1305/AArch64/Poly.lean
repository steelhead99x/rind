module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Poly1305 in nine registers (AArch64)

A block of Poly1305 absorbed in radix `2⁶⁴` using only the registers that
the eight-block ChaCha20 kernel (`Impl/ChaCha20/AArch64/Mixed8.lean`) leaves
free, so that ChaCha20-Poly1305 can absorb its data while the kernel's
rounds run (`Stitch.lean`).

* `x20` points at the block, and advances past it;
* `x21`, `x22`, `x23` hold the accumulator `h = h₀ + 2⁶⁴ h₁ + 2¹²⁸ h₂`,
  partially reduced (`h₂ ≤ 4`);
* the clamped key `r = r₀ + 2⁶⁴ r₁` is stored at `[x0 + 224]` and
  `[x0 + 232]` (bytes 160–175 of the kernel's working space, which starts 64
  bytes after the ChaCha20 state at `x0`), and each word is loaded into `x24`
  when it is used (there is no register left to keep it in);
* `x25`, `x27`, `x28` and `x30` hold the product `t = t₀ + … + 2¹⁹² t₃`.

As in BoringSSL's `chacha20_poly1305_armv8.pl`: `h += m + 2¹²⁸`; `t = h r`
from the products of `h` with `r₀`, then with `r₁`; then
`h = (t mod 2¹³⁰) + 5 ⌊t / 2¹³⁰⌋`, computed as `t mod 2¹³⁰` plus
`4 ⌊t / 2¹³⁰⌋ = (t₂ & ~3) + 2⁶⁴ t₃` plus `⌊t / 2¹³⁰⌋ = extr(t₃, t₂, 2) +
2⁶⁴ (t₃ >> 2)`. The model has no zero register and no immediate `and`, so
the constants 0, 1 and 3 are moved into registers that are free at that
point.

Only flags and the registers above are written, and memory is only read.
The addresses are `x20` and `x0` plus constants, so only those pointers can
affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.AArch64.Poly

open VG.AArch64

/-- The offsets of the clamped key's words from `x0`. -/
def r0Off : Nat := 224
def r1Off : Nat := 232

/-- `h += m + 2¹²⁸`, for the block `m` at `x20`. -/
def addBlock : List Instr :=
  [.ldr .x .x25 .x20 0, .ldr .x .x27 .x20 8, .movz .x .x28 1 0,
   .adds .x .x21 .x21 .x25, .adcs .x .x22 .x22 .x27, .adc .x .x23 .x23 .x28]

/-- `t₀ + 2⁶⁴ t₁ + 2¹²⁸ t₂ = h r₀`. -/
def mulR0 : List Instr :=
  [.ldr .x .x24 .x0 r0Off,
   .mul .x .x25 .x21 .x24, .umulh .x27 .x21 .x24,
   .mul .x .x28 .x22 .x24, .umulh .x30 .x22 .x24,
   .adds .x .x27 .x27 .x28,
   .mul .x .x28 .x23 .x24, .adc .x .x28 .x28 .x30]

/-- `t += 2⁶⁴ h r₁`, into four words. -/
def mulR1 : List Instr :=
  [.ldr .x .x24 .x0 r1Off,
   .mul .x .x30 .x21 .x24, .umulh .x21 .x21 .x24,
   .adds .x .x27 .x27 .x30,
   .mul .x .x30 .x22 .x24, .umulh .x22 .x22 .x24,
   .adcs .x .x30 .x30 .x21,
   .mul .x .x23 .x23 .x24, .adc .x .x23 .x23 .x22,
   .adds .x .x28 .x28 .x30,
   .movz .x .x22 0 0, .adc .x .x30 .x23 .x22]

/-- `h = (t mod 2¹³⁰) + 5 ⌊t / 2¹³⁰⌋`, and the pointer advanced. -/
def reduce : List Instr :=
  [.movz .x .x21 3 0, .logic .and .x .x23 .x28 .x21, .sub .x .x21 .x28 .x23,
   .extr .x .x28 .x30 .x28 2,
   .adds .x .x21 .x21 .x25,
   .lsr .x .x25 .x30 2, .adc .x .x22 .x30 .x25,
   .adds .x .x21 .x21 .x28, .adcs .x .x22 .x22 .x27,
   .movz .x .x25 0 0, .adc .x .x23 .x23 .x25,
   .addImm .x .x20 .x20 16]

/-- One block absorbed. -/
def block : List Instr := addBlock ++ mulR0 ++ mulR1 ++ reduce

end VG.Impl.ChaCha20Poly1305.AArch64.Poly
