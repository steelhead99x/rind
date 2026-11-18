module

public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# The AArch64 target (AAPCS64)

**Trusted.** Functions are emitted as Rust `extern "C"` naked functions.

AAPCS64 (Arm's "Procedure Call Standard for the Arm 64-bit Architecture"):
integer/pointer arguments arrive in `x0`–`x7`; `x19`–`x28` and the frame
pointer `x29` are callee-saved, as is `sp`. The model excludes `x29`,
so every instruction preserves the inherited frame pointer, including during
execution (Apple's ABI requires a valid frame pointer at all times).
The printer ends every function with `ret`, which returns to the address
in the link register `x30`, so `x30`
must be unchanged on exit. `x18` is the platform register (reserved on Apple
platforms and Windows), which the model does not have (see `TCB/AArch64/Isa.lean`),
so no code can modify it.

The SIMD and floating-point registers `v0`–`v7` and `v16`–`v31` are
caller-saved (AAPCS64 §6.1.2), so `abiPreserved` says nothing about them.
The low 64 bits of `v8`–`v15` are callee-saved (AAPCS64 §6.1.2), and
`abiPreserved` explicitly requires those bits to be restored. The upper 64
bits need not be preserved. See
https://github.com/ARM-software/abi-aa/blob/2025Q4/aapcs64/aapcs64.rst
(section 6.1.2, SIMD and Floating-Point registers).

PSTATE.C is modelled but is not callee-saved: NZCV is undefined on entry
to and return from a public interface (AAPCS64 §6.1.1). N, Z and V are not
observable by modelled instructions. FPCR and FPSR are not modelled (no
modelled instruction reads or writes them), nor is memory below `sp`
(never granted to a function).
-/

@[expose] public section

namespace VG.AArch64

def preserved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28,
  .x30]

/-- AAPCS64 §6.1.2: preserve the low 64 bits of these SIMD registers. -/
def preservedV : List VReg := [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
    (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)

/-- AAPCS64 argument registers, in order. -/
def argRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7]

/-! ## The calling convention, for `Sig`

Each integer or pointer argument takes the next of `x0`–`x7`
(a 32-bit argument in the low half; the upper half is unspecified). Once
they are used up, each further argument takes the next 8 bytes of stack, in
order, the first at `sp` on entry. AAPCS64, "Parameter passing rules":
stage A sets the next stacked argument address (NSAA) to `sp`; in stage C,
an integral or pointer argument of at most 8 bytes goes in `x[NGRN]` while
the next general-purpose register number NGRN is less than 8; otherwise
NGRN is set to 8, the NSAA is rounded up to the larger of 8 and the
argument's natural alignment, an argument of less than 8 bytes is given a
size of 8 bytes, and the argument is copied to memory at the NSAA, which is
then incremented by its size. Uniform 64-bit arguments (pointers, `usize`,
`u64`) are modelled on the stack: Apple's arm64 ABI ("Writing ARM64 code for
Apple platforms") passes narrower stack arguments in slots of their natural
size instead, and for 8-byte arguments the two conventions agree. We also
accept 32-bit stack arguments each immediately followed by a 64-bit one
(`pairedNarrowStack`). AAPCS64 C.14/C.16/C.17 give each argument a slot of 8
bytes, so the `i`-th is at offset `8 * i`. Apple's ABI puts each argument at
the next offset of its natural alignment: one of 64 bits ends at a multiple
of 8, so a 32-bit argument after it (or first) starts at a multiple of 8,
`8 * i`, takes four bytes, and the 64-bit argument after it is aligned up to
the next multiple of 8, `8 * (i + 1)`; by induction, every argument is at
the same offset under both ABIs. A 32-bit slot's high half is unspecified
and must be ignored. The 64-bit argument after it ensures that reading the
whole slot stays within the caller's allocated argument area. Other narrow
stack layouts remain unsupported because the two ABIs may assign different
offsets.
Sources: https://github.com/ARM-software/abi-aa/blob/2025Q4/aapcs64/aapcs64.rst
and https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms
("Pass arguments to functions correctly"). `abi` only
grants reading the stack arguments, and assumes they do not wrap around the
end of the address space. The return address is in `x30`, not in memory;
the integer result is in `x0`.
-/

/-- The address of the `i`-th (from 0) stack argument, on entry. -/
def stackArgAddr (s : State) (i : Nat) : Addr := s.sp + BitVec.ofNat 64 (8 * i)

/-- The `i`-th (from 0) stack argument, on entry. -/
def stackArg (s : State) (i : Nat) : BitVec 64 := s.mem.readW (stackArgAddr s i) 64

/-- A stack layout on which AAPCS64 and Apple's natural-size slots agree:
arguments of 64 bits, and of 32 bits each immediately followed by one of 64. -/
def pairedNarrowStack : List Nat → Bool
  | [] => true
  | [w] => w = 64
  | w :: w' :: rest => if w = 64 then pairedNarrowStack (w' :: rest)
      else w = 32 && w' = 64 && pairedNarrowStack rest

def abi : Abi isa where
  ptrBits := 64
  args ws := if ws.length ≤ argRegs.length then
    some fun s => (argRegs.take ws.length).map s.gpr
  else if (ws.drop argRegs.length).all (· = 64) then
    some fun s => argRegs.map s.gpr ++ (List.range (ws.length - argRegs.length)).map (stackArg s)
  else if pairedNarrowStack (ws.drop argRegs.length) then
    some fun s => argRegs.map s.gpr ++ (List.range (ws.length - argRegs.length)).map (stackArg s)
  else none
  argArea ws s := let n := ws.length - argRegs.length
    if n = 0 then [] else [(⟨stackArgAddr s 0, 8 * n⟩, false)]
  reserved n s := stackBelow s.sp n
  -- The stack the function's calls and frames use, and its stack arguments,
  -- do not wrap around.
  wf ws n s := if ws.length ≤ argRegs.length then
      match n with
      | 0 => True
      | n => n ≤ s.sp.toNat
    else
      (match n with
      | 0 => True
      | n => n ≤ s.sp.toNat) ∧ s.sp.toNat + 8 * (ws.length - argRegs.length) ≤ 2 ^ 64
  pub s₁ s₂ := s₁.sp = s₂.sp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret s := s.gpr .x0
  sym := some fun s name => s.syms name
  mode s := if s.dit then 1 else 0

/-- Reducible, as an `abbrev` would be, but not inlined: an `abbrev` is compiled into
every module that names it, which then builds a target of its own, so the emitter
would see one per registration module rather than this one (`Rust.printsAs`). -/
@[reducible] def target : Target where
  name := "aarch64"
  isa := isa
  abiPreserved := abiPreserved
  abi := abi

end VG.AArch64
