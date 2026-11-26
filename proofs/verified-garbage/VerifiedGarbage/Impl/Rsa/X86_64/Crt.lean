module

public import VerifiedGarbage.Impl.Rsa.X86_64
public import VerifiedGarbage.Impl.Bignum.X86_64.Adx
public import VerifiedGarbage.Impl.Bignum.CrtLayout

/-!
# RSA with the CRT private key on x86-64

`vg_rsa_private_crt(out, out_len, n, n_len, input, input_len, p, p_len, q,
q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`: the
first six arguments in registers, the others on the stack.

The working space holds three workspaces, each a header and eight arrays as
`vg_rsa_public`'s (`Impl/Bignum/X86_64.lean`): one for `n` (`w` words), at
`scratch`, then one for `p` and one for `q` (`max(2, ⌈len / 8⌉)` words each),
each followed by room for 32 more arrays, the exponentiation's table.
The code runs in one at a time, its base in `rdi`; the headers of `p`'s and
`q`'s link back to `n`'s.

1. `n` is checked as `vg_rsa_public` checks it (it is public, so the code
   branches on it), and loaded with the input `c`, `-n⁻¹`, `R² mod n`, the
   number 1 and `c` in Montgomery form.
2. `p`, `q` and `qInv` are loaded, and the mask of `c < n`, `p q = n` and
   `qInv < p` computed; where it is clear, `p` and `q` are replaced by 3 and
   `qInv` by 0, so that what follows computes with valid values either way,
   and the result is masked at the end.
3. For `X = q`, then `X = p`: `c R_X mod X` (`R_X = 2^(64 w_X)`) without
   `R_X² mod X`, as `X` divides `n`: `G = 2^E mod n` for
   `E = 64 w_X (K + 1)` and `K = ⌈w / w_X⌉` (by one multiplication mod `n`
   when `2^(E - 64 w) < n`, and otherwise by squarings and doublings), then `x G mod n` reduced by `K` Montgomery steps mod `X`
   (`redc`): `x R_X mod X`.
4. `m_X = c^d_X mod X` by a fixed window of 4 bits, with a table of the 16
   powers after the prime's arrays, read by masked selections (`expLoop`); `h = (m_p - m_q) qInv mod p`
   and `m = m_q + q h`, written out masked.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.Crt

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

/-! ## Header slots and arrays

The layout of `Impl/Bignum/CrtLayout.lean`, the same on every target; `n`'s
workspace also keeps `vg_rsa_public`'s `sOut`, `sN`, `sK`, `sIn`, `sMask`
and `sCnt`. -/

export VG.Impl.Bignum.Crt (sP sPlen sQ sQlen sDp sDq sQinv sWsP sWsQ sD sLink sExp sExpLen sI sBit sV sRem sSrc
  sMaskX sTab sEnt sNib sJ aChunk aXc aT)

/-- `[b + 8 i]`, header slot `i` of the workspace at `b`. -/
def ws (b : Reg) (i : Nat) : MemOp := { base := b, disp := 8 * i }

/-- The stack argument `i` (from 1). -/
def stk (i : Nat) : MemOp := { base := .rsp, disp := 8 * i }

/-! ## Entry -/

/-- Save the callee-saved registers and the arguments in the header at
`scratch`, with its base in `rdi`. -/
def entry : List Instr :=
  ([.mov .r11 (.mem (stk 11))] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  ([.store (ws .r11 sOut) .rdi, .store (ws .r11 sN) .rdx, .store (ws .r11 sK) .rcx, .store (ws .r11 sIn) .r8,
    .mov .rax (.mem (stk 1)), .store (ws .r11 sP) .rax, .mov .rax (.mem (stk 2)), .store (ws .r11 sPlen) .rax,
    .mov .rax (.mem (stk 3)), .store (ws .r11 sQ) .rax, .mov .rax (.mem (stk 4)), .store (ws .r11 sQlen) .rax,
    .mov .rax (.mem (stk 5)), .store (ws .r11 sDp) .rax, .mov .rax (.mem (stk 7)), .store (ws .r11 sDq) .rax,
    .mov .rax (.mem (stk 9)), .store (ws .r11 sQinv) .rax, .mov .rdi (.reg .r11)] : List Instr)

/-! ## `n`'s workspace -/

/-- `n`, the input `c`, the mask of `c < n`, `-n⁻¹`, the number 1, `R² mod n`
(as `vg_rsa_public_precompute` computes it, `R2Words.choice`: by word steps
for the moduli whose top bit is set and whose length is a multiple of 4
words) and `c R mod n`. -/
def nSetup (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block head,
  loadBE,
  .block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
  loadBE,
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
    .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    cfToRbp],
  .block (([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
    ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr)),
  setWord aOne .rcx,
  R2Words.choice mul,
  mul aXm aX aR2]

/-! ### With the key's precomputed values

`vg_rsa_private_crt_precomputed` takes the key's precomputed values `pre`
(`vg_rsa_private_precompute`'s) after `vg_rsa_private_crt`'s arguments, as
its stack arguments 12 and 13 (`pre` and `pre_len`), and copies from them
what `vg_rsa_private_crt` computes from the key alone. Nothing moves the
stack pointer from where the call left it, so `pre` is read from the stack
(`[rsp + 104]`) where it is needed. -/

/-- `pre`, stack argument 12 (from 0). -/
def preArg : MemOp := stk 13

/-- `R² mod n` into `aR2` from `pre`, `w` in `r12`: its words `w` to
`2 w - 1`, after `n`'s `w` words (what `vg_rsa_public_precompute` writes). -/
def r2Pre : Prog isa :=
  .seq (.block (([.mov .rsi (.mem preArg)] : List Instr) ++ eightW ++
      ([.alu .add .rsi (.reg .rax), .mov .rbx (.mem (hdr (sArr aR2)))] : List Instr)))
    copyWords

/-- `nSetup`, with `R² mod n` from `pre` (`r2Pre`) rather than computed. -/
def nSetupP (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block head,
  loadBE,
  .block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
  loadBE,
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
    .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    cfToRbp],
  .block (([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
    ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr)),
  setWord aOne .rcx,
  r2Pre,
  mul aXm aX aR2]

/-! ## The prime workspaces -/

/-- `rax := ` the end of the arrays of the workspace at `rdx`: its last
array's base plus `8 (w + 2)`. -/
def wsEnd : List Instr :=
  [.mov .rax (.mem (ws .rdx (sArr aOne))), .mov .rdx (.mem (ws .rdx sW)), .alu .add .rdx (.imm 2),
    .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx)]

/-- `rax := ` the end of a prime's workspace at `rdx`: its arrays, then room
for the 32 entries of a window's table (`8 (w + 2)` bytes each). -/
def wsEndT : List Instr :=
  wsEnd ++ ([.alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx),
    .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx)] : List Instr)

/-- A workspace at `rax` (its base stored in slot `slotWs`) for a number of
the byte length in slot `slotLen`: `w = max(2, ⌈len / 8⌉)`, its arrays'
bases, and its link to `n`'s; `rdi` stays `n`'s. -/
def wsNew (slotWs slotLen : Nat) : List (Prog isa) := [
  .block [.store (hdr slotWs) .rax, .mov .r12 (.mem (hdr slotLen)), .alu .add .r12 (.imm 7), .shift .shr .r12 3,
    .alu .cmp .r12 (.imm 2)],
  .ite .b (.block [.mov32 .r12 (.imm 2)]) (.block []),
  .block (([.mov .rsi (.reg .rdi), .mov .rdi (.reg .rax), .store (hdr sLink) .rsi, .store (hdr sW) .r12] : List Instr) ++ setBases ++
    ([.mov .rdi (.reg .rsi)] : List Instr))]

/-- `[j] := 0` in the current workspace (`w + 2` words). -/
def zeroArr (j : Nat) : Prog isa :=
  .seq (.block [.mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))]) zeroAccLoop

/-- In a prime workspace: `[j] := ` the number of the bytes whose pointer and
length are in `n`'s header slots `slotPtr` and `slotLen`. -/
def loadArr (j slotPtr slotLen : Nat) : List (Prog isa) := [
  zeroArr j,
  .block [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax slotPtr)), .mov .rcx (.mem (ws .rax slotLen)),
    .mov .rbx (.mem (hdr (sArr j)))],
  loadBE]

/-- Into `p`'s and `q`'s workspaces, from `n`'s. -/
def enterP : Instr := .mov .rdi (.mem (hdr sWsP))
def enterQ : Instr := .mov .rdi (.mem (hdr sWsQ))
def leave : Instr := .mov .rdi (.mem (hdr sLink))

/-- The workspaces, `p`, `q` and `qInv` (into `p`'s chunk array). -/
def primesSetup : List (Prog isa) :=
  [.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ wsEnd)] ++ wsNew sWsP sPlen ++
  [.block (([.mov .rdx (.mem (hdr sWsP))] : List Instr) ++ wsEndT)] ++ wsNew sWsQ sQlen ++
  [.block [enterP]] ++ loadArr aN sP sPlen ++ loadArr aChunk sQinv sPlen ++ [.block [leave, enterQ]] ++
  loadArr aN sQ sQlen ++ [.block [leave]]

/-! ## The checks -/

/-- `acc := 0` over `2 w + 2` words from `n`'s accumulator. -/
def zeroAccs : List (Prog isa) :=
  [.block [.mov .r8 (.mem (hdr (sArr aAcc))), .mov .rbx (.mem (hdr sW))], Adx.zeroWin]

/-- `acc += [r11] [r9]`: rows `acc[r13 ..] += [r11]_{r13} [r9]` (`r12` words) for
`r13` from 0 to `r10 - 1`, `r8` the row's base. -/
def mulRows : Prog isa :=
  .seq (.block [.mov32 .r13 (.imm 0)])
    (.loop (.seq (.block [.mov .rcx (.mem (ix .r11 .r13))])
      (.seq mulAddRow (.block [.alu .add .r8 (.imm 8), .alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r10)]))) .ne)

/-- `p q` into `n`'s accumulators. -/
def pqProduct : List (Prog isa) := zeroAccs ++ [
  .block [.mov .rax (.mem (hdr sWsP)), .mov .r11 (.mem (ws .rax (sArr aN))), .mov .r10 (.mem (ws .rax sW)),
    .mov .rax (.mem (hdr sWsQ)), .mov .r9 (.mem (ws .rax (sArr aN))), .mov .r12 (.mem (ws .rax sW)),
    .mov .r8 (.mem (hdr (sArr aAcc)))],
  mulRows]

/-- The mask of `p q = n`, and'ed into `sMask`: the OR of the words of the
product's `XOR` with `n` over `w` words and of its words `w` to `2 w + 1`,
then all ones if it is zero. -/
def eqCheck : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aAcc))), .mov .r10 (.mem (hdr (sArr aN))),
    .mov32 .rbp (.imm 0)],
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (ix .r10 .r14)), .alu .or .rbp (.reg .rax)],
  .block [.mov .rax (.reg .r12), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rbx (.reg .rax), .alu .add .r12 (.imm 2)],
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)],
  .block [.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp), .alu .and .rbp (.mem (hdr sMask)),
    .store (hdr sMask) .rbp]]

/-- In `p`'s workspace: the mask of `qInv < p`, and'ed into `n`'s `sMask`. -/
def qinvCheck : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aChunk))), .mov .r10 (.mem (hdr (sArr aN))),
    .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
  .block [.mov .rax (.mem (hdr sLink)), .alu .and .rbp (.mem (ws .rax sMask)), .store (ws .rax sMask) .rbp]]

/-- `[j] &= sMaskX` over `w` words. -/
def maskArr (j : Nat) : List (Prog isa) := [
  .block [.mov .r15 (.mem (hdr sMaskX)), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr j)))],
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .and .rax (.reg .r15), .store (ix .rbx .r14) .rax]]

/-- In a prime workspace: the mask from `n`'s; `X := mask ? X : 3`; `-X⁻¹`;
the number 1. -/
def primeFix : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr sLink)), .mov .rax (.mem (ws .rax sMask)), .store (hdr sMaskX) .rax]] ++
  maskArr aN ++
  [.block (([.mov .rax (.reg .r15), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.imm 3),
      .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax, .mov .rbx (.reg .rax)] : List Instr) ++ minv ++
      ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr)),
    setWord aOne .rcx]

/-- The checks and the fixes. -/
def checks : List (Prog isa) :=
  pqProduct ++ eqCheck ++ [.block [enterP]] ++ qinvCheck ++ primeFix ++ [.block [leave, enterQ]] ++ primeFix ++
  [.block [leave]]

/-- The checks but `p q = n`'s, for a key whose `p q = n` is known (as
`privatePrecompute` gave values for it): the mask is then the same. -/
def checksP : List (Prog isa) :=
  [.block [enterP]] ++ qinvCheck ++ primeFix ++ [.block [leave, enterQ]] ++ primeFix ++ [.block [leave]]

/-! ## Arithmetic modulo a prime -/

/-- `[o] = [a] + [b] mod m` for `[a], [b] < m`: the sum into the
accumulator (`w + 1` words), then the subtraction of `m` selected as in
`montMul`. -/
def addMod (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .rbx (.mem (hdr (sArr a))), .mov .r9 (.mem (hdr (sArr b))), .mov .r10 (.mem (hdr (sArr aN))),
      .mov .r8 (.mem (hdr (sArr aAcc))), .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aTmp))),
      .mov32 .rbp (.imm 0)])
    (.seq (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.mem (ix .r9 .r14)),
      .store (ix .r8 .r14) .rax, cfToRbp])
    (.seq (.block [.mov32 .rax (.imm 0), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax,
      .mov .rbx (.mem (hdr (sArr o)))])
    (.seq subMod selectAcc)))

/-- `[o] = [a] - [b] mod m` for `[a], [b] < m`: the difference into the
accumulator (as `subMod`'s loop), then `m` added under the mask of its
borrow. -/
def subModArr (o a b : Nat) : List (Prog isa) := [
  .block [.mov .r8 (.mem (hdr (sArr a))), .mov .r10 (.mem (hdr (sArr b))), .mov .rsi (.mem (hdr (sArr aAcc))),
    .mov .r12 (.mem (hdr sW)), .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    .store (ix .rsi .r14) .rax, cfToRbp],
  .block [.mov .r15 (.reg .rbp), .mov32 .rbp (.imm 0), .mov .r10 (.mem (hdr (sArr aN))),
    .mov .r8 (.mem (hdr (sArr aAcc))), .mov .rbx (.mem (hdr (sArr o)))],
  wordLoop 0 [.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r15), cfFromRbp,
    .alu .adc .rax (.mem (ix .r8 .r14)), .store (ix .rbx .r14) .rax, cfToRbp]]

/-- `[o] := [a]` over `w` words. -/
def copyArr (o a : Nat) : List (Prog isa) :=
  [.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr a))), .mov .rbx (.mem (hdr (sArr o)))], copyWords]

/-- In a prime workspace: `[aXc] := x R_X^(-K) mod X` for the `w_n` words at
`n`'s array `j` (`x = Σ x_k R_X^k`, chunks of `w_X` words): `acc := 0`;
for each chunk, `acc := acc R_X⁻¹ + x_k R_X⁻¹ mod X`. -/
def redc (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : List (Prog isa) := [
  zeroArr aXc,
  .block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax (sArr j))), .store (hdr sSrc) .rdx,
    .mov .rdx (.mem (ws .rax sW)), .store (hdr sRem) .rdx],
  .loop (seqs [
    zeroArr aChunk,
    .block [.mov .r12 (.mem (hdr sRem)), .alu .cmp .r12 (.mem (hdr sW))],
    .ite .b (.block []) (.block [.mov .r12 (.mem (hdr sW))]),
    .block [.mov .rsi (.mem (hdr sSrc)), .mov .rbx (.mem (hdr (sArr aChunk)))],
    copyWords,
    .block [.mov .rax (.mem (hdr sRem)), .alu .sub .rax (.reg .r12), .store (hdr sRem) .rax,
      .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12),
      .alu .add .r12 (.mem (hdr sSrc)), .store (hdr sSrc) .r12],
    mul aXc aXc aOne,
    mul aT aChunk aOne,
    addMod aXc aXc aT,
    .block [.mov .rax (.mem (hdr sRem)), .alu .test .rax (.reg .rax)]]) .ne]

/-- `G` the long way, `D` in slot `sD`: its top bit into `sCnt`, `Y = R mod n`,
and for each bit of `D` from the top, `Y := Y² R⁻¹`, doubled if the bit is
set: `Y = 2^D R`. -/
def gSlow (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block [.mov .rax (.mem (hdr sD))],
  topBit,
  .block [.store (hdr sCnt) .rdx],
  mul aY aR2 aOne,
  .loop (seqs [
    mul aY aY aY,
    .block [.mov .rax (.mem (hdr sD)), .alu .and .rax (.mem (hdr sCnt))],
    .ite .ne (double aN aAcc aTmp aY) (.block []),
    .block [.mov .rax (.mem (hdr sCnt)), .shift .shr .rax 1, .store (hdr sCnt) .rax, .alu .test .rax (.reg .rax)]]) .ne]

/-- `G` in one multiplication, `D = 64 c` with `c` in `rcx` and `w` in `r12`:
`Y := 2^D`, then `Y := R² Y R⁻¹ = 2^D R`. -/
def gFast (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs [.block [.mov32 .rdx (.imm 1)], setWord aY .rcx, mul aY aR2 aY]

/-- In `n`'s workspace: `[aY] := G = 2^E mod n` for `E = 64 w_X (K + 1)`,
`K = ⌈w / w_X⌉`, the prime workspace's base in slot `slotWs`: `D = E - 64 w`
(a multiple of 64), then `Y = 2^D R`: by `gFast` when `2^D < n`, which
holds when `n`'s top word is not 0 and `D < 64 (w - 1)` (as it is for
primes of half `n`'s length), and by `gSlow` otherwise. -/
def gPow (mul : Nat → Nat → Nat → Prog isa) (slotWs : Nat) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr slotWs)), .mov .rax (.mem (ws .rax sW)), .mov .r12 (.mem (hdr sW)),
    .mov32 .rcx (.imm 0)],
  .loop (.block [.alu .add .rcx (.reg .rax), .alu .cmp .rcx (.reg .r12)]) .b,
  .block [.alu .add .rcx (.reg .rax), .alu .sub .rcx (.reg .r12), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .store (hdr sD) .rcx, .mov .rax (.reg .rcx)],
  .block [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))],
  .block [.mov .rax (.mem (ix .r10 .r12 (-8))), .alu .test .rax (.reg .rax)],
  .ite .ne
    (.seq (.block [.mov .rcx (.mem (hdr sD)), .shift .shr .rcx 6, .mov .rdx (.reg .r12), .alu .sub .rdx (.imm 1),
        .alu .cmp .rcx (.reg .rdx)])
      (.ite .b (gFast mul) (gSlow mul)))
    (gSlow mul)]

/-! ## The exponentiation

By a fixed window of 4 bits: `Y := Y¹⁶ T_v` for each 4 bits `v` of the
exponent, from its top, with the table `T_i = x^i` in Montgomery form
(`T_0 = Y`, which is 1 in Montgomery form). The entry is read by a masked
selection from every entry, so the addresses do not depend on `v`. -/

/-- `rax := [sEnt] + 8 (w + 2)`, into `sEnt`: the next entry. -/
def nextEnt : Prog isa :=
  .block [.mov .rax (.mem (hdr sEnt)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx),
    .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx), .store (hdr sEnt) .rax]

/-- `[sEnt] := [a]` over `w` words. -/
def toEnt (a : Nat) : List (Prog isa) :=
  [.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr a))), .mov .rbx (.mem (hdr sEnt))], copyWords]

/-- A table of `c + 2` entries, after the workspace's last array:
`T_0 := Y`, `T_1 := [aXc]`, and `T_i := T_(i-1) [aXc] R⁻¹` (in `aT`) for `i`
from 2 to `c + 1`. -/
def tabBuildN (mul : Nat → Nat → Nat → Prog isa) (c : Nat) : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr (sArr aOne))), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2),
    .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx),
    .store (hdr sTab) .rax, .store (hdr sEnt) .rax]] ++
  toEnt aY ++ [nextEnt] ++ toEnt aXc ++ copyArr aT aXc ++
  [.block [.mov32 .rax (.imm (BitVec.ofNat 32 c)), .store (hdr sBit) .rax],
    .loop (seqs ([mul aT aT aXc, nextEnt] ++ toEnt aT ++
      [.block [.mov .rax (.mem (hdr sBit)), .alu .sub .rax (.imm 1), .store (hdr sBit) .rax]])) .ne]

/-- The table of the 16 powers. -/
def tabBuild (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := tabBuildN mul 14

/-- `x := mask (r15 + j = src)` in both quadwords, by `r14`. -/
def selMask (j : BitVec 32) (src : Src) (x : XReg) : List Instr :=
  [.mov .r14 (.reg .r15), .alu .add .r14 (.imm j), .alu .xor .r14 src, .alu .cmp .r14 (.imm 1),
    .alu .sbb .r14 (.reg .r14), .xop (.movq x .r14), .xop (.bin .punpcklqdq x x)]

/-- A pass's registers: `r15 = 8 p` (from `sJ`), `rcx` its first entry (from
`sEnt`), `r11` an entry's size `8 (w + 2)`, `r13 = 2 ⌈w / 2⌉` and `rbx = aT`. -/
def gatherRegs : List Instr :=
  [.mov .r15 (.mem (hdr sJ)), .mov .rcx (.mem (hdr sEnt)), .mov .r12 (.mem (hdr sW)), .mov .r11 (.reg .r12),
    .alu .add .r11 (.imm 2), .alu .add .r11 (.reg .r11), .alu .add .r11 (.reg .r11), .alu .add .r11 (.reg .r11),
    .mov .r13 (.reg .r12), .alu .add .r13 (.imm 1), .shift .shr .r13 1, .alu .add .r13 (.reg .r13),
    .mov .rbx (.mem (hdr (sArr aT)))]

/-- The pass's eight entries, from `rcx`, in `rcx`, `rdx`, `rsi`, `rbp`, `r8`,
`r9`, `r10` and `rax`, and `r14 = 0`. -/
def gatherBases : List Instr :=
  [.mov .rdx (.reg .rcx), .alu .add .rdx (.reg .r11), .mov .rsi (.reg .rdx), .alu .add .rsi (.reg .r11),
    .mov .rbp (.reg .rsi), .alu .add .rbp (.reg .r11), .mov .r8 (.reg .rbp), .alu .add .r8 (.reg .r11),
    .mov .r9 (.reg .r8), .alu .add .r9 (.reg .r11), .mov .r10 (.reg .r9), .alu .add .r10 (.reg .r11),
    .mov .rax (.reg .r10), .alu .add .rax (.reg .r11), .mov32 .r14 (.imm 0)]

/-- `xmm0 |= [b + 8 r14] & x`, a pair of words. -/
def gatherOr (b : Reg) (x : XReg) : List Instr :=
  [.movdquLoad .xmm1 (ix b .r14), .xop (.bin .pand .xmm1 x), .xop (.bin .por .xmm0 .xmm1)]

/-- `xmm0 := [rcx + 8 r14] & xmm8`. -/
def gatherFirst : List Instr :=
  [.movdquLoad .xmm0 (ix .rcx .r14), .xop (.bin .pand .xmm0 .xmm8)]

/-- The pair into `[rbx + 8 r14]`, and the next. -/
def gatherStore : List Instr :=
  [.movdquStore (ix .rbx .r14) .xmm0, .alu .add .r14 (.imm 2), .alu .cmp .r14 (.reg .r13)]

/-- `sEnt` past the pass's entries, `sJ := 8 (p + 1)`, `ZF` after the second. -/
def gatherEnd : List Instr :=
  [.alu .add .rax (.reg .r11), .store (hdr sEnt) .rax, .mov .rax (.reg .r15), .alu .add .rax (.imm 8),
    .store (hdr sJ) .rax, .alu .cmp .rax (.imm 16)]

/-- A pass's registers, masks and bases. -/
def gatherHead : List (Prog isa) :=
  [.block gatherRegs,
    .block (selMask 0 (.mem (hdr sNib)) .xmm8), .block (selMask 1 (.mem (hdr sNib)) .xmm9),
    .block (selMask 2 (.mem (hdr sNib)) .xmm10), .block (selMask 3 (.mem (hdr sNib)) .xmm11),
    .block (selMask 4 (.mem (hdr sNib)) .xmm12), .block (selMask 5 (.mem (hdr sNib)) .xmm13),
    .block (selMask 6 (.mem (hdr sNib)) .xmm14), .block (selMask 7 (.mem (hdr sNib)) .xmm15),
    .block (selMask 0 (.imm 8) .xmm7),
    .block gatherBases]

/-- A pair of words of `[aT]`: `([aT] & xmm7) | OR_j ([b_j] & xmm(8+j))`. -/
def gatherBody : List (Prog isa) :=
  [.block gatherFirst, .block (gatherOr .rdx .xmm9), .block (gatherOr .rsi .xmm10),
    .block (gatherOr .rbp .xmm11), .block (gatherOr .r8 .xmm12), .block (gatherOr .r9 .xmm13),
    .block (gatherOr .r10 .xmm14), .block (gatherOr .rax .xmm15), .block (gatherOr .rbx .xmm7),
    .block gatherStore]

/-- Pass `p` of the selection, over entries `8 p` to `8 p + 7`: with the mask
of `8 p + j = v` in `xmm(8 + j)` and the mask of `p = 1` in `xmm7`, each pair
of words of `[aT]` becomes `([aT] & xmm7) | OR_j (T_(8p+j) & xmm(8+j))`, two
words at a time, from eight bases in registers: `T_v` after both passes. -/
def gatherPass : List (Prog isa) :=
  [seqs gatherHead, .loop (seqs gatherBody) .ne, .block gatherEnd]

/-- `[aT] := T_v`, `v` in `sNib`: two passes of `gatherPass`. -/
def tabSelect : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr sTab)), .store (hdr sEnt) .rax, .mov32 .rax (.imm 0), .store (hdr sJ) .rax],
    .loop (seqs gatherPass) .ne]

/-! ### The selection with AVX2

`gatherPass`'s passes with AVX2: each pass's masks broadcast to whole `ymm`
registers, four words at a time (`vpand` from memory, `vpor`), then the
last two words with the `xmm` halves if `2 ⌈w / 2⌉` is not a multiple of 4;
`vzeroupper` at the end, before the next legacy SSE instruction. -/

/-- `x := mask (r15 + j = src)` in every quadword of `ymm`, by `r14`. -/
def selMaskV (j : BitVec 32) (src : Src) (x : XReg) : List Instr :=
  [.mov .r14 (.reg .r15), .alu .add .r14 (.imm j), .alu .xor .r14 src, .alu .cmp .r14 (.imm 1),
    .alu .sbb .r14 (.reg .r14), .vop (.vmovq x .r14), .vop (.vpbroadcastq .l256 x x)]

/-- `ymm7 := ` the mask of `p ≠ 0` (`r15 = 8 p`), by `r14`. -/
def keepMaskV : List Instr :=
  [.mov32 .r14 (.imm 0), .alu .cmp .r14 (.reg .r15), .alu .sbb .r14 (.reg .r14), .vop (.vmovq .xmm7 .r14),
    .vop (.vpbroadcastq .l256 .xmm7 .xmm7)]

/-- `gatherRegs`, and `r12 := 4 ⌊r13 / 4⌋`. -/
def gatherRegsV : List Instr :=
  gatherRegs ++ ([.mov .r12 (.reg .r13), .shift .shr .r12 2, .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12)] :
    List Instr)

/-- A pass's registers, masks and bases. -/
def gatherHeadV : List (Prog isa) :=
  [.block gatherRegsV,
    .block (selMaskV 0 (.mem (hdr sNib)) .xmm8), .block (selMaskV 1 (.mem (hdr sNib)) .xmm9),
    .block (selMaskV 2 (.mem (hdr sNib)) .xmm10), .block (selMaskV 3 (.mem (hdr sNib)) .xmm11),
    .block (selMaskV 4 (.mem (hdr sNib)) .xmm12), .block (selMaskV 5 (.mem (hdr sNib)) .xmm13),
    .block (selMaskV 6 (.mem (hdr sNib)) .xmm14), .block (selMaskV 7 (.mem (hdr sNib)) .xmm15),
    .block keepMaskV,
    .block gatherBases]

/-- `xmm0 |= [b + 8 r14] & x`, over the register's length `L`. -/
def gatherOrV (L : VLen) (b : Reg) (x : XReg) : List Instr :=
  [.vbinLoad .vpand L .xmm1 x (ix b .r14), .vop (.vbin .vpor L .xmm0 .xmm0 .xmm1)]

/-- The words of `[aT]` at `r14`, four (`.l256`) or two (`.l128`):
`([aT] & ymm7) | OR_j ([b_j] & ymm(8+j))`; `r14 += n`. -/
def gatherBodyV (L : VLen) (n : Nat) : List Instr :=
  [.vbinLoad .vpand L .xmm0 .xmm8 (ix .rcx .r14)] ++
  gatherOrV L .rdx .xmm9 ++ gatherOrV L .rsi .xmm10 ++ gatherOrV L .rbp .xmm11 ++ gatherOrV L .r8 .xmm12 ++
  gatherOrV L .r9 .xmm13 ++ gatherOrV L .r10 .xmm14 ++ gatherOrV L .rax .xmm15 ++ gatherOrV L .rbx .xmm7 ++
  ([.vmovdquStore L (ix .rbx .r14) .xmm0, .alu .add .r14 (.imm (BitVec.ofNat 32 n))] : List Instr)

/-- `sEnt` past the pass's entries, `sJ := 8 (p + 1)`, `ZF` after the fourth. -/
def gatherEndV : List Instr :=
  [.alu .add .rax (.reg .r11), .store (hdr sEnt) .rax, .mov .rax (.reg .r15), .alu .add .rax (.imm 8),
    .store (hdr sJ) .rax, .alu .cmp .rax (.imm 32)]

/-- Pass `p` of the selection with AVX2: the words of `[aT]` four at a time
below `r12`, then two more if `r12 < r13`. -/
def gatherPassV : List (Prog isa) :=
  [seqs gatherHeadV,
    .block [.alu .test .r12 (.reg .r12)],
    .ite .ne (.loop (.block (gatherBodyV .l256 4 ++ ([.alu .cmp .r14 (.reg .r12)] : List Instr))) .ne) (.block []),
    .block [.alu .cmp .r14 (.reg .r13)],
    .ite .ne (.block (gatherBodyV .l128 2)) (.block []),
    .block gatherEndV]

/-- `[aT] := T_v` for a table of 32 entries, `v` in `sNib`: four passes of
`gatherPassV`, then `vzeroupper`. -/
def tabSelectV : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr sTab)), .store (hdr sEnt) .rax, .mov32 .rax (.imm 0), .store (hdr sJ) .rax],
    .loop (seqs gatherPassV) .ne, .block [.vop .vzeroupper]]

/-- One window: `Y := Y¹⁶ T_v R⁻¹` for `v` the top 4 bits of the byte in
`sV`, which moves up 4 bits, by four squarings `sq` and a multiplication by
the table. -/
def expWin (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sel : List (Prog isa)) : List (Prog isa) :=
  [sq, sq, sq, sq,
    .block [.mov .rdx (.mem (hdr sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .store (hdr sV) .rax, .shift .shr .rdx 4,
      .alu .and .rdx (.imm 15), .store (hdr sNib) .rdx]] ++
  sel ++
  [mul aY aY aT,
    .block [.mov .rax (.mem (hdr sBit)), .alu .sub .rax (.imm 1), .store (hdr sBit) .rax]]

/-- `Y := Y^d` (`Y` 1 and `[aXc]` in Montgomery form) for the exponent whose
pointer and length are in `n`'s header slots `slotPtr` and `slotLen`, its
bytes most significant first, two windows a byte, its squarings by `sq`. -/
def expLoopS (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sel : List (Prog isa)) (slotPtr slotLen : Nat) :
    List (Prog isa) := [
  .block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax slotPtr)), .store (hdr sExp) .rdx,
    .mov .rdx (.mem (ws .rax slotLen)), .store (hdr sExpLen) .rdx, .mov32 .rdx (.imm 0), .store (hdr sI) .rdx]] ++
  tabBuild mul ++ [
  .loop (seqs [
    .block [.mov .rax (.mem (hdr sExp)), .mov .rcx (.mem (hdr sI)), .movzx8 .rax { base := .rax, index := some .rcx },
      .store (hdr sV) .rax, .mov32 .rax (.imm 2), .store (hdr sBit) .rax],
    .loop (seqs (expWin sq mul sel)) .ne,
    .block [.mov .rax (.mem (hdr sI)), .alu .add .rax (.imm 1), .store (hdr sI) .rax,
      .alu .cmp .rax (.mem (hdr sExpLen))]]) .ne]

/-- `expLoopS` with the squarings by `mul`. -/
def expLoop (mul : Nat → Nat → Nat → Prog isa) (sel : List (Prog isa)) (slotPtr slotLen : Nat) :
    List (Prog isa) := expLoopS (mul aY aY aY) mul sel slotPtr slotLen

/-! ### The exponentiation by windows of 5 bits

`expLoop5S`: `Y := Y³² T_v` for each 5 bits `v` of the exponent, from its
top, after `2 len mod 5` zero bits that make its `8 len` bits a whole
number of windows, with the table of the 32 powers. The exponent's bits not
yet in a window are kept at the top of `sV`, `b` of them (in `sBit`), and a
byte more is put below them when fewer than 5 are left, by a multiplication
by `2^(56 - b)` (in `sPow`): the shifts' amounts are the instructions'. -/

/-- In a prime's header: `2^(56 - b)`, `b` the bits left in `sV`. -/
def sPow : Nat := sFn 13

/-- `sBit := b = 2 len mod 5` for the exponent's length `len` (in
`sExpLen`), the zero bits put before its `8 len` bits, with `sV := 0` and
`sPow := 2^(56 - b)`: `⌊len / 5⌋ = ⌊len M / 2^66⌋` for `M = ⌈2^66 / 5⌉`,
then `2 (len mod 5)` less 5 if that does not borrow, and `2^56` halved once
for each of 1 to 4 that is at most `b`. -/
def padInit : List Instr :=
  [.mov .rcx (.mem (hdr sExpLen)), .movImm64 .rax 0xCCCCCCCCCCCCCCCD, .mul .rcx, .shift .shr .rdx 2,
    .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rdx),
    .alu .sub .rcx (.reg .rax), .alu .add .rcx (.reg .rcx), .mov .rax (.reg .rcx), .alu .sub .rax (.imm 5),
    .cmov .b .rax (.reg .rcx), .store (hdr sBit) .rax, .mov32 .rcx (.imm 0), .store (hdr sV) .rcx,
    .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 56)),
    .mov .rdx (.reg .rcx), .shift .shr .rdx 1, .alu .cmp .rax (.imm 1), .cmov .ae .rcx (.reg .rdx),
    .mov .rdx (.reg .rcx), .shift .shr .rdx 1, .alu .cmp .rax (.imm 2), .cmov .ae .rcx (.reg .rdx),
    .mov .rdx (.reg .rcx), .shift .shr .rdx 1, .alu .cmp .rax (.imm 3), .cmov .ae .rcx (.reg .rdx),
    .mov .rdx (.reg .rcx), .shift .shr .rdx 1, .alu .cmp .rax (.imm 4), .cmov .ae .rcx (.reg .rdx),
    .store (hdr sPow) .rcx]

/-- The next byte of the exponent (at `sI`, which moves up) below the `b`
bits in `sV`: `sV |= byte 2^(56 - b)`, `b += 8`, and `sPow` divided by
`2^8`. -/
def refill : List Instr :=
  [.mov .rax (.mem (hdr sExp)), .mov .rcx (.mem (hdr sI)), .mov .rdx (.mem (hdr sPow)), .mov .r8 (.mem (hdr sBit)),
    .movzx8 .rax { base := .rax, index := some .rcx }, .imul .rax .rdx, .alu .or .rax (.mem (hdr sV)),
    .store (hdr sV) .rax, .alu .add .rcx (.imm 1), .store (hdr sI) .rcx, .shift .shr .rdx 8, .store (hdr sPow) .rdx,
    .alu .add .r8 (.imm 8), .store (hdr sBit) .r8]

/-- The window: `sNib := ` the top 5 bits of `sV`, which moves up 5 bits,
`b -= 5`, and `sPow` multiplied by `2^5`. -/
def takeWin : List Instr :=
  [.mov .rax (.mem (hdr sV)), .mov .rdx (.mem (hdr sPow)), .mov .rcx (.mem (hdr sBit)), .shift .shl .rdx 5,
    .store (hdr sPow) .rdx, .alu .sub .rcx (.imm 5), .store (hdr sBit) .rcx, .mov .rdx (.reg .rax),
    .shift .shr .rdx 59, .store (hdr sNib) .rdx, .shift .shl .rax 5, .store (hdr sV) .rax]

/-- One window: a byte more into `sV` if fewer than 5 bits are left there,
then `Y := Y³² T_v R⁻¹` for `v` its top 5 bits, read by `sel`; `ZF` once no
byte nor bit is left. -/
def expWin5 (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sel : List (Prog isa)) : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr sBit)), .alu .cmp .rax (.imm 5)],
    .ite .b (.block refill) (.block []),
    sq, sq, sq, sq, sq,
    .block takeWin] ++
  sel ++
  [mul aY aY aT,
    .block [.mov .rax (.mem (hdr sExpLen)), .alu .sub .rax (.mem (hdr sI)), .alu .add .rax (.mem (hdr sBit))]]

/-- `expLoopS` by windows of 5 bits, the table's 32 entries read by `sel`. -/
def expLoop5S (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sel : List (Prog isa)) (slotPtr slotLen : Nat) :
    List (Prog isa) := [
  .block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax slotPtr)), .store (hdr sExp) .rdx,
    .mov .rdx (.mem (ws .rax slotLen)), .store (hdr sExpLen) .rdx, .mov32 .rdx (.imm 0), .store (hdr sI) .rdx]] ++
  tabBuildN mul 30 ++ [.block padInit, .loop (seqs (expWin5 sq mul sel)) .ne]

/-! ## The primes -/

/-- `q`: `m_q = c^dQ mod q` into `q`'s `aY`, by the exponentiation `ex`
(`expLoop mul sel` or `expLoop5S sq mul sel`). -/
def qPhase (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : List (Prog isa) :=
  gPow mul sWsQ ++ [.block [enterQ]] ++ redc mul aY ++ copyArr aY aXc ++ [.block [leave], mul aY aXm aY,
    .block [enterQ]] ++ redc mul aY ++ ex sDq sQlen ++ [mul aY aY aOne, .block [leave]]

/-- `p`: `m_p R_p` into `p`'s `aY`, `m_q R_p` into its `aXc`, their
difference into `aT`, `qInv` again (masked) into its chunk array, and
`h = (m_p - m_q) qInv mod p` into its `aY`. -/
def pPhase (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : List (Prog isa) :=
  gPow mul sWsP ++ [.block [enterP]] ++ redc mul aY ++ copyArr aY aXc ++ [.block [leave], zeroArr aX,
    .block [.mov .rax (.mem (hdr sWsQ)), .mov .rsi (.mem (ws .rax (sArr aY))), .mov .r12 (.mem (ws .rax sW)),
      .mov .rbx (.mem (hdr (sArr aX)))],
    copyWords, mul aX aX aR2, mul aX aX aY, mul aY aXm aY, .block [enterP]] ++
  redc mul aY ++ ex sDp sPlen ++ [.block [leave]] ++ [.block [enterP]] ++ redc mul aX ++
  subModArr aT aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++ [mul aY aT aChunk, .block [leave]]

/-! ## The result -/

/-- `m = m_q + q h` into `n`'s accumulators, written out masked, and the
mask's low bit returned. -/
def finish : List (Prog isa) := zeroAccs ++ [
  .block [.mov .rax (.mem (hdr sWsQ)), .mov .rsi (.mem (ws .rax (sArr aY))), .mov .r12 (.mem (ws .rax sW)),
    .mov .rbx (.mem (hdr (sArr aAcc)))],
  copyWords,
  .block [.mov .rax (.mem (hdr sWsP)), .mov .r11 (.mem (ws .rax (sArr aY))), .mov .r10 (.mem (ws .rax sW)),
    .mov .rax (.mem (hdr sWsQ)), .mov .r9 (.mem (ws .rax (sArr aN))), .mov .r12 (.mem (ws .rax sW)),
    .mov .r8 (.mem (hdr (sArr aAcc)))],
  mulRows,
  .block [.mov .rbx (.mem (hdr (sArr aAcc))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  storeBE,
  .block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)]

/-- `main` with `R² mod n` from `pre` (`nSetupP`), and without the check of
`p q = n`, which `pre` implies (`checksP`). -/
def mainP (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  seqs (nSetupP mul ++ primesSetup ++ checksP ++ qPhase mul ex ++ pPhase mul ex ++ finish)

/-- `vg_rsa_private_crt_precomputed`: `code`, with `R² mod n` from the key's
precomputed values `pre` (`mainP`). -/
def codeP (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) : Prog isa :=
  .seq (.block (entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid))
    (.ite .ne fail (mainP mul ex))

end VG.Impl.Rsa.X86_64.Crt
