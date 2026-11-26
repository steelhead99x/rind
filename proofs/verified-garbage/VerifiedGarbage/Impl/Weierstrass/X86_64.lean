module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Mont
public import VerifiedGarbage.Impl.Weierstrass.Rcb0

/-!
# Short Weierstrass curves on x86-64: points, scalar multiplication, powers

Code for any curve `y² = x³ + ax + b` over a prime field of `n` 64-bit
words, with the Montgomery arithmetic of `Impl/Mont/X86_64.lean`. Field
elements are in Montgomery form (`x R mod p`, `R = 2^(64 n)`) in slots of
the working space; a point is three slots, projective coordinates
`(X : Y : Z)`.

* `fprog`: field operations on slots (`FOp`, `Impl/Weierstrass/Slots.lean`),
  such as the complete addition `rcb`, one after the other.
* `ladder`: `[k]G` by double-and-add from the top bit, 256 times (or as many
  bits as the table has): `D = R + R`, `S = D + G` and `R = D` or `S` by a
  mask of the bit, so every iteration does the same. For a curve with
  `a = 0` and an affine `G` (`a0`), the doubling and the addition are those
  for `a = 0` (`dbl0`, `rcb0m`: 22 products, against 34).
* `pow`: `x^e` by square-and-multiply over the bits of a public exponent,
  also always multiplying and selecting by a mask, so that one loop serves
  every exponent.
* `bits`: the bits of a little-endian number in a slot, one byte each.

The only branches are on loop counters, and every address is `rdi` plus a
constant, or plus a counter: nothing but `rdi` may affect timing.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont

/-- The code of a field operation. -/
def opCode (M : Mod) : FOp → List Instr
  | .mul o a b => Mont.X86_64.mul M o a b
  | .add o a b => Mont.X86_64.add M o a b
  | .sub o a b => Mont.X86_64.sub M o a b

/-- A straight-line sequence of field operations. -/
def fprog (M : Mod) (ops : List FOp) : List Instr := ops.flatMap (opCode M)

/-- Straight-line code as a sequence of blocks (the same instructions as their
concatenation; the kernel handles many short blocks better than one long one). -/
def blocks : List (List Instr) → Prog isa
  | [] => .block []
  | [b] => .block b
  | b :: bs => .seq (.block b) (blocks bs)

/-- A product by a call of a function (`Mont.callOf`), for operands it can
take, else none. -/
def opCall? (M : Mod) : FOp → Option (Prog isa)
  | .mul o a b => match Mont.callOf M with
    | some (f, body) => if Mont.lowArgs M.n o a b then some (Mont.mulCall f body o a b) else none
    | none => none
  | _ => none

/-- A field operation: a call (`opCall?`), else its code as a block. -/
def opProg (M : Mod) (op : FOp) : Prog isa := (opCall? M op).getD (.block (opCode M op))

/-- Programs one after the other. -/
def progs : List (Prog isa) → Prog isa
  | [] => .block []
  | [p] => p
  | p :: ps => .seq p (progs ps)

/-- `fprog`, an operation at a time, its products calls where they can be
(`opProg`); without calls, a block per operation. -/
def fprogB (M : Mod) (ops : List FOp) : Prog isa := progs (ops.map (opProg M))

/-- `fprogB` with the block `side i` after operation `i` (from `i`): code that
the operations' wait on each other's results leaves time for. -/
def fprogBI (M : Mod) : List FOp → (Nat → List Instr) → Nat → Prog isa
  | [], _, _ => .block []
  | op :: ops, side, i => .seq (opProg M op) (.seq (.block (side i)) (fprogBI M ops side (i + 1)))

/-- `[o] = [a]` if the mask `rcx` is zero, `[b]` if it is all ones, `n`
words, through `rax` and `rdx`. -/
def sel : Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, o, a, b => [.mov .rax (.mem (sc a)), .mov .rdx (.mem (sc b)), .alu .xor .rdx (.reg .rax),
      .alu .and .rdx (.reg .rcx), .alu .xor .rax (.reg .rdx), .store (sc o) .rax] ++
      sel k (o + 8) (a + 8) (b + 8)

/-- `o = a` or `b`, a point, by the mask `rcx`. -/
def selPt (n : Nat) (o a b : Pt) : List Instr :=
  sel n o.x a.x b.x ++ sel n o.y a.y b.y ++ sel n o.z a.z b.z

/-- `[o] = [a]`, `n` words, through `rax`. -/
def copy : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, o, a => [.mov .rax (.mem (sc a)), .store (sc o) .rax] ++ copy k (o + 8) (a + 8)

/-- `[rdi + rbx + d]`: byte `rbx` of a table at `d`. -/
def tbl (d : Nat) : MemOp := { base := .rdi, index := some .rbx, disp := d }

/-- The mask `rcx = -[rdi + rbx + d]` of the bit of iteration `rbx`. -/
def bitMask (d : Nat) : List Instr :=
  [.movzx8 .rax (tbl d), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax)]

/-- One iteration of the ladder, for the bit `t = rbx - 1`: `D = R + R`,
`T = D + G`, then `R = T` if bit `t` is set, else `D`. -/
def ladderBody (L : LadderCfg) (a0 : Bool := false) : Prog isa :=
  .seq (.block [.alu .sub .rbx (.imm 1)]) <| .seq (fprogB L.M (ladDblOps L a0)) <|
    .seq (fprogB L.M (ladAddOps L a0)) <|
    .block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T ++ [.alu .test .rbx (.reg .rbx)])

/-- The ladder over the bits `nbits - 1` down to 0, from `R` as set up by the
caller (the point at infinity). -/
def ladder (L : LadderCfg) (a0 : Bool := false) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 L.nbits))]) (.loop (ladderBody L a0) .ne)

/-- One iteration: `acc = acc²`, `tmp = acc · base`, and `acc = tmp` if the
exponent's bit `rbx - 1` is set. -/
def powBody (P : PowCfg) : Prog isa :=
  .seq (.block ([.alu .sub .rbx (.imm 1)] ++ Mont.X86_64.mul P.M P.acc P.acc P.acc)) <|
  .seq (.block (Mont.X86_64.mul P.M P.tmp P.acc P.base)) <|
    .block (bitMask P.bits ++ sel P.M.n P.acc P.acc P.tmp ++ [.alu .test .rbx (.reg .rbx)])

/-- `[acc] = [base]^e` (in Montgomery form), from the top bit of `e`. -/
def pow (P : PowCfg) : Prog isa :=
  .seq (.block (copy P.M.n P.acc P.one ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 P.nbits))]))
    (.loop (powBody P) .ne)

/-- `[rdi + 8 rbx + d + j]`: bit `j` of byte `rbx` of a number, in a table at `d`. -/
def bitAt (d j : Nat) : MemOp := { base := .rdi, index := some .rbx, scale := 8, disp := d + j }

/-- The table at `dst` of the bits of the `nbytes`-byte little-endian number at
`src`: byte `8i + j` is bit `j` of byte `i` (so byte `t` is bit `t`). -/
def bits (src dst nbytes : Nat) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (.loop (.block (
    [.movzx8 .rax (tbl src)] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1), .store8 (bitAt dst j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm (BitVec.ofNat 32 nbytes))])) .ne)

/-! ## Numbers as bytes -/

/-- `[rdi + o] = ` the `len`-byte big-endian number at `[src]`, in `n` words
(`8 (n - 1) ≤ len ≤ 8 n`, and `8 ≤ len`): word `j` is the byte reversal of
the word at `src + len - 8 (j + 1)`, and a top word of fewer bytes `t` the
first eight bytes' reversal shifted right by `8 (8 - t)` bits. -/
def loadBytes (len n : Nat) (o : Nat) (src : Reg) : List Instr :=
  (List.range n).flatMap fun j =>
    if 8 * (j + 1) ≤ len then
      [.mov .rax (.mem { base := src, disp := ((len - 8 * (j + 1) : Nat) : Int) }), .bswap .rax,
        .store (sc (o + 8 * j)) .rax]
    else if len ≤ 8 * j then
      [.mov .rax (.imm 0), .store (sc (o + 8 * j)) .rax]
    else
      [.mov .rax (.mem { base := src, disp := ((0 : Nat) : Int) }), .bswap .rax,
        .shift .shr .rax (8 * (8 * (j + 1) - len)), .store (sc (o + 8 * j)) .rax]

/-- `[rdi + o] = [rdi + o] >> sh`, `n` words (`0 < sh < 64`), through `rax`
and `rdx`: word `j` is word `j` shifted right, or the low `sh` bits of word
`j + 1` rotated to the top (`x86-64` has no `shl` here). -/
def shrWords (n o sh : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    ([.mov .rax (.mem (sc (o + 8 * j))), .shift .shr .rax sh] : List Instr) ++
    ((if j + 1 < n then
      [.mov .rdx (.mem (sc (o + 8 * (j + 1)))), .alu .and .rdx (.imm (BitVec.ofNat 32 (2 ^ sh - 1))),
        .shift .ror .rdx sh, .alu .or .rax (.reg .rdx)]
    else []) : List Instr) ++
    ([.store (sc (o + 8 * j)) .rax] : List Instr)

/-- `[dst + d] = ` the `n`-word number at `[rdi + a]` masked with `rcx`,
big-endian in `len` bytes (`8 (n - 1) ≤ len ≤ 8 n`): word `j` byte-reversed
at `dst + d + len - 8 (j + 1)`, and a top word of fewer bytes `t` a byte at a
time (through `rdx`). -/
def storeBytes (len n : Nat) (dst : Reg) (d a : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    if 8 * (j + 1) ≤ len then
      [.mov .rax (.mem (sc (a + 8 * j))), .alu .and .rax (.reg .rcx), .bswap .rax,
        .store { base := dst, disp := ((d + (len - 8 * (j + 1)) : Nat) : Int) } .rax]
    else
      ([.mov .rax (.mem (sc (a + 8 * j))), .alu .and .rax (.reg .rcx)] : List Instr) ++
      (List.range (len - 8 * j)).flatMap fun i =>
        ([.mov .rdx (.reg .rax)] : List Instr) ++
        ((if len - 8 * j - 1 - i = 0 then [] else [.shift .shr .rdx (8 * (len - 8 * j - 1 - i))])
          : List Instr) ++
        ([.store8 { base := dst, disp := ((d + i : Nat) : Int) } .rdx] : List Instr)

/-- `[rdi + o] = x`, `n` words. -/
def setConst (n : Nat) (o x : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.movImm64 .rax (BitVec.ofNat 64 (x >>> (64 * j))), .store (sc (o + 8 * j)) .rax]

end VG.Impl.Weierstrass.X86_64
