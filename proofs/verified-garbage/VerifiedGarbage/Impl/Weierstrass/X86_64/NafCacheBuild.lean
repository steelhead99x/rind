module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Naf

/-! Precompute Z² and Z³ once for each public odd-multiple table entry. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Naf
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64

def cachePairOps (n ptbl tbl i : Nat) : List FOp :=
  [.mul (tbl+16*n*i) (ptbl+24*n*i+16*n) (ptbl+24*n*i+16*n),
   .mul (tbl+16*n*i+8*n) (tbl+16*n*i) (ptbl+24*n*i+16*n)]

def cachePair (M : Mod) (ptbl tbl i : Nat) : Prog isa :=
  if M.adx ∧ M.n = 4 then ForwardField.program M [] (cachePairOps M.n ptbl tbl i)
  else fprogB M (cachePairOps M.n ptbl tbl i)

/-- The first `k` entries unrolled; no secret-dependent loop or address. -/
def cacheUnrolled (M : Mod) (ptbl tbl : Nat) : Nat → Prog isa
  | 0 => .block []
  | k+1 => .seq (cacheUnrolled M ptbl tbl k) (cachePair M ptbl tbl k)

/-- `o = z²` and `o + 8 n = z³`. -/
def cacheOps (n z o : Nat) : List FOp :=
  [.mul o z z, .mul (o+8*n) o z]

def cacheMul (M : Mod) (z o : Nat) : Prog isa :=
  if M.adx ∧ M.n = 4 then ForwardField.program M [] (cacheOps M.n z o)
  else fprogB M (cacheOps M.n z o)

/-- Piece `i` of `w` words: `16 i`, but the last at its last 16 bytes. -/
def wordPieceOff (w i : Nat) : Nat := if i + 1 < (w + 1) / 2 then 16 * i else 8 * w - 16

/-- `Z` of entry `rbx` of the table at `ptbl` into `z`. -/
def cacheLoad (n ptbl z : Nat) : List Instr :=
  [.mov .rax (.reg .rbx)] ++ tableAddress n ptbl ++
  copyPieces ((n+1)/2) (fun i => tblAt (16*n+wordPieceOff n i)) (fun i => sc (z+wordPieceOff n i))

/-- The `16 n` bytes at `o` into entry `rbx` of the cache at `tbl`. -/
def cacheStore (n tbl o : Nat) : List Instr :=
  [.mov .rax (.reg .rbx)] ++ stridedAddress (16*n) tbl ++
  copyPieces n (fun i => sc (o+16*i)) (fun i => tblAt (16*i))

/-- Entry `rbx`: its `Z` into `e + 16 n`, `Z²` and `Z³` into `e` and
`e + 8 n`, and both into the cache. -/
def cacheStep (M : Mod) (ptbl tbl e : Nat) : Prog isa :=
  .seq (.block (cacheLoad M.n ptbl (e+16*M.n))) <|
  .seq (cacheMul M (e+16*M.n) e) <|
    .block (cacheStore M.n tbl e ++ [.alu .add .rbx (.imm 1),.alu .cmp .rbx (.imm 8)])

/-- A loop over the eight entries, by the public counter `rbx`. -/
def cacheTable (M : Mod) (ptbl tbl e : Nat) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (.loop (cacheStep M ptbl tbl e) .b)

/-- The first `k` steps of the loop, one after the other. -/
def cacheSteps (M : Mod) (ptbl tbl e : Nat) : Nat → Prog isa
  | 0 => .block []
  | k+1 => .seq (cacheSteps M ptbl tbl e k) (cacheStep M ptbl tbl e)

/-- The loop's eight steps unrolled: each entry's products are on `e`'s
slots, below the table, so that nine-word products are calls of
`vg_p521_mul_mod_p` rather than written out. -/
def cacheStaged (M : Mod) (ptbl tbl e : Nat) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 0)]) (cacheSteps M ptbl tbl e 8)

end VG.Impl.Weierstrass.X86_64.Naf
