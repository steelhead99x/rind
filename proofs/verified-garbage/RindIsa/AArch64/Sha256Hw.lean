import RindIsa.AArch64

/-!
# aws-lc's SHA-256 block function for the SHA-2 instructions

rind's naked function `low::aarch64::sha256::sha256_block_data_order_hw`,
aws-lc's `sha256_block_data_order_hw` (`crypto/fipsmodule/sha/asm/
sha512-armv8.pl`, its ARMv8 path), in rind's model of AArch64:
`sha256_block_data_order_hw(state = x0, data = x1, blocks = x2)`. The state
stays in `v0` and `v1` across the blocks; each block's sixteen message words
load into `v4`–`v7`, which SHA256SU0 and SHA256SU1 expand four words at a
time, and each group of four rounds adds the round constants, loaded from
the table `K256` that `x3` walks, to the schedule in `v16` or `v17`, one
group ahead, for SHA256H and SHA256H2.

`admin/prove lean` checks that `function prog` is the function's bytes and
relocations as rind's build emits it, and that the static `K256` begins with
`table`'s words.
-/

namespace Rind.AArch64.Sha256Hw

open VG VG.AArch64

/-- The name of the static of round constants. -/
def kName : String := "K256"

/-- FIPS 180-4's SHA-256 constants, the words the table `K256` begins
with. -/
def table : List (BitVec 32) :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The register holding schedule words `4i` to `4i + 3`. -/
def msg (i : Nat) : VReg := [.v4, .v5, .v6, .v7].getD (i % 4) .v4

/-- The register the constants of group `i` load into, and its sum with
the schedule. -/
def kreg (i : Nat) : VReg := if i % 2 = 0 then .v16 else .v17

def vop (o : VOp) : Instr := .vg (.vop o)

/-- Group `i` of four rounds: load the next group's constants (the last
group's without advancing `x3`, which then rewinds to the table's start for
the next block), add this group's to its schedule words,
schedule four more words while any group needs them, and run the rounds. -/
def group (i : Nat) : List Instr :=
  (if i < 14 then [.ld1 1 .s4 (kreg (i + 1)) .x3 true]
   else if i = 14 then [.ld1 1 .s4 (kreg (i + 1)) .x3 false] else []) ++
  [vop (.add .s4 (kreg i) (kreg i) (msg i))] ++
  (if i < 12 then [vop (.sha256su0 (msg i) (msg (i + 1)))] else []) ++
  (if i = 14 then [.vg (.subImm .x .x3 .x3 240)] else []) ++
  [vop (.mov .v2 .v0), vop (.sha256h .v0 .v1 (kreg i)), vop (.sha256h2 .v1 .v2 (kreg i))] ++
  (if i < 12 then [vop (.sha256su1 (msg i) (msg (i + 2)) (msg (i + 3)))] else [])

/-- Load the block, byte-reversing its words, and the first group's
constants, and keep the state for the feed-forward. -/
def head : List Instr :=
  [.ld1 4 .b16 .v4 .x1 true, .vg (.subImm .x .x2 .x2 1), .ld1 1 .s4 .v16 .x3 true,
   vop (.rev .rev32b .v4 .v4), vop (.rev .rev32b .v5 .v5), vop (.rev .rev32b .v6 .v6),
   vop (.rev .rev32b .v7 .v7), vop (.mov .v18 .v0), vop (.mov .v19 .v1)]

/-- Add the state the block started from. -/
def tail : List Instr := [vop (.add .s4 .v0 .v0 .v18), vop (.add .s4 .v1 .v1 .v19)]

/-- One block. -/
def body : List Instr := head ++ (List.range 16).flatMap group ++ tail

/-- Save the frame, load the state, and address the table. -/
def prologue : List Instr := [.stpFrame, .movFp, .ld1 2 .s4 .v0 .x0 false, .vg (.adrSym .x3 kName)]

/-- Store the state and restore the frame pointer. -/
def epilogue : List Instr := [.st1 2 .s4 .v0 .x0 false, .ldrFp]

/-- The function, but for its `ret`: the blocks in a loop while `x2`, the
count left, is not zero, so at least one runs. -/
def prog : Prog isa :=
  .seq (.block prologue) (.seq (.loop (.block body) (.nonzero .x .x2)) (.block epilogue))

end Rind.AArch64.Sha256Hw
