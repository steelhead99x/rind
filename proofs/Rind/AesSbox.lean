import Rind.Vale

/-!
# FIPS 197's S-box, as its table

`sboxTree` is FIPS 197's Figure 7, the S-box's 256 values, as a decision tree
on the input's bits, most significant first, and `sbox_eq_tree` proves it
Vale's `sbox`, by computing `fips197Sbox` on every byte. A proof of an S-box
circuit, such as the bitsliced AES's, compares against the tree, which
`bv_decide` reads, where `fips197Sbox`'s 254 field products are out of its
reach.
-/

namespace rind.vale

/-- FIPS 197's Figure 7. -/
def sboxTree (c : BitVec 8) : BitVec 8 :=
  bif c.getLsbD 7
    then bif c.getLsbD 6
      then bif c.getLsbD 5
        then bif c.getLsbD 4
          then bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x16#8 else 0xbb#8
                else bif c.getLsbD 0 then 0x54#8 else 0xb0#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x0f#8 else 0x2d#8
                else bif c.getLsbD 0 then 0x99#8 else 0x41#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x68#8 else 0x42#8
                else bif c.getLsbD 0 then 0xe6#8 else 0xbf#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x0d#8 else 0x89#8
                else bif c.getLsbD 0 then 0xa1#8 else 0x8c#8
          else bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xdf#8 else 0x28#8
                else bif c.getLsbD 0 then 0x55#8 else 0xce#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xe9#8 else 0x87#8
                else bif c.getLsbD 0 then 0x1e#8 else 0x9b#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x94#8 else 0x8e#8
                else bif c.getLsbD 0 then 0xd9#8 else 0x69#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x11#8 else 0x98#8
                else bif c.getLsbD 0 then 0xf8#8 else 0xe1#8
        else bif c.getLsbD 4
          then bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x9e#8 else 0x1d#8
                else bif c.getLsbD 0 then 0xc1#8 else 0x86#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xb9#8 else 0x57#8
                else bif c.getLsbD 0 then 0x35#8 else 0x61#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x0e#8 else 0xf6#8
                else bif c.getLsbD 0 then 0x03#8 else 0x48#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x66#8 else 0xb5#8
                else bif c.getLsbD 0 then 0x3e#8 else 0x70#8
          else bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x8a#8 else 0x8b#8
                else bif c.getLsbD 0 then 0xbd#8 else 0x4b#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x1f#8 else 0x74#8
                else bif c.getLsbD 0 then 0xdd#8 else 0xe8#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xc6#8 else 0xb4#8
                else bif c.getLsbD 0 then 0xa6#8 else 0x1c#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x2e#8 else 0x25#8
                else bif c.getLsbD 0 then 0x78#8 else 0xba#8
      else bif c.getLsbD 5
        then bif c.getLsbD 4
          then bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x08#8 else 0xae#8
                else bif c.getLsbD 0 then 0x7a#8 else 0x65#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xea#8 else 0xf4#8
                else bif c.getLsbD 0 then 0x56#8 else 0x6c#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xa9#8 else 0x4e#8
                else bif c.getLsbD 0 then 0xd5#8 else 0x8d#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x6d#8 else 0x37#8
                else bif c.getLsbD 0 then 0xc8#8 else 0xe7#8
          else bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x79#8 else 0xe4#8
                else bif c.getLsbD 0 then 0x95#8 else 0x91#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x62#8 else 0xac#8
                else bif c.getLsbD 0 then 0xd3#8 else 0xc2#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x5c#8 else 0x24#8
                else bif c.getLsbD 0 then 0x06#8 else 0x49#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x0a#8 else 0x3a#8
                else bif c.getLsbD 0 then 0x32#8 else 0xe0#8
        else bif c.getLsbD 4
          then bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xdb#8 else 0x0b#8
                else bif c.getLsbD 0 then 0x5e#8 else 0xde#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x14#8 else 0xb8#8
                else bif c.getLsbD 0 then 0xee#8 else 0x46#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x88#8 else 0x90#8
                else bif c.getLsbD 0 then 0x2a#8 else 0x22#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xdc#8 else 0x4f#8
                else bif c.getLsbD 0 then 0x81#8 else 0x60#8
          else bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x73#8 else 0x19#8
                else bif c.getLsbD 0 then 0x5d#8 else 0x64#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x3d#8 else 0x7e#8
                else bif c.getLsbD 0 then 0xa7#8 else 0xc4#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x17#8 else 0x44#8
                else bif c.getLsbD 0 then 0x97#8 else 0x5f#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xec#8 else 0x13#8
                else bif c.getLsbD 0 then 0x0c#8 else 0xcd#8
    else bif c.getLsbD 6
      then bif c.getLsbD 5
        then bif c.getLsbD 4
          then bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xd2#8 else 0xf3#8
                else bif c.getLsbD 0 then 0xff#8 else 0x10#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x21#8 else 0xda#8
                else bif c.getLsbD 0 then 0xb6#8 else 0xbc#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xf5#8 else 0x38#8
                else bif c.getLsbD 0 then 0x9d#8 else 0x92#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x8f#8 else 0x40#8
                else bif c.getLsbD 0 then 0xa3#8 else 0x51#8
          else bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xa8#8 else 0x9f#8
                else bif c.getLsbD 0 then 0x3c#8 else 0x50#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x7f#8 else 0x02#8
                else bif c.getLsbD 0 then 0xf9#8 else 0x45#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x85#8 else 0x33#8
                else bif c.getLsbD 0 then 0x4d#8 else 0x43#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xfb#8 else 0xaa#8
                else bif c.getLsbD 0 then 0xef#8 else 0xd0#8
        else bif c.getLsbD 4
          then bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xcf#8 else 0x58#8
                else bif c.getLsbD 0 then 0x4c#8 else 0x4a#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x39#8 else 0xbe#8
                else bif c.getLsbD 0 then 0xcb#8 else 0x6a#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x5b#8 else 0xb1#8
                else bif c.getLsbD 0 then 0xfc#8 else 0x20#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xed#8 else 0x00#8
                else bif c.getLsbD 0 then 0xd1#8 else 0x53#8
          else bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x84#8 else 0x2f#8
                else bif c.getLsbD 0 then 0xe3#8 else 0x29#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xb3#8 else 0xd6#8
                else bif c.getLsbD 0 then 0x3b#8 else 0x52#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xa0#8 else 0x5a#8
                else bif c.getLsbD 0 then 0x6e#8 else 0x1b#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x1a#8 else 0x2c#8
                else bif c.getLsbD 0 then 0x83#8 else 0x09#8
      else bif c.getLsbD 5
        then bif c.getLsbD 4
          then bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x75#8 else 0xb2#8
                else bif c.getLsbD 0 then 0x27#8 else 0xeb#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xe2#8 else 0x80#8
                else bif c.getLsbD 0 then 0x12#8 else 0x07#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x9a#8 else 0x05#8
                else bif c.getLsbD 0 then 0x96#8 else 0x18#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xc3#8 else 0x23#8
                else bif c.getLsbD 0 then 0xc7#8 else 0x04#8
          else bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x15#8 else 0x31#8
                else bif c.getLsbD 0 then 0xd8#8 else 0x71#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xf1#8 else 0xe5#8
                else bif c.getLsbD 0 then 0xa5#8 else 0x34#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xcc#8 else 0xf7#8
                else bif c.getLsbD 0 then 0x3f#8 else 0x36#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x26#8 else 0x93#8
                else bif c.getLsbD 0 then 0xfd#8 else 0xb7#8
        else bif c.getLsbD 4
          then bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xc0#8 else 0x72#8
                else bif c.getLsbD 0 then 0xa4#8 else 0x9c#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xaf#8 else 0xa2#8
                else bif c.getLsbD 0 then 0xd4#8 else 0xad#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xf0#8 else 0x47#8
                else bif c.getLsbD 0 then 0x59#8 else 0xfa#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x7d#8 else 0xc9#8
                else bif c.getLsbD 0 then 0x82#8 else 0xca#8
          else bif c.getLsbD 3
            then bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x76#8 else 0xab#8
                else bif c.getLsbD 0 then 0xd7#8 else 0xfe#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x2b#8 else 0x67#8
                else bif c.getLsbD 0 then 0x01#8 else 0x30#8
            else bif c.getLsbD 2
              then bif c.getLsbD 1
                then bif c.getLsbD 0 then 0xc5#8 else 0x6f#8
                else bif c.getLsbD 0 then 0x6b#8 else 0xf2#8
              else bif c.getLsbD 1
                then bif c.getLsbD 0 then 0x7b#8 else 0x77#8
                else bif c.getLsbD 0 then 0x7c#8 else 0x63#8

/-- Whether `fips197Sbox` is `sboxTree` on the 16 bytes from `lo`. -/
def treeAgrees (lo : Nat) : Bool :=
  (List.range' lo 16).all fun n => fips197Sbox (BitVec.ofNat 8 n) == sboxTree (BitVec.ofNat 8 n)

/-! The kernel keeps what it reduces until it has checked the declaration, so
one check of all 256 bytes peaks at 13 GB; sixteen bytes a declaration keep it
near the rest of the build's. -/

theorem treeAgrees_0 : treeAgrees 0 = true := by decide +kernel
theorem treeAgrees_1 : treeAgrees 16 = true := by decide +kernel
theorem treeAgrees_2 : treeAgrees 32 = true := by decide +kernel
theorem treeAgrees_3 : treeAgrees 48 = true := by decide +kernel
theorem treeAgrees_4 : treeAgrees 64 = true := by decide +kernel
theorem treeAgrees_5 : treeAgrees 80 = true := by decide +kernel
theorem treeAgrees_6 : treeAgrees 96 = true := by decide +kernel
theorem treeAgrees_7 : treeAgrees 112 = true := by decide +kernel
theorem treeAgrees_8 : treeAgrees 128 = true := by decide +kernel
theorem treeAgrees_9 : treeAgrees 144 = true := by decide +kernel
theorem treeAgrees_10 : treeAgrees 160 = true := by decide +kernel
theorem treeAgrees_11 : treeAgrees 176 = true := by decide +kernel
theorem treeAgrees_12 : treeAgrees 192 = true := by decide +kernel
theorem treeAgrees_13 : treeAgrees 208 = true := by decide +kernel
theorem treeAgrees_14 : treeAgrees 224 = true := by decide +kernel
theorem treeAgrees_15 : treeAgrees 240 = true := by decide +kernel

/-- Vale's S-box is the table. -/
theorem sbox_eq_tree (c : BitVec 8) : sbox c = sboxTree c := by
  have chunk : ∀ k < 16, treeAgrees (16 * k) = true
    | 0, _ => treeAgrees_0 | 1, _ => treeAgrees_1 | 2, _ => treeAgrees_2
    | 3, _ => treeAgrees_3 | 4, _ => treeAgrees_4 | 5, _ => treeAgrees_5
    | 6, _ => treeAgrees_6 | 7, _ => treeAgrees_7 | 8, _ => treeAgrees_8
    | 9, _ => treeAgrees_9 | 10, _ => treeAgrees_10 | 11, _ => treeAgrees_11
    | 12, _ => treeAgrees_12 | 13, _ => treeAgrees_13 | 14, _ => treeAgrees_14
    | 15, _ => treeAgrees_15 | _ + 16, h => absurd h (by omega)
  have h := chunk (c.toNat / 16) (by omega)
  rw [treeAgrees, List.all_eq_true] at h
  have := h c.toNat (by simp only [List.mem_range'_1]; omega)
  rw [sbox_eq]
  simpa using this

end rind.vale
