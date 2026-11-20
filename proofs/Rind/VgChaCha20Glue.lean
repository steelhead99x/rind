import Rind.VgChaCha20
import Rind.VgCurve25519
open Aeneas Aeneas.Std rind.spec
open VG.Spec.ChaCha20 (bytesAt leftAt restAt keystreamOf wordLE)

/-!
# What both targets' proofs of `cipher::ChaCha20`'s glue share

x86_64 and aarch64 keep the key and the block counter and nonce as `u32`
words, whose little-endian bytes are what pyca/verified-garbage's (VG's)
routines read, and start a keystream with `init` that the `apply` routines
XOR in. These facts about the words and that keystream name nothing either
target's translation defines, so both `Rind.X86_64.VgChaCha20` and
`Rind.Aarch64.VgChaCha20` take them from here.
-/

namespace rind.spec.vg

/-- Words as memory holds them: each one's little-endian bytes. -/
def wordBytes (ws : List U32) : List (BitVec 8) := (ws.map (·.bv)).flatMap BitVec.toLEBytes

theorem length_wordBytes (ws : List U32) : (wordBytes ws).length = 4 * ws.length := by
  rw [wordBytes, length_flatMap_toLEBytes, List.length_map]

theorem wordBytes_drop_one (ws : List U32) : (wordBytes ws).drop 4 = wordBytes (ws.drop 1) := by
  cases ws with
  | nil => simp [wordBytes]
  | cons w ws =>
    simp only [wordBytes, List.map_cons, List.flatMap_cons, List.drop_one, List.tail_cons]
    rw [List.drop_append_of_le_length (by simp [BitVec.toLEBytes_length]),
      List.drop_eq_nil_of_le (by simp [BitVec.toLEBytes_length]), List.nil_append]

theorem wordLE_wordBytes (ws : List U32) (h : 0 < ws.length) : wordLE (wordBytes ws) 0 = ws[0]!.bv := by
  rw [wordBytes, wordLE_flatMap _ 0 (by simpa using h)]
  cases ws with
  | nil => simp at h
  | cons w ws => rfl

/-- Words read from bytes, as `Rind.Spec`'s `words` reads them, written back
out are those bytes. -/
theorem wordBytes_of_words (ws : List U32) (b : List (BitVec 8)) (n : Nat) (hb : b.length = 4 * n)
    (hw : ws.map (·.bv) = chacha20.words b) : wordBytes ws = b := by
  rw [wordBytes, hw, flatMap_words b n hb]

/-- VG's theorems hold for any memory holding the state: memory holding only
the state's 768 bytes, from address 0, does. -/
theorem bytesAt_mem_state (x : Std.Array U8 768#usize) : bytesAt (vg.mem (bvs x.val)) 0 768 = bvs x.val := by
  have hx : (bvs x.val).length = 768 := by simp [bvs]
  simpa [hx] using bytesAt_mem (bvs x.val) (by rw [hx]; decide)

/-- What a state `init` started holds, for a buffer the keystream covers. -/
theorem leftAt_init (m : VG.Mem) (p : VG.Addr) (key : Std.Array U32 8#usize)
    (counter_nonce : Std.Array U32 4#usize)
    (hr : restAt m p = keystreamOf (wordBytes key.val) (wordBytes counter_nonce.val)) (n : Nat)
    (hl : counter_nonce.val[0]!.val + (n + 63) / 64 ≤ 2 ^ 32) : n ≤ leftAt m p := by
  rw [← length_restAt, hr, length_keystreamOf _ _ (by simp [length_wordBytes])
    (by simp [length_wordBytes]), wordLE_wordBytes _ (by simp)]
  simp only [UScalar.bv_toNat]
  omega

/-- The keystream `init` sets up, XORed into a buffer it covers. -/
theorem keystream_encrypt (key : Std.Array U32 8#usize) (counter_nonce : Std.Array U32 4#usize)
    (msg : List (BitVec 8)) (hl : counter_nonce.val[0]!.val + (msg.length + 63) / 64 ≤ 2 ^ 32) :
    List.zipWith (· ^^^ ·) msg
        ((keystreamOf (wordBytes key.val) (wordBytes counter_nonce.val)).take msg.length) =
      chacha20.encrypt (wordBytes key.val) counter_nonce.val[0]!.bv
        (wordBytes (counter_nonce.val.drop 1)) msg := by
  have hk : (wordBytes key.val).length = 32 := by simp [length_wordBytes]
  have hn : (wordBytes counter_nonce.val).length = 16 := by simp [length_wordBytes]
  rw [keystreamOf_encrypt _ _ _ hk hn, wordLE_wordBytes _ (by simp), wordBytes_drop_one]
  rw [length_keystreamOf _ _ hk hn, wordLE_wordBytes _ (by simp)]
  simp only [UScalar.bv_toNat]
  omega

/-- Setting each index of a list from `k` on to `f`'s value there. -/
theorem foldl_set_range' {α : Type} (f : Nat → α) (a : List α) (k m : Nat) (h : k + m = a.length) :
    (List.range' k m).foldl (fun l i => l.set i (f i)) a = a.take k ++ (List.range' k m).map f := by
  induction m generalizing k a with
  | zero => simp [List.take_of_length_le (by omega : a.length ≤ k)]
  | succ m ih =>
    have hk : k < a.length := by omega
    rw [List.range'_succ, List.foldl_cons, ih _ (k + 1) (by simp; omega), List.map_cons, List.take_add_one,
      List.take_set_of_le (Nat.le_refl k), List.getElem?_set_self hk]
    simp

end rind.spec.vg
