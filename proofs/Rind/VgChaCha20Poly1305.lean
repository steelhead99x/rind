import Rind.VgChaCha20
import VerifiedGarbage.Spec.ChaCha20Poly1305
open rind.spec

/-!
# pyca/verified-garbage's ChaCha20-Poly1305 spec is `Rind.Spec`'s

pyca/verified-garbage's (VG's) RFC 8439 spec of AEAD_CHACHA20_POLY1305,
`Spec/ChaCha20Poly1305.lean` over `Spec/ChaCha20.lean` and
`Spec/Poly1305.lean`, which `admin/import-vg-models` vendors and its theorems
about the one-pass routines state their results against, is `Rind.Spec`'s
for a 32-byte key and a 12-byte nonce. The theorems are about VG's own
definitions, so a re-pin that changes them fails here.
-/

namespace rind.spec.vg

/-! ## ChaCha20 -/

/-- VG's `chacha20_encrypt` is `Rind.Spec`'s, for a 32-byte key and a 12-byte nonce. -/
theorem vgEncrypt_eq (key : List (BitVec 8)) (counter : BitVec 32) (nonce msg : List (BitVec 8))
    (hk : key.length = 32) (hn : nonce.length = 12) :
    VG.Spec.ChaCha20.encrypt key counter nonce msg = chacha20.encrypt key counter nonce msg := by
  have hg : ∀ j, (chacha20.block key (counter + BitVec.ofNat 32 j) nonce).length = 64 :=
    fun j => s2n.length_block _ _ _ hk hn
  simp only [VG.Spec.ChaCha20.encrypt, chacha20Block_eq _ _ _ hk hn]
  rw [s2n.zipWith_flatMap _ _ hg]
  rfl

/-! ## Poly1305 -/

theorem vgLeNum_eq (l : List (BitVec 8)) : VG.Spec.Poly1305.leNum l = poly1305.leNum l := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [VG.Spec.Poly1305.leNum, ih, poly1305.leNum, List.map_cons, Nat.ofDigits_cons]

theorem vgLeBytes_eq (k n : Nat) : VG.Spec.Poly1305.leBytes k n = s2n.bytelistOfNum k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [VG.Spec.Poly1305.leBytes, List.range_succ_eq_map, List.map_cons, List.map_map,
      s2n.bytelistOfNum, ← ih (n / 256), VG.Spec.Poly1305.leBytes]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd]
    · apply List.map_congr_left
      intro i _
      simp [Function.comp, Nat.pow_succ', Nat.div_div_eq_div_mul]

/-- One block with the byte 1 after it, as a number, is the block's number
plus 2 to its length in bits. -/
theorem leNum_append_one (b : List (BitVec 8)) :
    poly1305.leNum (b ++ [0x01]) = poly1305.leNum b + 2 ^ (8 * b.length) := by
  simp [poly1305.leNum, Nat.ofDigits_append, pow_mul]

/-- VG's `poly1305_mac` is `Rind.Spec`'s, for a 32-byte key. -/
theorem vgMac_eq (key msg : List (BitVec 8)) (hk : key.length = 32) :
    VG.Spec.Poly1305.mac key msg = poly1305.mac key msg := by
  have hc : VG.Spec.Poly1305.clamp = poly1305.clamp := rfl
  have hp : VG.Spec.Poly1305.P = poly1305.p := rfl
  simp only [VG.Spec.Poly1305.mac, poly1305.mac, VG.Spec.Poly1305.accumulate, VG.Spec.Poly1305.numBlocks,
    VG.Spec.Poly1305.block, hc, hp, vgLeNum_eq, leNum_append_one, vgLeBytes_eq, s2n.bytelistOfNum_eq,
    List.take_of_length_le (by simp [hk] : (key.drop 16).length ≤ 16),
    Nat.mul_comm (poly1305.clamp (poly1305.leNum (key.take 16))), Nat.add_assoc]

/-! ## ChaCha20-Poly1305 -/

theorem vgPad16_eq (x : List (BitVec 8)) :
    VG.Spec.ChaCha20Poly1305.pad16 x = chacha20poly1305.pad16 x := by
  rw [VG.Spec.ChaCha20Poly1305.pad16, chacha20poly1305.pad16]
  split
  · next h => simp [h]
  · next h => rw [Nat.mod_eq_of_lt (a := 16 - x.length % 16) (by omega)]

theorem vgMacData_eq (aad ct : List (BitVec 8)) :
    VG.Spec.ChaCha20Poly1305.macData aad ct = chacha20poly1305.macData aad ct := by
  simp [VG.Spec.ChaCha20Poly1305.macData, chacha20poly1305.macData, vgPad16_eq, vgLeBytes_eq,
    s2n.bytelistOfNum_eq]

/-- VG's tag is `Rind.Spec`'s, for a 32-byte key and a 12-byte nonce. -/
theorem vgTag_eq (key nonce aad ct : List (BitVec 8)) (hk : key.length = 32) (hn : nonce.length = 12) :
    VG.Spec.Poly1305.mac (VG.Spec.ChaCha20Poly1305.polyKeyGen key nonce)
        (VG.Spec.ChaCha20Poly1305.macData aad ct) =
      poly1305.mac (chacha20poly1305.otk key nonce) (chacha20poly1305.macData aad ct) := by
  have ho : VG.Spec.ChaCha20Poly1305.polyKeyGen key nonce = chacha20poly1305.otk key nonce := by
    rw [VG.Spec.ChaCha20Poly1305.polyKeyGen, chacha20Block_eq _ _ _ hk hn]
    rfl
  have hl : (chacha20poly1305.otk key nonce).length = 32 := by
    simp [chacha20poly1305.otk, s2n.length_block _ _ _ hk hn]
  rw [ho, vgMacData_eq, vgMac_eq _ _ hl]

/-- VG's `chacha20_aead_encrypt` is `Rind.Spec`'s seal, for a 32-byte key and
a 12-byte nonce. -/
theorem vgSeal_eq (key nonce aad msg : List (BitVec 8)) (hk : key.length = 32) (hn : nonce.length = 12) :
    VG.Spec.ChaCha20Poly1305.encrypt key nonce aad msg = chacha20poly1305.seal key nonce aad msg := by
  rw [VG.Spec.ChaCha20Poly1305.encrypt, chacha20poly1305.seal, vgEncrypt_eq _ _ _ _ hk hn,
    vgTag_eq _ _ _ _ hk hn]

/-- VG's decryption is `Rind.Spec`'s open, whose plaintext it returns only
where the tag matches, for a 32-byte key and a 12-byte nonce. -/
theorem vgOpen_eq (key nonce aad ct tag : List (BitVec 8)) (hk : key.length = 32) (hn : nonce.length = 12) :
    VG.Spec.ChaCha20Poly1305.decrypt key nonce aad ct tag =
      if (chacha20poly1305.open key nonce aad ct tag).2 then
        some (chacha20poly1305.open key nonce aad ct tag).1
      else none := by
  rw [VG.Spec.ChaCha20Poly1305.decrypt, chacha20poly1305.open, vgTag_eq _ _ _ _ hk hn,
    vgEncrypt_eq _ _ _ _ hk hn]
  by_cases h : poly1305.mac (chacha20poly1305.otk key nonce) (chacha20poly1305.macData aad ct) = tag <;>
    simp [h]

end rind.spec.vg
