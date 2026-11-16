import Rind.X86_64.Blockwise
import Rind.X86_64.Sha256Shaext
open Aeneas Aeneas.Std Result rind.spec

/-!
# SHA-1 and SHA-256's block functions on x86_64

SHA-256's routines on the SHA extensions are proven: `Rind.X86_64.Sha256Shaext`
restates their HOL Light proofs as axioms and proves the finish's padding. No
proof covers x86_64's other SHA-1 and SHA-256 block functions, so the theorems
over them take `Sha1Blocks` or `Sha256Blocks` as a hypothesis instead of an
axiom: each routine's contract, FIPS 180-4's block function over every whole
block it is given, and that rind's checks pass. On the SHA extensions, SHA-1
pads its last block in registers, so that routine's contract covers the padding
too. Once a routine's published proof lands, an axiom restating it under the
composition rule discharges its field.
-/

namespace rind.x86_64

/-- What the SHA-1 theorems assume of the code below rind's padding on
x86_64: each routine computes FIPS 180-4's block function, or pads and
compresses as FIPS 180-4 does on the SHA extensions, the CPU dispatch picks
one, and the entry checks pass. None reads an input. -/
structure Sha1Blocks : Prop where
  entry : ∃ e, low.entry.Entry.new_secret = ok e
  held : low.entry.Entry.assert_held = ok ()
  sha1_path : ∃ p, low.x86_64.sha1_mux.path = ok p
  /-- SHA-1's padded compression on the SHA extensions: `m` padded and closed
  by `length`. -/
  sha1_shaext : ∀ t h (m : Slice U8) (length : Std.Array U8 8#usize),
    low.x86_64.sha1.sha1_compress_padded_shaext h m length t ⦃ h' =>
      words h'.val = (blocks 64 (bv (m.val ++ [128#u8] ++
        List.replicate (padZeros 64 8 m.length) 0#u8 ++ length.val))).foldl sha1.compress
          (words h.val) ⦄
  -- After `sha1_shaext`, whose `sha1.compress` would otherwise name this field.
  sha1 : Compresses sha1.compress low.x86_64.sha1_mux.sha1_compress_blocks

/-- What the SHA-256 theorems assume of the code below rind's padding on
x86_64, as `Sha1Blocks` does for SHA-1's, but for the SHA extensions' routines,
which `Rind.X86_64.Sha256Shaext` proves. -/
structure Sha256Blocks : Prop where
  entry : ∃ e, low.entry.Entry.new_secret = ok e
  held : low.entry.Entry.assert_held = ok ()
  path : ∃ p, low.x86_64.sha256_mux.path = ok p
  avx : ∀ t, Compresses sha256.compress fun h b => low.x86_64.sha256.sha256_compress_blocks_avx h b t
  avx2 : ∀ t, Compresses sha256.compress fun h b =>
    low.x86_64.sha256.sha256_compress_blocks_avx2 h b t
  ssse3 : ∀ t, Compresses sha256.compress fun h b =>
    low.x86_64.sha256.sha256_compress_blocks_ssse3 h b t
  nohw : Compresses sha256.compress low.x86_64.sha256.sha256_compress_blocks_nohw

theorem sha256_compress_blocks_spec (hb : Sha256Blocks) :
    Compresses sha256.compress low.x86_64.sha256_mux.sha256_compress_blocks := by
  intro h b hl
  obtain ⟨p, hp⟩ := hb.path
  unfold low.x86_64.sha256_mux.sha256_compress_blocks
  rw [hp]
  cases p with
  | Shaext t => exact (by simpa using sha256_compress_blocks_shaext_compresses t h b hl)
  | Avx t => exact (by simpa using hb.avx t h b hl)
  | Avx2 t => exact (by simpa using hb.avx2 t h b hl)
  | Ssse3 t => exact (by simpa using hb.ssse3 t h b hl)
  | Nohw => exact (by simpa using hb.nohw h b hl)

/-- SHA-256's block function as `Sha256State` calls it. -/
theorem sha256_block_spec (hb : Sha256Blocks) : Compresses sha256.compress mid.sha2.Sha256State.compress := by
  intro h b hl
  unfold mid.sha2.Sha256State.compress
  rw [hb.held]
  simpa using sha256_compress_blocks_spec hb h b hl

/-- SHA-1's block function as `Sha1State` calls it. -/
theorem sha1_block_spec (hb : Sha1Blocks) :
    Compresses sha1.compress mid.sha1.Sha1State.compress := by
  intro h b hl
  unfold mid.sha1.Sha1State.compress
  rw [hb.held]
  simpa using hb.sha1 h b hl

/-- SHA-1's padded last blocks. -/
theorem sha1_compress_padded_spec (hb : Sha1Blocks) (P : List U8) (state : Std.Array U32 5#usize)
    (message : Slice U8) (length : Std.Array U8 8#usize)
    (hR : Absorbed sha1.compress sha1.H0 P state) :
    low.x86_64.sha1_mux.sha1_compress_padded state message length ⦃ h' =>
      Absorbed sha1.compress sha1.H0
        (P ++ message.val ++ [128#u8] ++ List.replicate (padZeros 64 8 message.length) 0#u8 ++
          length.val) h' ⦄ := by
  have fallback :
      (do
        let (blocks, rest) ← low.generic.blockwise.split_tail 64#usize 8#usize message
        let b ← core.slice.Slice.is_empty blocks
        let state1 ← if b then ok state else low.x86_64.sha1_mux.sha1_compress_blocks state blocks
        let a := Std.Array.repeat 64#usize 0#u8
        let last := Std.Array.repeat 2#usize a
        let (s, _) ← low.generic.blockwise.pad rest length last
        low.x86_64.sha1_mux.sha1_compress_blocks state1 s) ⦃ h' =>
        Absorbed sha1.compress sha1.H0
          (P ++ message.val ++ [128#u8] ++ List.replicate (padZeros 64 8 message.length) 0#u8 ++
            length.val) h' ⦄ := by
    step with split_tail_spec (N := 64#usize) (L := 8#usize) message (by decide) (by scalar_tac)
      (by decide) as ⟨bl, re, hs1, hs2, hs3, hs4⟩
    exact compress_tail_spec low.x86_64.sha1_mux.sha1_compress_blocks
      (Absorbed sha1.compress sha1.H0) (P.length + message.length + 9 + 64)
      (fun p s b hR hl _ => by
        apply WP.spec_mono (hb.sha1 s b hl)
        intro h' hh
        exact absorbed_append hR hl hh)
      P message bl re length state hR (by decide) (by scalar_tac) (by decide) ⟨hs1, hs2, hs3, hs4⟩
      (by have h64 : (64#usize).val = 64 := by simp
          have h8 : (8#usize).val = 8 := by simp
          have := padZeros_lt (64#usize).val (8#usize).val message.length (by omega)
          omega)
  obtain ⟨p, hp⟩ := hb.sha1_path
  unfold low.x86_64.sha1_mux.sha1_compress_padded
  rw [hp]
  cases p with
  | Shaext t =>
    simp only [bind_ok]
    apply WP.spec_mono (hb.sha1_shaext t state message length)
    intro h' hh
    have hm := pad_mod (N := 64) (L := 8) message.length (by decide)
    have := absorbed_append hR (b := message.val ++ [128#u8] ++
      List.replicate (padZeros 64 8 message.length) 0#u8 ++ length.val)
      (by simp [Slice.length] at hm ⊢; omega) hh
    simpa only [List.append_assoc] using this
  | Avx2 _ => simp only [bind_ok]; exact fallback
  | Avx _ => simp only [bind_ok]; exact fallback
  | Ssse3 _ => simp only [bind_ok]; exact fallback
  | Nohw => simp only [bind_ok]; exact fallback

/-- SHA-256's padded last blocks, on the routines that do not finish a hash
themselves. -/
theorem sha256_compress_padded_spec (hb : Sha256Blocks) (P : List U8) (state : Std.Array U32 8#usize)
    (message : Slice U8) (length : Std.Array U8 8#usize)
    (hR : Absorbed sha256.compress sha256.H0 P state) :
    low.x86_64.sha256_mux.sha256_compress_padded state message length ⦃ h' =>
      Absorbed sha256.compress sha256.H0
        (P ++ message.val ++ [128#u8] ++ List.replicate (padZeros 64 8 message.length) 0#u8 ++
          length.val) h' ⦄ := by
  have tail : ∀ blocks rest : Slice U8, blocks.length % (64#usize).val = 0 ∧
      blocks.val ++ rest.val = message.val ∧ rest.length + 1 + (8#usize).val ≤ 2 * (64#usize).val ∧
      padZeros (64#usize).val (8#usize).val rest.length =
        padZeros (64#usize).val (8#usize).val message.length →
      (do
        let b ← core.slice.Slice.is_empty blocks
        let state1 ← if b then ok state else low.x86_64.sha256_mux.sha256_compress_blocks state blocks
        let a := Std.Array.repeat 64#usize 0#u8
        let last := Std.Array.repeat 2#usize a
        let (s, _) ← low.generic.blockwise.pad rest length last
        low.x86_64.sha256_mux.sha256_compress_blocks state1 s) ⦃ h' =>
        Absorbed sha256.compress sha256.H0
          (P ++ message.val ++ [128#u8] ++ List.replicate (padZeros 64 8 message.length) 0#u8 ++
            length.val) h' ⦄ :=
    fun blocks rest hs => compress_tail_spec low.x86_64.sha256_mux.sha256_compress_blocks
      (Absorbed sha256.compress sha256.H0) (P.length + message.length + 9 + 64)
      (fun p s b hR hl _ => by
        apply WP.spec_mono (sha256_compress_blocks_spec hb s b hl)
        intro h' hh
        exact absorbed_append hR hl hh)
      P message blocks rest length state hR (by decide) (by scalar_tac) (by decide) hs
      (by have h64 : (64#usize).val = 64 := by simp
          have h8 : (8#usize).val = 8 := by simp
          have := padZeros_lt (64#usize).val (8#usize).val message.length (by omega)
          omega)
  unfold low.x86_64.sha256_mux.sha256_compress_padded
  step with split_tail_spec (N := 64#usize) (L := 8#usize) message (by decide) (by scalar_tac)
    (by decide) as ⟨bl, re, hs1, hs2, hs3, hs4⟩
  exact tail bl re ⟨hs1, hs2, hs3, hs4⟩

/-- The routines that do not finish a hash: the padded last blocks, then the
digest's encoding. -/
theorem sha256_finish_padded_spec (hb : Sha256Blocks) (P : List U8) (state : Std.Array U32 8#usize)
    (message : Slice U8) (length : Std.Array U8 8#usize)
    (hR : Absorbed sha256.compress sha256.H0 P state) :
    (do
      let state1 ← low.x86_64.sha256_mux.sha256_compress_padded state message length
      low.generic.blockwise.sha256_digest state1) ⦃ r =>
        bv r.val = sha256Finished P message.val length.val ⦄ := by
  step with sha256_compress_padded_spec hb P state message length hR as ⟨h', hh'⟩
  apply WP.spec_mono (sha256_digest_spec h')
  intro r hr
  rw [hr, hh'.1]
  rfl

/-- SHA-256's digest of what `state` has absorbed followed by `message`. -/
theorem sha256_finish_spec (hb : Sha256Blocks) (P : List U8) (state : Std.Array U32 8#usize)
    (message : Slice U8) (length : Std.Array U8 8#usize)
    (hR : Absorbed sha256.compress sha256.H0 P state) :
    low.x86_64.sha256_mux.sha256_finish state message length ⦃ r =>
      bv r.val = sha256Finished P message.val length.val ⦄ := by
  obtain ⟨p, hp⟩ := hb.path
  unfold low.x86_64.sha256_mux.sha256_finish
  rw [hp]
  cases p with
  | Shaext t =>
    simp only [bind_ok]
    apply WP.spec_mono (sha256_finish_shaext_spec t state message length)
    intro r hr
    have := sha256Finished_split (b := []) (rest := message.val) (length := length.val) hR
      (by simp)
    rw [hr]
    simpa [Slice.length] using this
  | Avx t => simp only [bind_ok]; exact sha256_finish_padded_spec hb P state message length hR
  | Avx2 t => simp only [bind_ok]; exact sha256_finish_padded_spec hb P state message length hR
  | Ssse3 t => simp only [bind_ok]; exact sha256_finish_padded_spec hb P state message length hR
  | Nohw => simp only [bind_ok]; exact sha256_finish_padded_spec hb P state message length hR

end rind.x86_64
