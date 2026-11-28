(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* aws-lc's gcm_ghash_neon, as rind's build emits it.                       *)
(* ========================================================================= *)

(* The A32 routine `gcm_ghash_neon` in rind's low::arm::ghash_armv4, which
   armv7 runs for GHASH without the crypto extension, with the key
   gcm_init_neon twisted. Its theorems hold for a caller in A32 or T32, so
   they cover every armv7 target. *)

needs "aarch32/proofs/base.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;

(* admin/prove writes the routine's bytes, as rind's release build for
   armv7-unknown-linux-gnueabihf emits them, to armv7/gcm_ghash_neon.bin,
   and the definition fails unless they are these. The routine is A32 on
   every target. *)
let gcm_ghash_neon_mc = define_assert_word_list "gcm_ghash_neon_mc"
  (term_of_bytes (load_file "armv7/gcm_ghash_neon.bin"))
[
  0xf42017cd; (* vld1.64 {d1}, [r0]! *)
  0xf42007cd; (* vld1.64 {d0}, [r0]! *)
  0xf2c3de3f; (* vmov.i64 d29, #0xffffffffffff *)
  0xecd1ab04; (* vldmia r1, {d26, d27} *)
  0xf2c0ee3f; (* vmov.i64 d30, #0xffffffff *)
  0xf3b00040; (* vrev64.8 q0, q0 *)
  0xf2c0fe33; (* vmov.i64 d31, #0xffff *)
  0xf34ac1bb; (* veor d28, d26, d27 *)
  0xf42277cd; (* vld1.64 {d7}, [r2]! *)
  0xf42267cd; (* vld1.64 {d6}, [r2]! *)
  0xf3b06046; (* vrev64.8 q3, q3 *)
  0xf3066150; (* veor q3, q3, q0 *)
  0xf2fa01aa; (* vext.8 d16, d26, d26, #0x1 *)
  0xf2c00e86; (* vmull.p8 q8, d16, d6 *)
  0xf2b60106; (* vext.8 d0, d6, d6, #0x1 *)
  0xf28a0e80; (* vmull.p8 q0, d26, d0 *)
  0xf2fa22aa; (* vext.16 d18, d26, d26, #0x1 *)
  0xf2c22e86; (* vmull.p8 q9, d18, d6 *)
  0xf2f66206; (* vext.16 d22, d6, d6, #0x1 *)
  0xf2ca6ea6; (* vmull.p8 q11, d26, d22 *)
  0xf2fa43aa; (* vext.8 d20, d26, d26, #0x3 *)
  0xf34001d0; (* veor q8, q8, q0 *)
  0xf2c44e86; (* vmull.p8 q10, d20, d6 *)
  0xf2b60306; (* vext.8 d0, d6, d6, #0x3 *)
  0xf34221f6; (* veor q9, q9, q11 *)
  0xf28a0e80; (* vmull.p8 q0, d26, d0 *)
  0xf34001b1; (* veor d16, d16, d17 *)
  0xf24111bd; (* vand d17, d17, d29 *)
  0xf2f66406; (* vext.32 d22, d6, d6, #0x1 *)
  0xf34221b3; (* veor d18, d18, d19 *)
  0xf24331be; (* vand d19, d19, d30 *)
  0xf2ca6ea6; (* vmull.p8 q11, d26, d22 *)
  0xf34441d0; (* veor q10, q10, q0 *)
  0xf34001b1; (* veor d16, d16, d17 *)
  0xf34221b3; (* veor d18, d18, d19 *)
  0xf34441b5; (* veor d20, d20, d21 *)
  0xf24551bf; (* vand d21, d21, d31 *)
  0xf2f00fe0; (* vext.8 q8, q8, q8, #0xf *)
  0xf34661b7; (* veor d22, d22, d23 *)
  0xf2c07e30; (* vmov.i64 d23, #0x0 *)
  0xf2f22ee2; (* vext.16 q9, q9, q9, #0x7 *)
  0xf34441b5; (* veor d20, d20, d21 *)
  0xf28a0e86; (* vmull.p8 q0, d26, d6 *)
  0xf2f66ce6; (* vext.32 q11, q11, q11, #0x3 *)
  0xf2f44de4; (* vext.8 q10, q10, q10, #0xd *)
  0xf34001f2; (* veor q8, q8, q9 *)
  0xf34441f6; (* veor q10, q10, q11 *)
  0xf3000170; (* veor q0, q0, q8 *)
  0xf3000174; (* veor q0, q0, q10 *)
  0xf3066117; (* veor d6, d6, d7 *)
  0xf2fc01ac; (* vext.8 d16, d28, d28, #0x1 *)
  0xf2c00e86; (* vmull.p8 q8, d16, d6 *)
  0xf2b62106; (* vext.8 d2, d6, d6, #0x1 *)
  0xf28c2e82; (* vmull.p8 q1, d28, d2 *)
  0xf2fc22ac; (* vext.16 d18, d28, d28, #0x1 *)
  0xf2c22e86; (* vmull.p8 q9, d18, d6 *)
  0xf2f66206; (* vext.16 d22, d6, d6, #0x1 *)
  0xf2cc6ea6; (* vmull.p8 q11, d28, d22 *)
  0xf2fc43ac; (* vext.8 d20, d28, d28, #0x3 *)
  0xf34001d2; (* veor q8, q8, q1 *)
  0xf2c44e86; (* vmull.p8 q10, d20, d6 *)
  0xf2b62306; (* vext.8 d2, d6, d6, #0x3 *)
  0xf34221f6; (* veor q9, q9, q11 *)
  0xf28c2e82; (* vmull.p8 q1, d28, d2 *)
  0xf34001b1; (* veor d16, d16, d17 *)
  0xf24111bd; (* vand d17, d17, d29 *)
  0xf2f66406; (* vext.32 d22, d6, d6, #0x1 *)
  0xf34221b3; (* veor d18, d18, d19 *)
  0xf24331be; (* vand d19, d19, d30 *)
  0xf2cc6ea6; (* vmull.p8 q11, d28, d22 *)
  0xf34441d2; (* veor q10, q10, q1 *)
  0xf34001b1; (* veor d16, d16, d17 *)
  0xf34221b3; (* veor d18, d18, d19 *)
  0xf34441b5; (* veor d20, d20, d21 *)
  0xf24551bf; (* vand d21, d21, d31 *)
  0xf2f00fe0; (* vext.8 q8, q8, q8, #0xf *)
  0xf34661b7; (* veor d22, d22, d23 *)
  0xf2c07e30; (* vmov.i64 d23, #0x0 *)
  0xf2f22ee2; (* vext.16 q9, q9, q9, #0x7 *)
  0xf34441b5; (* veor d20, d20, d21 *)
  0xf28c2e86; (* vmull.p8 q1, d28, d6 *)
  0xf2f66ce6; (* vext.32 q11, q11, q11, #0x3 *)
  0xf2f44de4; (* vext.8 q10, q10, q10, #0xd *)
  0xf34001f2; (* veor q8, q8, q9 *)
  0xf34441f6; (* veor q10, q10, q11 *)
  0xf3022170; (* veor q1, q1, q8 *)
  0xf3022174; (* veor q1, q1, q10 *)
  0xf2fb01ab; (* vext.8 d16, d27, d27, #0x1 *)
  0xf2c00e87; (* vmull.p8 q8, d16, d7 *)
  0xf2b74107; (* vext.8 d4, d7, d7, #0x1 *)
  0xf28b4e84; (* vmull.p8 q2, d27, d4 *)
  0xf2fb22ab; (* vext.16 d18, d27, d27, #0x1 *)
  0xf2c22e87; (* vmull.p8 q9, d18, d7 *)
  0xf2f76207; (* vext.16 d22, d7, d7, #0x1 *)
  0xf2cb6ea6; (* vmull.p8 q11, d27, d22 *)
  0xf2fb43ab; (* vext.8 d20, d27, d27, #0x3 *)
  0xf34001d4; (* veor q8, q8, q2 *)
  0xf2c44e87; (* vmull.p8 q10, d20, d7 *)
  0xf2b74307; (* vext.8 d4, d7, d7, #0x3 *)
  0xf34221f6; (* veor q9, q9, q11 *)
  0xf28b4e84; (* vmull.p8 q2, d27, d4 *)
  0xf34001b1; (* veor d16, d16, d17 *)
  0xf24111bd; (* vand d17, d17, d29 *)
  0xf2f76407; (* vext.32 d22, d7, d7, #0x1 *)
  0xf34221b3; (* veor d18, d18, d19 *)
  0xf24331be; (* vand d19, d19, d30 *)
  0xf2cb6ea6; (* vmull.p8 q11, d27, d22 *)
  0xf34441d4; (* veor q10, q10, q2 *)
  0xf34001b1; (* veor d16, d16, d17 *)
  0xf34221b3; (* veor d18, d18, d19 *)
  0xf34441b5; (* veor d20, d20, d21 *)
  0xf24551bf; (* vand d21, d21, d31 *)
  0xf2f00fe0; (* vext.8 q8, q8, q8, #0xf *)
  0xf34661b7; (* veor d22, d22, d23 *)
  0xf2c07e30; (* vmov.i64 d23, #0x0 *)
  0xf2f22ee2; (* vext.16 q9, q9, q9, #0x7 *)
  0xf34441b5; (* veor d20, d20, d21 *)
  0xf28b4e87; (* vmull.p8 q2, d27, d7 *)
  0xf2f66ce6; (* vext.32 q11, q11, q11, #0x3 *)
  0xf2f44de4; (* vext.8 q10, q10, q10, #0xd *)
  0xf34001f2; (* veor q8, q8, q9 *)
  0xf34441f6; (* veor q10, q10, q11 *)
  0xf3044170; (* veor q2, q2, q8 *)
  0xf3044174; (* veor q2, q2, q10 *)
  0xf3022150; (* veor q1, q1, q0 *)
  0xf3022154; (* veor q1, q1, q2 *)
  0xf3011112; (* veor d1, d1, d2 *)
  0xf3044113; (* veor d4, d4, d3 *)
  0xf2f925d0; (* vshl.i64 q9, q0, #0x39 *)
  0xf2fe45d0; (* vshl.i64 q10, q0, #0x3e *)
  0xf34441f2; (* veor q10, q10, q9 *)
  0xf2ff25d0; (* vshl.i64 q9, q0, #0x3f *)
  0xf34441f2; (* veor q10, q10, q9 *)
  0xf3011134; (* veor d1, d1, d20 *)
  0xf3044135; (* veor d4, d4, d21 *)
  0xf3ff40d0; (* vshr.u64 q10, q0, #0x1 *)
  0xf3044150; (* veor q2, q2, q0 *)
  0xf3000174; (* veor q0, q0, q10 *)
  0xf3fa40f4; (* vshr.u64 q10, q10, #0x6 *)
  0xf3bf00d0; (* vshr.u64 q0, q0, #0x1 *)
  0xf3000154; (* veor q0, q0, q2 *)
  0xf3000174; (* veor q0, q0, q10 *)
  0xe2533010; (* subs r3, r3, #16 *)
  0x1affff77; (* bne 0x20 *)
  0xf3b00040; (* vrev64.8 q0, q0 *)
  0xe2400010; (* sub r0, r0, #16 *)
  0xf40017cd; (* vst1.64 {d1}, [r0]! *)
  0xf40007cf; (* vst1.64 {d0}, [r0] *)
  0xe12fff1e  (* bx lr *)
];;

let GCM_GHASH_NEON_EXEC = AARCH32_MK_EXEC_RULE gcm_ghash_neon_mc;;

(* ------------------------------------------------------------------------- *)
(* Carry-less products of shifted bytes, the pieces vmull.p8 computes.       *)
(* ------------------------------------------------------------------------- *)

let POLY_DEG_X_POW = prove
 (`!k. poly_deg bool_ring (ring_pow bool_poly (poly_var bool_ring one) k) = k`,
  REWRITE_TAC[bool_poly; GSYM POLY_CLAUSES; POLY_DEG_VAR_POW; BOOL_RING]);;

let POLY_DEG_BOOL_POLY_MUL = prove
 (`!p q. p IN ring_carrier bool_poly /\ q IN ring_carrier bool_poly
         ==> poly_deg bool_ring (ring_mul bool_poly p q) <=
             poly_deg bool_ring p + poly_deg bool_ring q`,
  REWRITE_TAC[bool_poly; POLY_RING; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_DEG_MUL_LE THEN ASM_REWRITE_TAC[]);;

let POLY_OF_WORD_SHL = prove
 (`!(w:N word) k.
     poly_deg bool_ring (poly_of_word w) + k < dimindex(:N)
     ==> poly_of_word(word_shl w k) =
         ring_mul bool_poly (poly_of_word w)
                  (ring_pow bool_poly (poly_var bool_ring one) k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k < dimindex(:N)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POLY_VAR_POW_OF_WORD] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 WORD_PMUL_POW2)] THEN
  MATCH_MP_TAC POLY_OF_WORD_PMUL_GEN THEN
  ASM_SIMP_TAC[GSYM POLY_VAR_POW_OF_WORD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_BOOL_POLY_MUL o lhand o snd) THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY; POLY_DEG_X_POW] THEN
  ASM_ARITH_TAC);;

let POLY_DEG_BYTE = prove
 (`!x:byte. poly_deg bool_ring (poly_of_word x) <= 7`,
  GEN_TAC THEN MP_TAC(ISPEC `x:byte` POLY_DEG_POLY_OF_WORD_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let RING_MUL_POW_SHUFFLE = prove
 (`!r a b v:A m n.
     a IN ring_carrier r /\ b IN ring_carrier r /\ v IN ring_carrier r
     ==> ring_mul r (ring_mul r a (ring_pow r v m))
                    (ring_mul r b (ring_pow r v n)) =
         ring_mul r (ring_mul r a b) (ring_pow r v (m + n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RING_POW_ADD] THEN
  MP_TAC(ISPECL [`r:A ring`; `v:A`; `m:num`] RING_POW) THEN
  MP_TAC(ISPECL [`r:A ring`; `v:A`; `n:num`] RING_POW) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`ring_pow r (v:A) m`,`x:A`) THEN
  SPEC_TAC(`ring_pow r (v:A) n`,`y:A`) THEN
  REPEAT STRIP_TAC THEN RING_TAC);;

let PMUL_SHL_BYTES = prove
 (`!(x:byte) (y:byte) m n.
     m <= 56 /\ n <= 56
     ==> (word_pmul (word_shl (word_zx x:int64) m)
                    (word_shl (word_zx y:int64) n):int128) =
         word_shl (word_zx (word_pmul x y:int16)) (m + n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC POLY_OF_WORD_INJ THEN
  MP_TAC(ISPEC `x:byte` POLY_DEG_BYTE) THEN
  MP_TAC(ISPEC `y:byte` POLY_DEG_BYTE) THEN
  SUBGOAL_THEN
   `poly_of_word(word_zx (x:byte):int64) = poly_of_word x /\
    poly_of_word(word_zx (y:byte):int64) = poly_of_word y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC POLY_OF_WORD_ZX THEN
    REWRITE_TAC[DIMINDEX_8; DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `poly_of_word(word_shl (word_zx (x:byte):int64) m) =
    ring_mul bool_poly (poly_of_word x)
             (ring_pow bool_poly (poly_var bool_ring one) m) /\
    poly_of_word(word_shl (word_zx (y:byte):int64) n) =
    ring_mul bool_poly (poly_of_word y)
             (ring_pow bool_poly (poly_var bool_ring one) n)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_OF_WORD_SHL o lhand o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_64] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_of_word(word_zx(word_pmul (x:byte) (y:byte):int16):int128) =
    poly_of_word(word_pmul x y:int16)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC POLY_OF_WORD_ZX THEN
    REWRITE_TAC[DIMINDEX_16; DIMINDEX_128] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_deg bool_ring (poly_of_word(word_pmul (x:byte) (y:byte):int16)) < 16`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DIMINDEX_16; POLY_DEG_POLY_OF_WORD_BOUND]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_OF_WORD_SHL o rand o snd) THEN
  ASM_REWRITE_TAC[DIMINDEX_128] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_OF_WORD_PMUL_GEN o lhand o snd) THEN
  ASM_REWRITE_TAC[DIMINDEX_128] THEN ANTS_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_BOOL_POLY_MUL o
      lhand o snd) THEN
    SIMP_TAC[RING_MUL; BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY] THEN
    MATCH_MP_TAC(ARITH_RULE
     `a <= 7 + m /\ b <= 7 + n /\ m <= 56 /\ n <= 56
      ==> c <= a + b ==> c < 128`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_BOOL_POLY_MUL o
      lhand o snd) THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VARPOW_BOOL_POLY; POLY_DEG_X_POW] THEN
    ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `poly_of_word(word_pmul (x:byte) (y:byte):int16) =
    ring_mul bool_poly (poly_of_word x) (poly_of_word y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC POLY_OF_WORD_PMUL_GEN THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_BOOL_POLY_MUL o
      lhand o snd) THEN
    REWRITE_TAC[BOOL_POLY_OF_WORD; DIMINDEX_16] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC RING_MUL_POW_SHUFFLE THEN
  REWRITE_TAC[BOOL_POLY_OF_WORD; POLY_VAR_BOOL_POLY]);;

(* A 64-bit product is the XOR of its 64 byte products, shifted into place. *)
let WORD_BYTES_64 = BITBLAST_RULE
 `!a:int64.
    a = word_xor (word_shl (word_zx (word_subword a (0,8):byte):int64) 0)
       (word_xor (word_shl (word_zx (word_subword a (8,8):byte):int64) 8)
       (word_xor (word_shl (word_zx (word_subword a (16,8):byte):int64) 16)
       (word_xor (word_shl (word_zx (word_subword a (24,8):byte):int64) 24)
       (word_xor (word_shl (word_zx (word_subword a (32,8):byte):int64) 32)
       (word_xor (word_shl (word_zx (word_subword a (40,8):byte):int64) 40)
       (word_xor (word_shl (word_zx (word_subword a (48,8):byte):int64) 48)
                 (word_shl (word_zx (word_subword a (56,8):byte):int64) 56)))))))`;;

let PMUL64_BYTES =
  let pmul_shl_conv t =
    let th = PART_MATCH (lhand o rand) PMUL_SHL_BYTES t in
    MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
  GEN_ALL
   ((LAND_CONV(REWR_CONV(SPEC `a:int64` WORD_BYTES_64)) THENC
     RAND_CONV(REWR_CONV(SPEC `b:int64` WORD_BYTES_64)) THENC
     REWRITE_CONV[WORD_PMUL_XOR] THENC
     ONCE_DEPTH_CONV pmul_shl_conv THENC NUM_REDUCE_CONV)
    `word_pmul (a:int64) (b:int64):int128`);;

(* vmull.p8 multiplies eight byte lanes at once, so the routine builds each
   64x64 product from eight of them, of one operand against byte rotations
   of the other, masked and shifted into place. Given the simulated value t
   of such a product and the product `target` it is meant to be,
   PMUL_P8_CONV proves t = target: both sides become XORs of the 64 byte
   products, which, taken as atoms, BITBLAST_RULE matches up. *)
let PMUL_P8_CONV =
  let is_atom t =
    match t with
      Comb(Comb(Const("word_pmul",ty),_),_) -> ty = `:byte->byte->int16`
    | _ -> false
  and norm = TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
             PURE_REWRITE_CONV[WORD_PMUL_ZX] in
  fun target t ->
    let a,b = dest_binop `word_pmul:int64->int64->int128` target in
    let eth = CONV_RULE (RAND_CONV norm) (ISPECL [a;b] PMUL64_BYTES)
    and tth = norm t in
    let atoms = setify (find_terms is_atom (rand(concl tth)) @
                        find_terms is_atom (rand(concl eth))) in
    let sub = map (fun a -> genvar(type_of a),a) atoms in
    let gen th = subst sub (rand(concl th)) in
    let lin = INST (map (fun (v,a) -> a,v) sub)
                   (BITBLAST_RULE(mk_eq(gen tth,gen eth))) in
    TRANS tth (TRANS lin (SYM eth));;

(* Rewrites the assumption `read c s = t` to `read c s = target`. *)
let PMUL_P8_TAC c target =
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),_)),t) when c' = c ->
        ASSUME_TAC(TRANS th (PMUL_P8_CONV target t))
    | _ -> failwith "PMUL_P8_TAC");;

(* vrev64.8 of both halves reverses the bytes of the whole register, as
   the routines hold GHASH's big-endian blocks. *)
let GHASH_REV64_BYTES = prove
 (`!b:int128. word_join (word_reversefields 8 (word_subword b (0,64):int64))
                        (word_reversefields 8 (word_subword b (64,64):int64)) =
              word_bytereverse b`,
  GEN_TAC THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; BIT_WORD_SUBWORD;
              BIT_WORD_REVERSEFIELDS; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let GHASH_BYTES128_HALVES = prove
 (`!(a:int32) s x.
     read (memory :> bytes128 a) s = x
     ==> read (memory :> bytes64 a) s = word_subword x (0,64) /\
         read (memory :> bytes64 (word_add a (word 8))) s =
         word_subword x (64,64)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[]);;
(* Renames the values of the components cs to fresh variables, so stepping
   on doesn't drag along the terms a macro left in its scratch registers. *)
let FORGET_TAC cs =
  MAP_EVERY (fun c ->
    FIRST_X_ASSUM(fun th ->
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),_)),t)
          when c' = c && not(is_var t) ->
            MP_TAC th THEN SPEC_TAC(t,genvar(type_of t)) THEN
            GEN_TAC THEN DISCH_TAC
      | _ -> failwith "FORGET_TAC")) cs;;

(* ------------------------------------------------------------------------- *)
(* Blocks in memory, as in proofs/hol-light/x86_64/aes_hw_cbc_encrypt.ml.    *)
(* ------------------------------------------------------------------------- *)

(* ghash_blocks_num f j m is the 16m bytes of the blocks f j, ...,
   f (j + m - 1) read as a little-endian number, as memory holds them one
   after another. *)
let ghash_blocks_num = define
 `(!f j. ghash_blocks_num (f:num->int128) j 0 = 0) /\
  (!f j m. ghash_blocks_num f j (SUC m) =
           val(f j) + 2 EXP 128 * ghash_blocks_num f (j + 1) m)`;;

let GHASH_ADD_MULT_EXP_EQ = prove
 (`!e x y x' y'. x < e /\ x' < e
                 ==> (x + e * y = x' + e * y' <=> x = x' /\ y = y')`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x + e * y) MOD e = (x' + e * y') MOD e /\
                (x + e * y) DIV e = (x' + e * y') DIV e` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(e = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES]);;

let GHASH_FORALL_LT_SUC = prove
 (`!P m. (!i. i < SUC m ==> P i) <=> P 0 /\ (!i. i < m ==> P(SUC i))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[LT_SUC; LT_0]]);;

let GHASH_READ_BYTES128_VAL = prove
 (`!(a:int32) s x. read (memory :> bytes128 a) s = x <=>
                   read (memory :> bytes(a,16)) s = val(x:int128)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let GHASH_READ_BLOCKS = prove
 (`!m (f:num->int128) j (a:int32) s.
        read (memory :> bytes(a,16 * m)) s = ghash_blocks_num f j m <=>
        !i. i < m ==> read (memory :> bytes128(word_add a (word(16 * i)))) s =
                      f(j + i)`,
  INDUCT_TAC THEN REWRITE_TAC[ghash_blocks_num; CONJUNCT1 LT; MULT_CLAUSES] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * m + 16 = 16 + 16 * m`; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[ARITH_RULE `8 * 16 = 128`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GHASH_ADD_MULT_EXP_EQ o lhand o snd) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `(f:num->int128) j` VAL_BOUND) THEN
    MP_TAC(ISPECL [`a:int32`; `16`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM GHASH_READ_BYTES128_VAL] THEN
  REWRITE_TAC[GHASH_FORALL_LT_SUC] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              ARITH_RULE `(j + 1) + i = SUC(j + i)`]);;

let GHASH_WORD_SUB = prove
 (`!x y. y <= x ==> word_sub (word x) (word y):int32 = word(x - y)`,
  SIMP_TAC[WORD_SUB]);;

let GHASH_LEN_STEP = prove
 (`!n i. i < n /\ 16 * n < 2 EXP 32
         ==> word_sub (word_sub (word(16 * n)) (word(16 * i))) (word 16):int32 =
             word_sub (word(16 * n)) (word(16 * (i + 1))) /\
             (val(word_sub (word_sub (word(16 * n)) (word(16 * i))) (word 16):int32) = 0 <=>
              i + 1 = n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 * (i + 1) <= 16 * n` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GHASH_WORD_SUB; ARITH_RULE `16 * (i + 1) <= 16 * n ==> 16 * i <= 16 * n`;
               ARITH_RULE `16 * (i + 1) <= 16 * n ==> 16 <= 16 * n - 16 * i`] THEN
  REWRITE_TAC[ARITH_RULE `16 * n - 16 * i - 16 = 16 * n - 16 * (i + 1)`] THEN
  SIMP_TAC[VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `16 * n - 16 * (i + 1) < 2 EXP 32` (fun th -> SIMP_TAC[MOD_LT; th])
  THEN ASM_ARITH_TAC);;
let GHASH_MAP_BYTEREVERSE = prove
 (`!l:int128 list.
     MAP word_bytereverse l =
     list_of_seq (\j. word_bytereverse (EL j l)) (LENGTH l)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF]);;

(* Folding in block i extends the fold over blocks 0, ..., i - 1. *)
let GHASH_ACC_STEP = prove
 (`!ht acc (f:num->int128) i.
     ghash_polyval_acc ht acc (list_of_seq f (i + 1)) =
     polyval_dot (word_xor (ghash_polyval_acc ht acc (list_of_seq f i)) (f i)) ht`,
  REWRITE_TAC[GSYM ADD1; list_of_seq; GHASH_ACC_APPEND; ghash_polyval_acc]);;

(* The loop's state at its head, pc + 0x20, after i blocks, and at its
   SUBS and BNE, pc + 0x23c, after i + 1: Xi and the blocks are big-endian
   numbers, so the fold is s2n-bignum's POLYVAL form of GHASH over their
   byte reversals, with the twisted key ht. *)
let GHASH_NEON_INV = `\i s.
  (read R0 s = word_add xi (word 16) /\ read R1 s = htable /\
   read R2 s = word_add inp (word(16 * i)) /\
   read R3 s = word_sub (word(16 * n)) (word(16 * i)) /\
   read Q13 s = ht /\
   read Q14 s = word_join (word 0xffffffffffff:int64)
                  (word_xor (word_subword ht (0,64)) (word_subword ht (64,64)):int64) /\
   read Q15 s = word_join (word 0xffff:int64) (word 0xffffffff:int64) /\
   read (memory :> bytes(inp,16 * n)) s = ghash_blocks_num (\i. EL i blocks) 0 n /\
   read Q0 s = ghash_polyval_acc ht (word_bytereverse x)
                 (list_of_seq (\j. word_bytereverse (EL j blocks)) i)) /\
  (read ZF s <=> i = n)`;;

(* Xi, its 16 bytes, is x, and the n blocks at inp are blocks; the routine
   leaves in Xi SP 800-38D's GHASH under h, the key gcm_init_neon twisted,
   of the blocks from Xi, every value read in the byte order of a block.
   rind calls it with at least one block. *)
let GCM_GHASH_NEON_CORRECT = prove
 (`!xi htable inp n x h blocks pc.
     0 < n /\ 16 * n < 2 EXP 32 /\ LENGTH blocks = n /\
     aligned 16 htable /\ aarch32_nowrap htable 16 /\
     aarch32_nowrap xi 16 /\ aarch32_nowrap inp (16 * n) /\
     nonoverlapping (word pc,0x254) (xi,16)
     ==> ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) gcm_ghash_neon_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi; htable; inp; word(16 * n)] s /\
               read (memory :> bytes128 xi) s = x /\
               read (memory :> bytes128 htable) s = ghash_twist h /\
               (!i. i < n
                    ==> read (memory :> bytes128 (word_add inp (word(16 * i)))) s =
                        EL i blocks))
          (\s. read PC s = word (pc + 0x250) /\
               read (memory :> bytes128 xi) s =
               word_bytereverse
                (nist_ghash h (word_bytereverse x) (MAP word_bytereverse blocks)))
          (MAYCHANGE [PC; R0; R2; R3] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q8; Q9; Q10; Q11; Q13; Q14; Q15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes128 xi] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; fst GCM_GHASH_NEON_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. (!i. i < n
             ==> read (memory :> bytes128 (word_add inp (word(16 * i)))) s =
                 EL i blocks) <=>
        read (memory :> bytes(inp,16 * n)) s =
        ghash_blocks_num (\i. EL i blocks) 0 n`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GHASH_READ_BLOCKS; ADD_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  ABBREV_TAC `ht = ghash_twist h` THEN
  ENSURES_WHILE_PUP_TAC `n:num` `pc + 0x20` `pc + 0x23c` GHASH_NEON_INV THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* There is a block. *)
    ASM_ARITH_TAC;

    (* Into the loop: Xi, big-endian, and the key and its masks. *)
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; list_of_seq; ghash_polyval_acc;
                WORD_SUB_0] THEN
    MAP_EVERY (fun (v,c) -> GHOST_INTRO_TAC v c)
     [`q0:int128`,`read Q0`; `q13:int128`,`read Q13`;
      `q14:int128`,`read Q14`; `q15:int128`,`read Q15`] THEN
    ENSURES_INIT_TAC "s0" THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GHASH_BYTES128_HALVES)) THEN
    AARCH32_STEPS_TAC GCM_GHASH_NEON_EXEC (1--8) THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV
      (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GHASH_REV64_BYTES; AARCH32_JOIN_HALVES]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (* Block i: y is Xi XOR the block, and the three Karatsuba products of
       its halves and the key's, each from vmull.p8, are plo, pmid, and phh.
       Renaming each product, and forgetting the scratch registers after
       it, keeps the terms the next steps carry small. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GHASH_ACC_STEP] THEN
    ABBREV_TAC `a = ghash_polyval_acc ht (word_bytereverse x)
                      (list_of_seq (\j. word_bytereverse (EL j blocks)) i)` THEN
    ABBREV_TAC `b:int128 = EL i blocks` THEN
    SUBGOAL_THEN
     `word_xor a (word_bytereverse b) = word_xor (word_bytereverse b) (a:int128)`
    SUBST1_TAC THENL [REWRITE_TAC[WORD_XOR_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `word_add inp (word(16 * (i + 1))):int32 =
                  word_add (word_add inp (word(16 * i))) (word 16)`
    SUBST1_TAC THENL
     [REWRITE_TAC[LEFT_ADD_DISTRIB; WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `i:num`] GHASH_LEN_STEP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1 th)] THEN
                         ASSUME_TAC(CONJUNCT2 th)) THEN
    SUBGOAL_THEN `aarch32_nowrap (word_add inp (word(16 * i)):int32) 16`
    ASSUME_TAC THENL
     [MATCH_MP_TAC AARCH32_NOWRAP_OFFSET THEN EXISTS_TAC `16 * n` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `blk = word_add inp (word(16 * i)):int32` THEN
    MAP_EVERY (fun (v,c) -> GHOST_INTRO_TAC v c)
     [`q1:int128`,`read Q1`; `q2:int128`,`read Q2`; `q3:int128`,`read Q3`;
      `q8:int128`,`read Q8`; `q9:int128`,`read Q9`; `q10:int128`,`read Q10`;
      `q11:int128`,`read Q11`] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[GHASH_READ_BLOCKS] o
      check (can (term_match [] `read (memory :> bytes(a,l)) s =
                                 ghash_blocks_num f j m`) o concl)) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP GHASH_BYTES128_HALVES) THEN
    AARCH32_STEPS_TAC GCM_GHASH_NEON_EXEC (1--4) THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV
      (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GHASH_REV64_BYTES]) THEN
    ABBREV_TAC `y = word_xor (word_bytereverse b) (a:int128)` THEN
    AARCH32_STEPS_TAC GCM_GHASH_NEON_EXEC (5--41) THEN
    PMUL_P8_TAC `Q0`
     `word_pmul (word_subword (ht:int128) (0,64):int64)
                (word_subword (y:int128) (0,64):int64):int128` THEN
    ABBREV_TAC `plo = word_pmul (word_subword (ht:int128) (0,64):int64)
                                (word_subword (y:int128) (0,64):int64):int128` THEN
    FORGET_TAC [`Q8`; `Q9`; `Q10`; `Q11`] THEN
    AARCH32_STEPS_TAC GCM_GHASH_NEON_EXEC [42] THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV
      (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))) THEN
    ABBREV_TAC `ymid = word_xor (word_subword y (0,64))
                                (word_subword (y:int128) (64,64)):int64` THEN
    AARCH32_STEPS_TAC GCM_GHASH_NEON_EXEC (43--79) THEN
    PMUL_P8_TAC `Q1`
     `word_pmul (word_xor (word_subword (ht:int128) (0,64))
                          (word_subword ht (64,64)):int64)
                (ymid:int64):int128` THEN
    ABBREV_TAC `pmid = word_pmul (word_xor (word_subword (ht:int128) (0,64))
                                           (word_subword ht (64,64)):int64)
                                 (ymid:int64):int128` THEN
    FORGET_TAC [`Q8`; `Q9`; `Q10`; `Q11`] THEN
    AARCH32_STEPS_TAC GCM_GHASH_NEON_EXEC (80--116) THEN
    PMUL_P8_TAC `Q2`
     `word_pmul (word_subword (ht:int128) (64,64):int64)
                (word_subword (y:int128) (64,64):int64):int128` THEN
    ABBREV_TAC `phh = word_pmul (word_subword (ht:int128) (64,64):int64)
                                (word_subword (y:int128) (64,64):int64):int128` THEN
    FORGET_TAC [`Q8`; `Q9`; `Q10`; `Q11`] THEN
    AARCH32_STEPS_TAC GCM_GHASH_NEON_EXEC (117--135) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* The code's Karatsuba tidy-up and shift reduction compute Gueron's
       Proposition 3 reduction of the product, as a linear map of the three
       products. *)
    REWRITE_TAC[polyval_dot] THEN ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN
    REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL PMUL_KARATSUBA)] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[polyval_reduce_prop3] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[PMUL_W_64_128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN BITBLAST_TAC;

    (* Back to the head while blocks remain. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `read ZF (s0:aarch32state) <=> (i:num) = n` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    AARCH32_STEPS_TAC GCM_GHASH_NEON_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (* Out: Xi, back in the byte order of a block. *)
    REWRITE_TAC[GHASH_MAP_BYTEREVERSE] THEN ASM_REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN
    AARCH32_STEPS_TAC GCM_GHASH_NEON_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[GHASH_REV64_BYTES]]);;

let GCM_GHASH_NEON_SUBROUTINE_CORRECT = prove
 (`!xi htable inp n x h blocks pc returnaddress.
     0 < n /\ 16 * n < 2 EXP 32 /\ LENGTH blocks = n /\
     aligned 16 htable /\ aarch32_nowrap htable 16 /\
     aarch32_nowrap xi 16 /\ aarch32_nowrap inp (16 * n) /\
     nonoverlapping (word pc,0x254) (xi,16) /\
     aarch32_bx_target returnaddress
     ==> ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) gcm_ghash_neon_mc /\
               read PC s = word pc /\
               read LR s = returnaddress /\
               C_ARGUMENTS [xi; htable; inp; word(16 * n)] s /\
               read (memory :> bytes128 xi) s = x /\
               read (memory :> bytes128 htable) s = ghash_twist h /\
               (!i. i < n
                    ==> read (memory :> bytes128 (word_add inp (word(16 * i)))) s =
                        EL i blocks))
          (\s. read PC s = returnaddress /\
               read (memory :> bytes128 xi) s =
               word_bytereverse
                (nist_ghash h (word_bytereverse x) (MAP word_bytereverse blocks)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes128 xi])`,
  REWRITE_TAC[fst GCM_GHASH_NEON_EXEC] THEN
  AARCH32_ADD_RETURN_NOSTACK_TAC GCM_GHASH_NEON_EXEC
    (REWRITE_RULE[fst GCM_GHASH_NEON_EXEC] GCM_GHASH_NEON_CORRECT));;
