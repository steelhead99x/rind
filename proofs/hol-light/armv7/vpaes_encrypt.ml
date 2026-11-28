(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* aws-lc's vpaes_encrypt, as rind's build emits it.                         *)
(* ========================================================================= *)

(* The A32 routine `vpaes_encrypt` in rind's low::arm::vpaes_armv7, which
   armv7 runs for an AES block without the crypto extension: Mike Hamburg's
   vector-permutation AES, every S-box lookup a VTBL on a nibble. Its
   theorems hold for a caller in A32 or T32, so they cover every armv7
   target.

   The proof has two halves. The first, on 128-bit words alone, shows that
   vpaes's rounds compute FIPS 197's on a transformed state: each byte
   through a GF(2)-linear map T and the bytes permuted as ShiftRows has
   left them, so that a round's S-box outputs, read from vpaes's tables at
   the nibble indices io and jo, are T of the S-box's and its double's, and
   MixColumns is three byte rotations. The second steps the code, keeping
   each VTBL lane folded until its index is a numeral and naming each
   round's intermediate values, and shows it computes those rounds. *)

needs "aarch32/proofs/base.ml";;
needs "common/fips197.ml";;

(* admin/prove writes the code's bytes, from _vpaes_consts through the end
   of vpaes_encrypt, as rind's release build for armv7-unknown-linux-gnueabihf
   emits them, to armv7/vpaes_encrypt.bin, with each bl to _vpaes_preheat and
   _vpaes_encrypt_core resolved as the linker does, and the definition fails
   unless they are these: the tables at 0, _vpaes_preheat at 0x1b0,
   _vpaes_encrypt_core at 0x1d0, and vpaes_encrypt at 0x300. The tables' 128-byte
   alignment is the code's: it clears bit 6 of an address to wrap the
   rotations' index. *)
let vpaes_encrypt_mc = define_assert_word_list "vpaes_encrypt_mc"
  (term_of_bytes (load_file "armv7/vpaes_encrypt.bin"))
[
  0x00030201; (* mc_forward *)
  0x04070605; (* data *)
  0x080b0a09; (* data *)
  0x0c0f0e0d; (* data *)
  0x04070605; (* data *)
  0x080b0a09; (* data *)
  0x0c0f0e0d; (* data *)
  0x00030201; (* data *)
  0x080b0a09; (* data *)
  0x0c0f0e0d; (* data *)
  0x00030201; (* data *)
  0x04070605; (* data *)
  0x0c0f0e0d; (* data *)
  0x00030201; (* data *)
  0x04070605; (* data *)
  0x080b0a09; (* data *)
  0x02010003; (* mc_backward *)
  0x06050407; (* data *)
  0x0a09080b; (* data *)
  0x0e0d0c0f; (* data *)
  0x0e0d0c0f; (* data *)
  0x02010003; (* data *)
  0x06050407; (* data *)
  0x0a09080b; (* data *)
  0x0a09080b; (* data *)
  0x0e0d0c0f; (* data *)
  0x02010003; (* data *)
  0x06050407; (* data *)
  0x06050407; (* data *)
  0x0a09080b; (* data *)
  0x0e0d0c0f; (* data *)
  0x02010003; (* data *)
  0x03020100; (* sr *)
  0x07060504; (* data *)
  0x0b0a0908; (* data *)
  0x0f0e0d0c; (* data *)
  0x0f0a0500; (* data *)
  0x030e0904; (* data *)
  0x07020d08; (* data *)
  0x0b06010c; (* data *)
  0x0b020900; (* data *)
  0x0f060d04; (* data *)
  0x030a0108; (* data *)
  0x070e050c; (* data *)
  0x070a0d00; (* data *)
  0x0b0e0104; (* data *)
  0x0f020508; (* data *)
  0x0306090c; (* data *)
  0x0d080180; (* inv, inva *)
  0x0e05060f; (* data *)
  0x0a0b0c02; (* data *)
  0x04070309; (* data *)
  0x0f0b0780; (* data *)
  0x01040a06; (* data *)
  0x02050809; (* data *)
  0x030d0e0c; (* data *)
  0x5a2a7000; (* ipt *)
  0xc2b2e898; (* data *)
  0x52227808; (* data *)
  0xcabae090; (* data *)
  0x317c4d00; (* data *)
  0x4c01307d; (* data *)
  0xb0fdcc81; (* data *)
  0xcd80b1fc; (* data *)
  0x6fbdc700; (* sbo *)
  0xd0d26d17; (* data *)
  0xc502a878; (* data *)
  0x15aabf7a; (* data *)
  0x5fbb6a00; (* data *)
  0xcfe474a5; (* data *)
  0x412b35fa; (* data *)
  0x8e1e90d1; (* data *)
  0xfae22300; (* sb1 *)
  0x3618d415; (* data *)
  0x0d2ed9ef; (* data *)
  0x3bf7ccc1; (* data *)
  0xcb503e00; (* data *)
  0xb19be18f; (* data *)
  0x142af544; (* data *)
  0xa5df7a6e; (* data *)
  0x0ae12900; (* sb2 *)
  0x69eb8840; (* data *)
  0xab82234a; (* data *)
  0xc2a163c8; (* data *)
  0x0b712400; (* data *)
  0xe27a93c6; (* data *)
  0xbc982fcd; (* data *)
  0x5eb7e955; (* data *)
  0x74636556; (* the credit string *)
  0x5020726f; (* data *)
  0x756d7265; (* data *)
  0x69746174; (* data *)
  0x41206e6f; (* data *)
  0x66205345; (* data *)
  0x4120726f; (* data *)
  0x37764d52; (* data *)
  0x4f454e20; (* data *)
  0x4d202c4e; (* data *)
  0x20656b69; (* data *)
  0x626d6148; (* data *)
  0x20677275; (* data *)
  0x61745328; (* data *)
  0x726f666e; (* data *)
  0x6e552064; (* data *)
  0x72657669; (* data *)
  0x79746973; (* data *)
  0x00000029; (* data *)
  0xe320f000; (* nop *)
  0xe24fa0f8; (* sub r10, pc, #248 *)
  0xf2c02e5f; (* vmov.i8 q9, #0xf *)
  0xf46a42cd; (* vld1.64 {d20, d21, d22, d23}, [r10]! *)
  0xe28aa040; (* add r10, r10, #64 *)
  0xf46a82cd; (* vld1.64 {d24, d25, d26, d27}, [r10]! *)
  0xf46ac2cf; (* vld1.64 {d28, d29, d30, d31}, [r10] *)
  0xe12fff1e; (* bx lr *)
  0xe320f000; (* nop *)
  0xe1a09002; (* mov r9, r2 *)
  0xe59280f0; (* ldr r8, [r2, #0xf0] *)
  0xe24fbc01; (* sub r11, pc, #256 *)
  0xf42b42cf; (* vld1.64 {d4, d5, d6, d7}, [r11] *)
  0xe24fbf76; (* sub r11, pc, #472 *)
  0xf429aacd; (* vld1.64 {d10, d11}, [r9]! *)
  0xf2002172; (* vand q1, q0, q9 *)
  0xf38c0050; (* vshr.u8 q0, q0, #0x4 *)
  0xf3b42902; (* vtbl.8 d2, {d4, d5}, d2 *)
  0xf3b43903; (* vtbl.8 d3, {d4, d5}, d3 *)
  0xf3b64900; (* vtbl.8 d4, {d6, d7}, d0 *)
  0xf3b65901; (* vtbl.8 d5, {d6, d7}, d1 *)
  0xf302015a; (* veor q0, q1, q5 *)
  0xf3000154; (* veor q0, q0, q2 *)
  0xe1180008; (* tst r8, r8 *)
  0xea000018; (* b 0x274 *)
  0xe28ba040; (* add r10, r11, #64 *)
  0xf3ba8984; (* vtbl.8 d8, {d26, d27}, d4 *)
  0xf3ba9985; (* vtbl.8 d9, {d26, d27}, d5 *)
  0xf42b2acd; (* vld1.64 {d2, d3}, [r11]! *)
  0xf3b80986; (* vtbl.8 d0, {d24, d25}, d6 *)
  0xf3b81987; (* vtbl.8 d1, {d24, d25}, d7 *)
  0xf308815a; (* veor q4, q4, q5 *)
  0xf3bea984; (* vtbl.8 d10, {d30, d31}, d4 *)
  0xf3beb985; (* vtbl.8 d11, {d30, d31}, d5 *)
  0xf3000158; (* veor q0, q0, q4 *)
  0xf3bc4986; (* vtbl.8 d4, {d28, d29}, d6 *)
  0xf3bc5987; (* vtbl.8 d5, {d28, d29}, d7 *)
  0xf42a8acf; (* vld1.64 {d8, d9}, [r10] *)
  0xf3b06902; (* vtbl.8 d6, {d0, d1}, d2 *)
  0xf3b07903; (* vtbl.8 d7, {d0, d1}, d3 *)
  0xf304415a; (* veor q2, q2, q5 *)
  0xf3b0a908; (* vtbl.8 d10, {d0, d1}, d8 *)
  0xf3b0b909; (* vtbl.8 d11, {d0, d1}, d9 *)
  0xf3066154; (* veor q3, q3, q2 *)
  0xf3b68902; (* vtbl.8 d8, {d6, d7}, d2 *)
  0xf3b69903; (* vtbl.8 d9, {d6, d7}, d3 *)
  0xf30a0156; (* veor q0, q5, q3 *)
  0xe3cbb040; (* bic r11, r11, #64 *)
  0xf3000158; (* veor q0, q0, q4 *)
  0xe2588001; (* subs r8, r8, #1 *)
  0xf2002172; (* vand q1, q0, q9 *)
  0xf38c0050; (* vshr.u8 q0, q0, #0x4 *)
  0xf3b6a982; (* vtbl.8 d10, {d22, d23}, d2 *)
  0xf3b6b983; (* vtbl.8 d11, {d22, d23}, d3 *)
  0xf3022150; (* veor q1, q1, q0 *)
  0xf3b46980; (* vtbl.8 d6, {d20, d21}, d0 *)
  0xf3b47981; (* vtbl.8 d7, {d20, d21}, d1 *)
  0xf3b48982; (* vtbl.8 d8, {d20, d21}, d2 *)
  0xf3b49983; (* vtbl.8 d9, {d20, d21}, d3 *)
  0xf306615a; (* veor q3, q3, q5 *)
  0xf308815a; (* veor q4, q4, q5 *)
  0xf3b44986; (* vtbl.8 d4, {d20, d21}, d6 *)
  0xf3b45987; (* vtbl.8 d5, {d20, d21}, d7 *)
  0xf3b46988; (* vtbl.8 d6, {d20, d21}, d8 *)
  0xf3b47989; (* vtbl.8 d7, {d20, d21}, d9 *)
  0xf3044152; (* veor q2, q2, q1 *)
  0xf3066150; (* veor q3, q3, q0 *)
  0xf429aacd; (* vld1.64 {d10, d11}, [r9]! *)
  0x1affffd3; (* bne 0x210 *)
  0xe28ba080; (* add r10, r11, #128 *)
  0xe24fbf73; (* sub r11, pc, #460 *)
  0xf42b2acd; (* vld1.64 {d2, d3}, [r11]! *)
  0xf42b0acf; (* vld1.64 {d0, d1}, [r11] *)
  0xf3b28904; (* vtbl.8 d8, {d2, d3}, d4 *)
  0xf3b29905; (* vtbl.8 d9, {d2, d3}, d5 *)
  0xf42a2acf; (* vld1.64 {d2, d3}, [r10] *)
  0xf3b04906; (* vtbl.8 d4, {d0, d1}, d6 *)
  0xf3b05907; (* vtbl.8 d5, {d0, d1}, d7 *)
  0xf308815a; (* veor q4, q4, q5 *)
  0xf3044158; (* veor q2, q2, q4 *)
  0xf3b40902; (* vtbl.8 d0, {d4, d5}, d2 *)
  0xf3b41903; (* vtbl.8 d1, {d4, d5}, d3 *)
  0xe12fff1e; (* bx lr *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe92d4f80; (* push {r7, r8, r9, r10, r11, lr} *)
  0xed2d8b08; (* vpush {d8, d9, d10, d11} *)
  0xf4200acf; (* vld1.64 {d0, d1}, [r0] *)
  0xebffffa7; (* bl 0x1b0 *)
  0xebffffae; (* bl 0x1d0 *)
  0xf4010acf; (* vst1.64 {d0, d1}, [r1] *)
  0xecbd8b08; (* vpop {d8, d9, d10, d11} *)
  0xe8bd8f80  (* pop {r7, r8, r9, r10, r11, pc} *)
];;

let VPAES_ENCRYPT_EXEC = AARCH32_MK_EXEC_RULE vpaes_encrypt_mc;;

(* admin/prove writes vpaes_encrypt's offset from _vpaes_consts in rind's
   build to armv7/vpaes_encrypt.offset, and this fails unless it is 0x300,
   the entry the theorems take, so the symbol rind calls is the code they
   are about. *)
let () =
  let offset =
    int_of_string (String.trim (Bytes.to_string
                                 (load_file "armv7/vpaes_encrypt.offset"))) in
  if offset <> 0x300 then
    failwith ("vpaes_encrypt: vpaes_encrypt is at " ^
              string_of_int offset ^ ", not 0x300");;

(* ------------------------------------------------------------------------- *)
(* Reading the code's tables.                                                *)
(* ------------------------------------------------------------------------- *)

let VPAES_LOADED_BYTES64 = prove
 (`!(s:aarch32state) (a:int32) b0 b1 b2 b3 b4 b5 b6 b7.
     bytes_loaded s a [b0;b1;b2;b3;b4;b5;b6;b7]
     ==> read (memory :> bytes64 a) s =
         word(num_of_bytelist [b0;b1;b2;b3;b4;b5;b6;b7])`,
  REWRITE_TAC[bytes_loaded; READ_COMPONENT_COMPOSE; bytelist; through; read] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bytes64; asword; READ_COMPONENT_COMPOSE; through; read] THEN
  MESON_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; BYTELIST_OF_NUM_OF_BYTELIST;
            READ_BYTES_BOUND_ALT; LENGTH_BYTELIST_OF_NUM; LENGTH_CONV `LENGTH [b0;b1;b2;b3;b4;b5;b6;b7:byte]`]);;

(* VPAES_READ_RULE off: the doubleword the code holds at pc + off. *)
let VPAES_READ_RULE off =
  let th = SPECL [`s:aarch32state`; `word pc:int32`; `vpaes_encrypt_mc`;
                  mk_small_numeral off; `8`]
             aligned_bytes_loaded_sub_list in
  let th = CONV_RULE (LAND_CONV (RAND_CONV DIVIDES_CONV) THENC
             RAND_CONV (RAND_CONV (REWRITE_CONV[vpaes_encrypt_mc] THENC SUB_LIST_CONV) THENC
                        REWR_CONV aligned_bytes_loaded)) th in
  let th = MATCH_MP VPAES_LOADED_BYTES64 (CONJUNCT2 (UNDISCH (REWRITE_RULE[] th))) in
  let th = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV[num_of_bytelist] THENC
                                            DEPTH_CONV WORD_NUM_RED_CONV THENC
                                            NUM_REDUCE_CONV))) th in
  let th = REWRITE_RULE[GSYM WORD_ADD; ADD_CLAUSES] th in
  GEN_ALL (DISCH_ALL th);;

(* The doublewords the code holds from 0 to 0x1a8, at the addresses a load
   computes, pc + n or, for a load's second doubleword, its base plus 8. *)
let VPAES_CONSTS =
  let offs = map (fun k -> 8 * k) (0--52) in
  let ths = map (fun off -> SPEC_ALL (VPAES_READ_RULE off)) offs in
  let concls = map (fun th -> rand(concl th)) ths in
  let alt = mapfilter (fun t ->
      let a = rand(rand(lhand(lhand t))) in
      let n = try dest_small_numeral(rand(rand a)) with _ -> 0 in
      if n mod 16 = 8 then
        let a' = mk_comb(mk_comb(`word_add:int32->int32->int32`,
                    if n = 8 then `word pc:int32` else
                    mk_comb(`word:num->int32`, mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral (n - 8)))),
                    `word 8:int32`) in
        subst [a', a] t
      else failwith "") concls in
  let goal = mk_imp(`aligned_bytes_loaded s (word pc) vpaes_encrypt_mc`,
                    list_mk_conj(concls @ alt)) in
  prove(goal,
        DISCH_TAC THEN
        REWRITE_TAC[WORD_RULE `word_add (word (pc + n)) (word 8):int32 = word(pc + n + 8)`;
                    WORD_RULE `word_add (word pc) (word 8):int32 = word(pc + 8)`] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
        REPEAT CONJ_TAC THEN
        FIRST(map (fun th -> MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC) ths));;

(* The constants a four-register VLD1 reads past its first two doublewords,
   at the addresses the step computes from its base. *)
let VPAES_CONSTS_X =
  let pairs = allpairs (fun b d -> (b,d)) [192; 224; 288; 320] [16; 24] in
  let base = UNDISCH VPAES_CONSTS in
  let facts = CONJUNCTS base in
  let addr_of th = try rand(rand(rand(rator(lhand(concl th))))) with Failure _ -> `T` in
  let find_fact n =
    let a = mk_comb(`word:num->int32`, mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral n)) in
    find (fun th -> addr_of th = a) facts in
  let ths = map (fun (b,d) ->
    let th = find_fact (b + d) in
    let a' = mk_binop `word_add:int32->int32->int32`
               (mk_comb(`word:num->int32`, mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral b)))
               (mk_comb(`word:num->int32`, mk_small_numeral d)) in
    let eq = (REWRITE_CONV[GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
              ONCE_DEPTH_CONV NUM_ADD_CONV) a' in
    let c = subst [a', addr_of th] (concl th) in
    EQ_MP (SYM (REWRITE_CONV[eq] c)) (EQT_ELIM (REWRITE_CONV[th] (rhs(concl(REWRITE_CONV[eq] c)))))) pairs in
  DISCH_ALL (end_itlist CONJ ths);;

(* Adds the code's doublewords for the current state. *)
let VP_CONSTS_TAC =
  FIRST_ASSUM(fun th ->
    if fst(strip_comb(concl th)) = `aligned_bytes_loaded:aarch32state->int32->byte list->bool`
    then STRIP_ASSUME_TAC(MATCH_MP VPAES_CONSTS th) THEN
         STRIP_ASSUME_TAC(MATCH_MP VPAES_CONSTS_X th) else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Addresses and steps.                                                      *)
(* ------------------------------------------------------------------------- *)

let VP_WORD_SHL_128 = prove
 (`!m. word(128 * m):int32 = word_shl (word m) 7`,
  REWRITE_TAC[WORD_SHL_WORD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Normalizes an address the code computes from pc to word (pc + n), and
   the bic that wraps the rotations' index, given 128 divides pc. *)
let VP_ADDR_CONV =
  let pth0 = prove(`word_add (word pc) (word b):int32 = word(pc + b)`, REWRITE_TAC[WORD_ADD])
  and pthz = prove(`word(pc + 0):int32 = word pc`, REWRITE_TAC[ADD_CLAUSES])
  and pth_add = prove
   (`word_add (word (pc + a)) (word b):int32 = word(pc + (a + b))`,
    REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC])
  and pth_sub = prove
   (`b <= a ==> word_sub (word (pc + a)) (word b):int32 = word(pc + (a - b))`,
    STRIP_TAC THEN ASM_SIMP_TAC[GSYM ADD_SUB; WORD_SUB; LE_ADD; ADD_SUB2; GSYM ADD_SUB;
      ARITH_RULE `b <= a ==> pc + a - b = (pc + a) - b`; ARITH_RULE `b <= a ==> b <= pc + a`]) in
  let add_conv =
    GEN_REWRITE_CONV I [pth_add] THENC RAND_CONV(RAND_CONV NUM_ADD_CONV)
  and sub_conv tm =
    let th = PART_MATCH (lhand o rand) pth_sub tm in
    let th' = MP th (EQT_ELIM(NUM_LE_CONV(lhand(concl th)))) in
    CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV NUM_SUB_CONV))) th'
  and bic_conv tm =
    match tm with
      Comb(Comb(Const("word_and",_),Comb(Const("word",_),
           Comb(Comb(Const("+",_),p),c))),
           Comb(Const("word",_),msk))
      when is_numeral c && dest_numeral msk = num 4294967231 ->
        let n = dest_small_numeral c in
        if n >= 128 then failwith "bic_conv" else
        let n' = if n >= 64 then n - 64 else n in
        let rhs = mk_comb(`word:num->int32`, mk_binop `(+):num->num->num` p (mk_small_numeral n')) in
        let goal = mk_imp(mk_comb(mk_comb(`(divides):num->num->bool`, `128`), p), mk_eq(tm, rhs)) in
        UNDISCH(prove(goal,
          REWRITE_TAC[divides] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[WORD_ADD; WORD_ADD_0; VP_WORD_SHL_128] THEN
          SPEC_TAC(`word x:int32`,`y:int32`) THEN GEN_TAC THEN
          W(fun (_,w) -> let l = lhand(lhand w) in
             if is_comb l && is_comb(rator l) && fst(dest_const(rator(rator l))) = "word_add"
             then MP_TAC(PART_MATCH (lhand o rand) WORD_ADD_OR l)
             else ALL_TAC) THEN
          TRY(ANTS_TAC THENL [BITBLAST_TAC; DISCH_THEN SUBST1_TAC]) THEN
          TRY(W(fun (_,w) -> let r = rand w in
             if is_comb r && is_comb(rator r) && fst(dest_const(rator(rator r))) = "word_add"
             then MP_TAC(PART_MATCH (lhand o rand) WORD_ADD_OR r) THEN
                  ANTS_TAC THENL [BITBLAST_TAC; DISCH_THEN SUBST1_TAC]
             else ALL_TAC)) THEN
          BITBLAST_TAC))
    | _ -> failwith "bic_conv" in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_add",_),Comb(Const("word",_),Var(_,_))),
           Comb(Const("word",_),b)) when is_numeral b -> REWR_CONV pth0 tm
    | Comb(Const("word",_),Comb(Comb(Const("+",_),Var(_,_)),z))
           when is_numeral z && dest_small_numeral z = 0 -> REWR_CONV pthz tm
    | Comb(Comb(Const("word_add",_),Comb(Const("word",_),Comb(Comb(Const("+",_),_),a))),
           Comb(Const("word",_),b)) when is_numeral a && is_numeral b -> add_conv tm
    | Comb(Comb(Const("word_sub",_),Comb(Const("word",_),Comb(Comb(Const("+",_),_),a))),
           Comb(Const("word",_),b)) when is_numeral a && is_numeral b -> sub_conv tm
    | _ -> bic_conv tm;;

(* After each step: R registers' addresses as `word (pc + n)`, and Q
   registers' lanes with subwords of joins taken. *)
let VP_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if not (is_eq c) then th else
    let l = lhand c in
    match l with
      Comb(Comb(Const("read",_),Const(r,_)),Var(_,_)) when String.length r > 0 && (r.[0] = 'R' || r = "LR") ->
        CONV_RULE (RAND_CONV (TOP_DEPTH_CONV VP_ADDR_CONV)) th
    | Comb(Comb(Const("read",_),Const(r,_)),Var(_,_)) when String.length r > 0 && r.[0] = 'Q' ->
        CONV_RULE (RAND_CONV (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) (REWRITE_RULE[AARCH32_JOIN_HALVES] th)
    | _ -> th);;
(* Steps the instructions l, each with the code's doublewords at hand. *)
let VP_STEPS_TAC l = MAP_EVERY (fun n -> VP_CONSTS_TAC THEN AARCH32_STEPS_TAC VPAES_ENCRYPT_EXEC [n] THEN VP_NORM_TAC) l;;

(* A block's two doublewords, as VLD1 reads them. *)
let VPAES_BYTES128_HALVES = prove
 (`!(a:int32) s x.
     read (memory :> bytes128 a) s = x
     ==> read (memory :> bytes64 a) s = word_subword x (0,64) /\
         read (memory :> bytes64 (word_add a (word 8))) s =
         word_subword x (64,64)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* vpaes's operations.                                                       *)
(* ------------------------------------------------------------------------- *)

(* VTBL with a one-Q-register table t on each byte of x: t's byte at that
   index, or zero for an index of 16 or more. *)
let vpaes_tbl = new_definition
 `vpaes_tbl (t:int128) (x:int128) : int128 =
    usimd16 (aarch32_tbl 2 (word_zx t)) x`;;

let vpaes_lo = new_definition
 `vpaes_lo (x:int128) : int128 = word_and x (word 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f)`;;

let vpaes_hi = new_definition
 `vpaes_hi (x:int128) : int128 = usimd16 (\b:byte. word_ushr b 4) x`;;

let vpaes_inv = new_definition
 `vpaes_inv:int128 = word 0x40703090a0b0c020e05060f0d080180`;;
let vpaes_inva = new_definition
 `vpaes_inva:int128 = word 0x30d0e0c0205080901040a060f0b0780`;;

(* The top of a round: the two indices, io and jo, of x's bytes in the S-box
   output tables. *)
let vpaes_io = new_definition
 `vpaes_io (x:int128) : int128 =
    let k = vpaes_lo x and i = vpaes_hi x in
    let ak = vpaes_tbl vpaes_inva k in
    word_xor (vpaes_tbl vpaes_inv (word_xor (vpaes_tbl vpaes_inv i) ak))
             (word_xor k i)`;;

let vpaes_jo = new_definition
 `vpaes_jo (x:int128) : int128 =
    let k = vpaes_lo x and i = vpaes_hi x in
    let ak = vpaes_tbl vpaes_inva k in
    word_xor (vpaes_tbl vpaes_inv (word_xor (vpaes_tbl vpaes_inv (word_xor k i)) ak)) i`;;

let vpaes_mc_forward = new_definition
 `vpaes_mc_forward r:int128 =
    EL (r MOD 4) [word 0xc0f0e0d080b0a090407060500030201;
                  word 0x302010c0f0e0d080b0a0904070605;
                  word 0x4070605000302010c0f0e0d080b0a09;
                  word 0x80b0a0904070605000302010c0f0e0d]`;;

let vpaes_mc_backward = new_definition
 `vpaes_mc_backward r:int128 =
    EL (r MOD 4) [word 0xe0d0c0f0a09080b0605040702010003;
                  word 0xa09080b06050407020100030e0d0c0f;
                  word 0x6050407020100030e0d0c0f0a09080b;
                  word 0x20100030e0d0c0f0a09080b06050407]`;;

let vpaes_sr = new_definition
 `vpaes_sr r:int128 =
    EL (r MOD 4) [word 0xf0e0d0c0b0a09080706050403020100;
                  word 0xb06010c07020d08030e09040f0a0500;
                  word 0x70e050c030a01080f060d040b020900;
                  word 0x306090c0f0205080b0e0104070a0d00]`;;

(* A middle round's S-box outputs from the indices io and jo of its input,
   with its key k, and doubled. *)
let vpaes_a = new_definition
 `vpaes_a (io:int128) (jo:int128) (k:int128) : int128 =
    word_xor (vpaes_tbl (word 0x3bf7ccc10d2ed9ef3618d415fae22300) jo)
             (word_xor (vpaes_tbl (word 0xa5df7a6e142af544b19be18fcb503e00) io) k)`;;

let vpaes_a2 = new_definition
 `vpaes_a2 (io:int128) (jo:int128) : int128 =
    word_xor (vpaes_tbl (word 0xc2a163c8ab82234a69eb88400ae12900) jo)
             (vpaes_tbl (word 0x5eb7e955bc982fcde27a93c60b712400) io)`;;

(* Middle round r: MixColumns of a and a2 by byte rotations. *)
let vpaes_mid = new_definition
 `vpaes_mid r (io:int128) (jo:int128) (k:int128) : int128 =
    let b = word_xor (vpaes_tbl (vpaes_a io jo k) (vpaes_mc_forward r)) (vpaes_a2 io jo) in
    word_xor (word_xor (vpaes_tbl (vpaes_a io jo k) (vpaes_mc_backward r)) b)
             (vpaes_tbl b (vpaes_mc_forward r))`;;

(* The last round, r, and its key k. *)
let vpaes_last = new_definition
 `vpaes_last r (io:int128) (jo:int128) (k:int128) : int128 =
    vpaes_tbl (word_xor (vpaes_tbl (word 0x8e1e90d1412b35facfe474a55fbb6a00) jo)
                        (word_xor (vpaes_tbl (word 0x15aabf7ac502a878d0d26d176fbdc700) io) k))
              (vpaes_sr r)`;;

(* The input transform and the first key. *)
let vpaes_first = new_definition
 `vpaes_first (k:int128) (x:int128) : int128 =
    word_xor (word_xor (vpaes_tbl (word 0xcabae09052227808c2b2e8985a2a7000) (vpaes_lo x)) k)
             (vpaes_tbl (word 0xcd80b1fcb0fdcc814c01307d317c4d00) (vpaes_hi x))`;;

let vpaes_rounds = define
 `vpaes_rounds 0 (ks:int128 list) (x:int128) = x /\
  vpaes_rounds (SUC i) ks x =
    vpaes_mid (SUC i) (vpaes_io (vpaes_rounds i ks x)) (vpaes_jo (vpaes_rounds i ks x))
              (EL (SUC i) ks)`;;

(* vpaes's cipher of x under its schedule ks, n middle rounds. *)
let vpaes_cipher = new_definition
 `vpaes_cipher n (ks:int128 list) (x:int128) =
    let y = vpaes_rounds n ks (vpaes_first (EL 0 ks) x) in
    vpaes_last (n + 1) (vpaes_io y) (vpaes_jo y) (EL (n + 1) ks)`;;

(* ------------------------------------------------------------------------- *)
(* Folding a register's lanes into an operation.                             *)
(* ------------------------------------------------------------------------- *)

(* Two 128-bit words are equal when their 16 bytes are. *)
let VPAES_WORD_EQ_BYTES = prove
 (`!x y:int128.
     x = y <=> !i. i < 16 ==> word_subword x (8 * i,8):byte = word_subword y (8 * i,8)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  BITBLAST_TAC);;

(* Pushes a lane's subword through xor, and, and the folded lookups. *)
let VPAES_FOLD_LANE_CONV =
  TOP_DEPTH_CONV
   (WORD_SIMPLE_SUBWORD_CONV ORELSEC
    REWR_CONV WORD_SUBWORD_XOR ORELSEC REWR_CONV WORD_SUBWORD_AND ORELSEC
    WORD_RED_CONV ORELSEC AARCH32_TBL_CONV ORELSEC BETA_CONV ORELSEC
    NUM_RED_CONV);;

(* Unfolds defs and vpaes's operations to their lanes. *)
let VPAES_SPEC_CONV defs =
  REWRITE_CONV defs THENC
  REWRITE_CONV[vpaes_tbl; vpaes_lo; vpaes_hi; vpaes_inv; vpaes_inva;
               vpaes_mc_forward; vpaes_mc_backward; vpaes_sr] THENC
  NUM_REDUCE_CONV THENC DEPTH_CONV EL_CONV THENC
  TOP_DEPTH_CONV let_CONV THENC
  AARCH32_SIMD_EXPAND_CONV;;

(* Proves x = y lane by lane, each lane's subword pushed through the
   operations to the inputs'. *)
let VPAES_LANES_TAC defs =
  CONV_TAC(BINOP_CONV (VPAES_SPEC_CONV defs)) THEN
  GEN_REWRITE_TAC I [VPAES_WORD_EQ_BYTES] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_BINOP_CONV `(/\)` (BINOP_CONV VPAES_FOLD_LANE_CONV)) THEN
  REWRITE_TAC[];;

(* Replaces register r's value, as the assumption gives it, by spec, which
   unfolding defs proves equal lane by lane. *)
let VP_FOLD_TAC (r:term) (spec:term) (defs:thm list) : tactic =
  fun (asl,w as gl) ->
    let (_,th) = find (fun (_,th) -> let c = concl th in
       is_eq c && (try rand(rator(lhand c)) = r with _ -> false) &&
       is_var(rand(lhand c))) asl in
    let eq = prove(mk_eq(rand(concl th), spec), VPAES_LANES_TAC defs) in
    let th' = TRANS th eq in
    (UNDISCH_THEN (concl th) (K ALL_TAC) THEN ASSUME_TAC th') gl;;

(* ------------------------------------------------------------------------- *)
(* Bytes.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* vpaes's byte transform T, GF(2)-linear: the low nibble's and high
   nibble's table entries. *)
let vpaes_tb = new_definition
 `vpaes_tb (b:byte) : byte =
    word_xor (aarch32_tbl 2 (word 0xcabae09052227808c2b2e8985a2a7000) (word_and b (word 15)))
             (aarch32_tbl 2 (word 0xcd80b1fcb0fdcc814c01307d317c4d00) (word_ushr b 4))`;;

(* Byte b's indices, as a round's top computes them for each byte. *)
let vpaes_iob = new_definition
 `vpaes_iob (b:byte) : byte =
    let k = word_and b (word 15) and i = word_ushr b 4 in
    let ak = aarch32_tbl 2 (word 0x30d0e0c0205080901040a060f0b0780) k in
    word_xor (aarch32_tbl 2 (word 0x40703090a0b0c020e05060f0d080180)
               (word_xor (aarch32_tbl 2 (word 0x40703090a0b0c020e05060f0d080180) i) ak))
             (word_xor k i)`;;

let vpaes_job = new_definition
 `vpaes_job (b:byte) : byte =
    let k = word_and b (word 15) and i = word_ushr b 4 in
    let ak = aarch32_tbl 2 (word 0x30d0e0c0205080901040a060f0b0780) k in
    word_xor (aarch32_tbl 2 (word 0x40703090a0b0c020e05060f0d080180)
               (word_xor (aarch32_tbl 2 (word 0x40703090a0b0c020e05060f0d080180) (word_xor k i)) ak)) i`;;

let FORALL_BYTE_CASES = prove
 (`!P. (!b:byte. P b) <=> (!n. n < 256 ==> P (word n))`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `b:byte` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `val(b:byte)`) THEN
  REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* Proves !b:byte. P b by evaluating P at each of the 256 bytes. *)
let BYTE_CASES_TAC conv =
  REWRITE_TAC[FORALL_BYTE_CASES] THEN
  CONV_TAC(EXPAND_CASES_CONV) THEN
  REPEAT CONJ_TAC THEN CONV_TAC conv;;

(* Evaluates vpaes's byte functions and the S-box and doubling on a byte. *)
let VPAES_BYTE_CONV =
  let tabs = lazy (Array.to_list (Lazy.force aes_sbox_table) @
                   Array.to_list (Lazy.force ffmul02_table) @
                   Array.to_list (Lazy.force ffmul03_table)) in
  fun tm ->
    (REWRITE_CONV[vpaes_tb; vpaes_iob; vpaes_job] THENC
     TOP_DEPTH_CONV let_CONV THENC
     TOP_DEPTH_CONV (WORD_RED_CONV ORELSEC AARCH32_TBL_CONV ORELSEC
                     NUM_RED_CONV ORELSEC GEN_REWRITE_CONV I (Lazy.force tabs)) THENC
     REWRITE_CONV[]) tm;;

let vpaes_tlin = new_definition
 `vpaes_tlin (b:byte) : byte =
    word_xor (word_and (word_ishr (word_shl b 7) 7) (word 0x70))
   (word_xor (word_and (word_ishr (word_shl b 6) 7) (word 0x2a))
   (word_xor (word_and (word_ishr (word_shl b 5) 7) (word 0x98))
   (word_xor (word_and (word_ishr (word_shl b 4) 7) (word 0x08))
   (word_xor (word_and (word_ishr (word_shl b 3) 7) (word 0x4d))
   (word_xor (word_and (word_ishr (word_shl b 2) 7) (word 0x7c))
   (word_xor (word_and (word_ishr (word_shl b 1) 7) (word 0x7d))
             (word_and (word_ishr b 7) (word 0x81))))))))`;;

(* T as the GF(2)-linear map it is. *)
let VPAES_TB_TLIN = prove
 (`!b. vpaes_tb b = vpaes_tlin b`,
  BYTE_CASES_TAC (VPAES_BYTE_CONV THENC REWRITE_CONV[vpaes_tlin] THENC WORD_REDUCE_CONV));;

let VPAES_TB_XOR = prove
 (`!a b. vpaes_tb (word_xor a b) = word_xor (vpaes_tb a) (vpaes_tb b)`,
  REWRITE_TAC[VPAES_TB_TLIN; vpaes_tlin] THEN BITBLAST_TAC);;

(* The S-box output tables, at the indices of a transformed byte: sb1's
   are T of the S-box xor 0x5b, which the key's 0x5b cancels; sb2's T of
   its double xor 0x4e; and sbo's the S-box xor 0x63, which the last key's
   0x63 cancels. *)
let VPAES_SB1_BYTE = prove
 (`!s. word_xor (aarch32_tbl 2 (word 0x3bf7ccc10d2ed9ef3618d415fae22300) (vpaes_job (vpaes_tb s)))
                (aarch32_tbl 2 (word 0xa5df7a6e142af544b19be18fcb503e00) (vpaes_iob (vpaes_tb s))) =
       word_xor (vpaes_tb (aes_sub_byte joined_GF2 s)) (word 0x5b)`,
  BYTE_CASES_TAC VPAES_BYTE_CONV);;

let VPAES_SB2_BYTE = prove
 (`!s. word_xor (aarch32_tbl 2 (word 0xc2a163c8ab82234a69eb88400ae12900) (vpaes_job (vpaes_tb s)))
                (aarch32_tbl 2 (word 0x5eb7e955bc982fcde27a93c60b712400) (vpaes_iob (vpaes_tb s))) =
       word_xor (vpaes_tb (FFmul02 (aes_sub_byte joined_GF2 s))) (word 0x4e)`,
  BYTE_CASES_TAC VPAES_BYTE_CONV);;

let VPAES_SBO_BYTE = prove
 (`!s. word_xor (aarch32_tbl 2 (word 0x8e1e90d1412b35facfe474a55fbb6a00) (vpaes_job (vpaes_tb s)))
                (aarch32_tbl 2 (word 0x15aabf7ac502a878d0d26d176fbdc700) (vpaes_iob (vpaes_tb s))) =
       word_xor (aes_sub_byte joined_GF2 s) (word 0x63)`,
  BYTE_CASES_TAC VPAES_BYTE_CONV);;

let VPAES_FFMUL03 = prove
 (`!y. FFmul03 y = word_xor (FFmul02 y) y`,
  BYTE_CASES_TAC VPAES_BYTE_CONV);;

(* As the rounds' lanes meet them, with the key's byte after. *)
let VPAES_SB1_KEY = prove
 (`!s z. word_xor (aarch32_tbl 2 (word 0x3bf7ccc10d2ed9ef3618d415fae22300) (vpaes_job (vpaes_tb s)))
          (word_xor (aarch32_tbl 2 (word 0xa5df7a6e142af544b19be18fcb503e00) (vpaes_iob (vpaes_tb s))) z) =
         word_xor (word_xor (vpaes_tb (aes_sub_byte joined_GF2 s)) (word 0x5b)) z`,
  REWRITE_TAC[GSYM VPAES_SB1_BYTE; WORD_XOR_ASSOC]);;

let VPAES_SBO_KEY = prove
 (`!s z. word_xor (aarch32_tbl 2 (word 0x8e1e90d1412b35facfe474a55fbb6a00) (vpaes_job (vpaes_tb s)))
          (word_xor (aarch32_tbl 2 (word 0x15aabf7ac502a878d0d26d176fbdc700) (vpaes_iob (vpaes_tb s))) z) =
         word_xor (word_xor (aes_sub_byte joined_GF2 s) (word 0x63)) z`,
  REWRITE_TAC[GSYM VPAES_SBO_BYTE; WORD_XOR_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The transformed state and schedule.                                       *)
(* ------------------------------------------------------------------------- *)

let vpaes_tmap = new_definition
 `vpaes_tmap (x:int128) : int128 = usimd16 vpaes_tb x`;;

(* Each column's bytes rotated by one, two, and three, summed. *)
let vpaes_mix3 = new_definition
 `vpaes_mix3 (x:int128) : int128 =
    let r1 = vpaes_tbl x (vpaes_mc_forward 0) in
    let r2 = vpaes_tbl r1 (vpaes_mc_forward 0) in
    let r3 = vpaes_tbl r2 (vpaes_mc_forward 0) in
    word_xor r1 (word_xor r2 r3)`;;

(* The state after i rounds: AES's state s, bytes transformed, and permuted
   as ShiftRows i times over leaves them in vpaes's order. *)
let vpaes_state = new_definition
 `vpaes_state i (s:int128) : int128 =
    vpaes_tbl (vpaes_tmap s) (vpaes_sr (4 - i MOD 4))`;;

let vpaes_key = new_definition
 `vpaes_key j (k:int128) : int128 =
    vpaes_tbl (word_xor (vpaes_tmap (vpaes_mix3 k))
                        (word 0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b))
              (vpaes_sr (4 - j MOD 4))`;;

let vpaes_key_last = new_definition
 `vpaes_key_last j (k:int128) : int128 =
    vpaes_tbl (word_xor k (word 0x63636363636363636363636363636363))
              (vpaes_sr j)`;;

(* The schedule vpaes reads for the FIPS 197 round keys ks, n middle
   rounds: round key 0 transformed, the middle ones mixed and transformed,
   and the last as it is, each byte-reversed to a little-endian word. *)
let vpaes_schedule = new_definition
 `vpaes_schedule n (ks:int128 list) =
    list_of_seq (\j. if j = 0 then vpaes_tmap (word_bytereverse (EL 0 ks))
                     else if j <= n then vpaes_key j (word_bytereverse (EL j ks))
                     else vpaes_key_last (n + 1) (word_bytereverse (EL j ks)))
                (n + 2)`;;

(* FIPS 197's cipher with n middle rounds, on round keys ks. *)
let aes_fips_rounds = define
 `aes_fips_rounds 0 (s:int128) (ks:int128 list) = s /\
  aes_fips_rounds (SUC i) s ks = fips197_round (aes_fips_rounds i s ks) (EL (SUC i) ks)`;;

let aes_fips_cipher = new_definition
 `aes_fips_cipher n (x:int128) (ks:int128 list) =
    fips197_final_round (aes_fips_rounds n (word_xor x (EL 0 ks)) ks) (EL (n + 1) ks)`;;

(* ------------------------------------------------------------------------- *)
(* Lanes.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* LANE_RULES tm: tm, an equation with `p` free for a lane, proven by conv
   at each of the 16 lanes. *)
let LANE_RULES conv tm =
  map (fun p ->
         let t = vsubst [mk_small_numeral (8 * p), `p:num`] tm in
         prove(t, REPEAT GEN_TAC THEN CONV_TAC conv))
      (0--15);;

let USIMD16_LANES = LANE_RULES
  (LAND_CONV (LAND_CONV AARCH32_SIMD_EXPAND_CONV THENC
              TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THENC
   REWRITE_CONV[])
  `!(f:byte->byte) (x:int128). word_subword (usimd16 f x) (p,8) = f (word_subword x (p,8))`;;

let BYTEREVERSE_LANES =
  map (fun p ->
         let t = vsubst [mk_small_numeral (8 * p), `p:num`;
                         mk_small_numeral (8 * (15 - p)), `q:num`]
                  `!x:int128. word_subword (word_bytereverse x) (p,8):byte = word_subword x (q,8)` in
         prove(t, GEN_TAC THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
                  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_REVERSEFIELDS;
                              DIMINDEX_8; DIMINDEX_128] THEN
                  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV))
      (0--15);;

let VPAES_LANE_CONV unfolds =
  let base = USIMD16_LANES @ BYTEREVERSE_LANES @
             [vpaes_tbl; vpaes_tmap; vpaes_lo; vpaes_hi; vpaes_inv; vpaes_inva;
              vpaes_mc_forward; vpaes_mc_backward; vpaes_sr; vpaes_mix3] in
  let rw = GEN_REWRITE_CONV I (base @ unfolds) in
  TOP_DEPTH_CONV
   (rw ORELSEC
    WORD_SIMPLE_SUBWORD_CONV ORELSEC
    REWR_CONV WORD_SUBWORD_XOR ORELSEC REWR_CONV WORD_SUBWORD_AND ORELSEC
    WORD_RED_CONV ORELSEC AARCH32_TBL_CONV ORELSEC BETA_CONV ORELSEC
    NUM_RED_CONV ORELSEC let_CONV ORELSEC EL_CONV);;

(* Splits an equation of 128-bit words into its 16 lanes, each side taken
   to its lanes' inputs. *)
let VPAES_SPLIT_LANES_TAC unfolds =
  GEN_REWRITE_TAC I [VPAES_WORD_EQ_BYTES] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_BINOP_CONV `(/\)` (BINOP_CONV (VPAES_LANE_CONV unfolds)));;

let VPAES_IO_SIMD = prove
 (`!x. vpaes_io x = usimd16 vpaes_iob x`,
  GEN_TAC THEN VPAES_SPLIT_LANES_TAC [vpaes_io; vpaes_iob] THEN REWRITE_TAC[]);;

let VPAES_JO_SIMD = prove
 (`!x. vpaes_jo x = usimd16 vpaes_job x`,
  GEN_TAC THEN VPAES_SPLIT_LANES_TAC [vpaes_jo; vpaes_job] THEN REWRITE_TAC[]);;

(* LANE_EQS conv tm: tm, a term with `x` and `p` free, with p each lane's
   offset, equated with what conv takes it to, generalized over x. *)
let LANE_EQS conv tm =
  map (fun p -> GEN_ALL (conv (vsubst [mk_small_numeral (8 * p), `p:num`] tm))) (0--15);;

let FIPS_LANE_SIMP_CONV =
  TOP_DEPTH_CONV (WORD_SIMPLE_SUBWORD_CONV ORELSEC EL_CONV ORELSEC let_CONV ORELSEC
                  NUM_RED_CONV ORELSEC BETA_CONV);;

let FIPS_SHIFT_ROWS_LANES = LANE_EQS
  (LAND_CONV (REWRITE_CONV[fips197_shift_rows; word_join_list_16_8]) THENC FIPS_LANE_SIMP_CONV)
  `word_subword (fips197_shift_rows (x:int128)) (p,8):byte`;;

let FIPS_SUB_BYTES_LANES = LANE_EQS
  (LAND_CONV (REWRITE_CONV[fips197_sub_bytes; aes_sub_bytes; aes_sub_bytes_select;
                           word_join_list_16_8]) THENC FIPS_LANE_SIMP_CONV)
  `word_subword (fips197_sub_bytes (x:int128)) (p,8):byte`;;

let FIPS_MIX_COLUMNS_LANES = LANE_EQS
  (LAND_CONV (REWRITE_CONV[fips197_mix_columns; word_join_list_16_8]) THENC
   FIPS_LANE_SIMP_CONV THENC REWRITE_CONV[aes_mix_word] THENC FIPS_LANE_SIMP_CONV)
  `word_subword (fips197_mix_columns (x:int128)) (p,8):byte`;;

let VPAES_FIPS_LANES = FIPS_SHIFT_ROWS_LANES @ FIPS_SUB_BYTES_LANES @ FIPS_MIX_COLUMNS_LANES;;

let rec vpaes_term_size t =
  match t with
    Comb(f,x) -> vpaes_term_size f + vpaes_term_size x
  | Abs(_,b) -> 1 + vpaes_term_size b
  | _ -> 1;;

(* Generalizes each subterm whose head is one of the constants named,
   largest first, to a fresh variable. *)

let VPAES_GEN_ATOMS_TAC names : tactic =
  fun (asl,w as gl) ->
    let atoms = find_terms (fun t -> is_comb t &&
                  (let h,_ = strip_comb t in is_const h && mem (fst(dest_const h)) names)) w in
    let atoms = sort (fun a b -> vpaes_term_size a > vpaes_term_size b) (setify atoms) in
    MAP_EVERY (fun t -> SPEC_TAC(t, genvar(type_of t)) THEN GEN_TAC) atoms gl;;

(* A lane of a round, its S-box outputs and the key's bytes as atoms of a
   GF(2)-linear identity. *)
let VPAES_LINEAR_TAC =
  REWRITE_TAC[VPAES_SB1_KEY; VPAES_SB2_BYTE; VPAES_SBO_KEY; VPAES_SBO_BYTE; VPAES_FFMUL03] THEN
  REWRITE_TAC[VPAES_TB_TLIN] THEN
  VPAES_GEN_ATOMS_TAC ["FFmul02"] THEN
  VPAES_GEN_ATOMS_TAC ["aes_sub_byte"] THEN
  REWRITE_TAC[vpaes_tlin] THEN BITBLAST_TAC;;

let VPAES_ROUND_UNFOLDS =
  [vpaes_mid; vpaes_a; vpaes_a2; vpaes_key; vpaes_state; VPAES_IO_SIMD; VPAES_JO_SIMD;
   fips197_round] @ VPAES_FIPS_LANES;;

(* ------------------------------------------------------------------------- *)
(* Rounds.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* Each operation that reads a rotation or permutation table by its round
   reads it at the round MOD 4. *)
let VPAES_MOD4_LEMMAS = map (fun def ->
    prove(mk_eq(lhs(snd(strip_forall(concl def))),
                vsubst [`r MOD 4`,`r:num`] (lhs(snd(strip_forall(concl def))))),
          REWRITE_TAC[def; MOD_MOD_REFL]))
  [vpaes_mc_forward; vpaes_mc_backward; vpaes_sr];;

let VPAES_STATE_MOD = prove
 (`!i. vpaes_state i = vpaes_state (i MOD 4)`,
  REWRITE_TAC[FUN_EQ_THM; vpaes_state; MOD_MOD_REFL]);;

let VPAES_KEY_MOD = prove
 (`!i. vpaes_key i = vpaes_key (i MOD 4)`,
  REWRITE_TAC[FUN_EQ_THM; vpaes_key; MOD_MOD_REFL]);;

let VPAES_MID_MOD = prove
 (`!i. vpaes_mid i = vpaes_mid (i MOD 4)`,
  REWRITE_TAC[FUN_EQ_THM; vpaes_mid] THEN
  ONCE_REWRITE_TAC[el 0 VPAES_MOD4_LEMMAS; el 1 VPAES_MOD4_LEMMAS] THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

let VPAES_LAST_MOD = prove
 (`!i. vpaes_last i = vpaes_last (i MOD 4)`,
  REWRITE_TAC[FUN_EQ_THM; vpaes_last] THEN
  ONCE_REWRITE_TAC[el 2 VPAES_MOD4_LEMMAS] THEN REWRITE_TAC[MOD_MOD_REFL]);;

let VPAES_KEY_LAST_MOD = prove
 (`!i. vpaes_key_last i = vpaes_key_last (i MOD 4)`,
  REWRITE_TAC[FUN_EQ_THM; vpaes_key_last] THEN
  ONCE_REWRITE_TAC[el 2 VPAES_MOD4_LEMMAS] THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* Splits a goal on i MOD 4, with SUC i MOD 4 following it. *)
let VPAES_MOD4_CASES_TAC =
  SUBGOAL_THEN `!i. SUC i MOD 4 = (i MOD 4 + 1) MOD 4` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[ADD1] THEN CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[GSYM MOD_ADD_MOD])) THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `i MOD 4 < 4` MP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`i MOD 4`,`r:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV;;

(* A middle round is FIPS 197's, on the state's vpaes form. *)
let VPAES_ROUND = prove
 (`!i S k. vpaes_mid (SUC i) (vpaes_io (vpaes_state i S)) (vpaes_jo (vpaes_state i S))
                     (vpaes_key (SUC i) (word_bytereverse k)) =
           vpaes_state (SUC i) (word_bytereverse (fips197_round (word_bytereverse S) k))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[VPAES_STATE_MOD; VPAES_KEY_MOD; VPAES_MID_MOD] THEN
  VPAES_MOD4_CASES_TAC THEN REPEAT CONJ_TAC THEN
  VPAES_SPLIT_LANES_TAC VPAES_ROUND_UNFOLDS THEN REPEAT CONJ_TAC THEN VPAES_LINEAR_TAC);;

let VPAES_TB_FIRST = prove
 (`!b z. word_xor (word_xor (aarch32_tbl 2 (word 0xcabae09052227808c2b2e8985a2a7000) (word_and b (word 15))) z)
                  (aarch32_tbl 2 (word 0xcd80b1fcb0fdcc814c01307d317c4d00) (word_ushr b 4)) =
         word_xor (vpaes_tb b) z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vpaes_tb] THEN
  VPAES_GEN_ATOMS_TAC ["aarch32_tbl"] THEN BITBLAST_TAC);;

(* The input transform with round key 0 is its AddRoundKey on vpaes's form. *)
let VPAES_FIRST = prove
 (`!x k. vpaes_first (vpaes_tmap (word_bytereverse k)) x =
         vpaes_state 0 (word_bytereverse (word_xor (word_bytereverse x) k))`,
  REPEAT GEN_TAC THEN
  VPAES_SPLIT_LANES_TAC [vpaes_first; vpaes_state] THEN
  REWRITE_TAC[VPAES_TB_FIRST; VPAES_TB_XOR]);;

(* The last round, after an odd number of middle rounds. *)
let VPAES_LAST = prove
 (`!n S k. ODD n
           ==> vpaes_last (n + 1) (vpaes_io (vpaes_state n S)) (vpaes_jo (vpaes_state n S))
                          (vpaes_key_last (n + 1) (word_bytereverse k)) =
               word_bytereverse (fips197_final_round (word_bytereverse S) k)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[VPAES_STATE_MOD; VPAES_LAST_MOD; VPAES_KEY_LAST_MOD] THEN
  REWRITE_TAC[GSYM ADD1] THEN
  SUBGOAL_THEN `ODD n <=> ODD (n MOD 4)` SUBST1_TAC THENL
   [REWRITE_TAC[ODD_MOD; ARITH_RULE `4 = 2 * 2`; MOD_MOD]; ALL_TAC] THEN
  SPEC_TAC(`n:num`,`i:num`) THEN GEN_TAC THEN
  VPAES_MOD4_CASES_TAC THEN REWRITE_TAC[ODD; ARITH] THEN REPEAT CONJ_TAC THEN
  VPAES_SPLIT_LANES_TAC ([vpaes_last; vpaes_key_last; vpaes_state; VPAES_IO_SIMD; VPAES_JO_SIMD;
                          fips197_final_round] @ VPAES_FIPS_LANES) THEN
  REPEAT CONJ_TAC THEN VPAES_LINEAR_TAC);;

let VPAES_SCHEDULE_EL = prove
 (`!n ks j. j < n + 2
            ==> EL j (vpaes_schedule n ks) =
                if j = 0 then vpaes_tmap (word_bytereverse (EL 0 ks))
                else if j <= n then vpaes_key j (word_bytereverse (EL j ks))
                else vpaes_key_last (n + 1) (word_bytereverse (EL j ks))`,
  SIMP_TAC[vpaes_schedule; EL_LIST_OF_SEQ]);;

(* The middle rounds, by induction. *)
let VPAES_ROUNDS = prove
 (`!n ks y i. i <= n
              ==> vpaes_rounds i (vpaes_schedule n ks) (vpaes_state 0 (word_bytereverse y)) =
                  vpaes_state i (word_bytereverse (aes_fips_rounds i y ks))`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[vpaes_rounds; aes_fips_rounds] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[VPAES_SCHEDULE_EL; ARITH_RULE `SUC i <= n ==> SUC i < n + 2`; NOT_SUC] THEN
  REWRITE_TAC[VPAES_ROUND; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* vpaes's cipher, on the schedule vpaes reads, is FIPS 197's on
   little-endian words. *)
let VPAES_CIPHER = prove
 (`!n ks x. ODD n
            ==> vpaes_cipher n (vpaes_schedule n ks) x =
                word_bytereverse (aes_fips_cipher n (word_bytereverse x) ks)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vpaes_cipher; aes_fips_cipher] THEN
  SIMP_TAC[VPAES_SCHEDULE_EL; ARITH_RULE `0 < n + 2 /\ n + 1 < n + 2 /\ ~(n + 1 = 0) /\ ~(n + 1 <= n)`] THEN
  REWRITE_TAC[VPAES_FIRST] THEN
  SIMP_TAC[VPAES_ROUNDS; LE_REFL] THEN
  ASM_SIMP_TAC[VPAES_LAST; WORD_BYTEREVERSE_BYTEREVERSE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_SIMP_TAC[VPAES_LAST; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* aes_fips_cipher 9 and 13 are the fork's AES-128 and AES-256 ciphers,
   unrolled; it has no AES-192 one. *)
let AES_FIPS_ROUNDS_CONV =
  let pth = CONJUNCT2 aes_fips_rounds in
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Const("aes_fips_rounds",_),n),_),_)
        when is_numeral n && dest_small_numeral n > 0 ->
        (RATOR_CONV(RATOR_CONV(RAND_CONV num_CONV)) THENC REWR_CONV pth THENC
         RAND_CONV(LAND_CONV NUM_SUC_CONV) THENC LAND_CONV conv) tm
    | Comb(Comb(Comb(Const("aes_fips_rounds",_),n),_),_) when is_numeral n ->
        REWR_CONV (CONJUNCT1 aes_fips_rounds) tm
    | _ -> failwith "AES_FIPS_ROUNDS_CONV" in
  conv;;

let AES_FIPS_CIPHER_128 = prove
 (`!x ks. aes_fips_cipher 9 x ks = aes128_cipher x ks`,
  REWRITE_TAC[aes_fips_cipher; aes128_cipher] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV AES_FIPS_ROUNDS_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let AES_FIPS_CIPHER_256 = prove
 (`!x ks. aes_fips_cipher 13 x ks = aes256_cipher x ks`,
  REWRITE_TAC[aes_fips_cipher; aes256_cipher] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV AES_FIPS_ROUNDS_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The schedule in memory.                                                   *)
(* ------------------------------------------------------------------------- *)

let vpaes_blocks_num = define
 `(!f j. vpaes_blocks_num (f:num->int128) j 0 = 0) /\
  (!f j m. vpaes_blocks_num f j (SUC m) =
           val(f j) + 2 EXP 128 * vpaes_blocks_num f (j + 1) m)`;;

let VPAES_ADD_MULT_EXP_EQ = prove
 (`!e x y x' y'. x < e /\ x' < e
                 ==> (x + e * y = x' + e * y' <=> x = x' /\ y = y')`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x + e * y) MOD e = (x' + e * y') MOD e /\
                (x + e * y) DIV e = (x' + e * y') DIV e` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(e = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES]);;

let VPAES_FORALL_LT_SUC = prove
 (`!P m. (!i. i < SUC m ==> P i) <=> P 0 /\ (!i. i < m ==> P(SUC i))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[LT_SUC; LT_0]]);;

let VPAES_READ_BYTES128_VAL = prove
 (`!(a:int32) s x. read (memory :> bytes128 a) s = x <=>
                   read (memory :> bytes(a,16)) s = val(x:int128)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let VPAES_READ_BLOCKS = prove
 (`!m (f:num->int128) j (a:int32) s.
        read (memory :> bytes(a,16 * m)) s = vpaes_blocks_num f j m <=>
        !i. i < m ==> read (memory :> bytes128(word_add a (word(16 * i)))) s =
                      f(j + i)`,
  INDUCT_TAC THEN REWRITE_TAC[vpaes_blocks_num; CONJUNCT1 LT; MULT_CLAUSES] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * m + 16 = 16 + 16 * m`; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[ARITH_RULE `8 * 16 = 128`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VPAES_ADD_MULT_EXP_EQ o lhand o snd) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `(f:num->int128) j` VAL_BOUND) THEN
    MP_TAC(ISPECL [`a:int32`; `16`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM VPAES_READ_BYTES128_VAL] THEN
  REWRITE_TAC[VPAES_FORALL_LT_SUC] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              ARITH_RULE `(j + 1) + i = SUC(j + i)`]);;

let VPAES_KEY_BLOCKS = prove
 (`!key n (kv:int128 list) s.
     (!j. j < n + 2
          ==> read (memory :> bytes128 (word_add key (word(16 * j)))) s = EL j kv) <=>
     read (memory :> bytes(key,16 * (n + 2))) s = vpaes_blocks_num (\j. EL j kv) 0 (n + 2)`,
  REWRITE_TAC[VPAES_READ_BLOCKS; ADD_CLAUSES]);;

let VP_ADD_ADD = prove
 (`!k a b. word_add (word_add k (word a)) (word b):int32 = word_add k (word (a + b))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; WORD_ADD]);;

let VP_KEY_HALVES_TAC (js:term list) =
  MAP_EVERY (fun j ->
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes(a,l)) s = vpaes_blocks_num f j m`) (concl th)
      then MP_TAC(SPEC j (REWRITE_RULE[VPAES_READ_BLOCKS] th))
      else NO_TAC) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    DISCH_THEN(fun th -> let th' = MATCH_MP VPAES_BYTES128_HALVES th in
      STRIP_ASSUME_TAC th' THEN
      STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) (REWRITE_RULE[VP_ADD_ADD] th')))) js;;

(* ------------------------------------------------------------------------- *)
(* The loop.                                                                 *)
(* ------------------------------------------------------------------------- *)

let VPAES_INV = `\i s.
  (read R1 s = out /\
   read R9 s = word_add key (word (16 * (i + 2))) /\
   read R8 s = word (n - i) /\
   read R11 s = word (pc + 16 * ((i + 1) MOD 4)) /\
   read LR s = word (pc + 0x314) /\
   read Q9 s = word 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f /\
   read Q10 s = word 0x040703090a0b0c020e05060f0d080180 /\
   read Q11 s = word 0x030d0e0c0205080901040a060f0b0780 /\
   read Q12 s = word 0x3bf7ccc10d2ed9ef3618d415fae22300 /\
   read Q13 s = word 0xa5df7a6e142af544b19be18fcb503e00 /\
   read Q14 s = word 0xc2a163c8ab82234a69eb88400ae12900 /\
   read Q15 s = word 0x5eb7e955bc982fcde27a93c60b712400 /\
   read (memory :> bytes(key,16 * (n + 2))) s = vpaes_blocks_num (\j. EL j kv) 0 (n + 2) /\
   read Q2 s = vpaes_io (vpaes_rounds i kv (vpaes_first (EL 0 kv) x)) /\
   read Q3 s = vpaes_jo (vpaes_rounds i kv (vpaes_first (EL 0 kv) x)) /\
   read Q5 s = EL (i + 1) kv) /\
  (read ZF s <=> i = n)`;;

let VP_SUB1 = prove
 (`!n i. i < n ==> word_sub (word (n - i)) (word 1):int32 = word (n - (i + 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `n - (i + 1) = (n - i) - 1`] THEN
  ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < n ==> 1 <= n - i`]);;

let VP_ZF = prove
 (`!n i. i < n /\ n <= 13 ==> (val (word (n - (i + 1)):int32) = 0 <=> i + 1 = n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (word (n - (i + 1)):int32) = n - (i + 1)` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let VP_BODY_FINAL_TAC =
  FIRST_X_ASSUM(fun th -> if concl th = `i < n` then
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP VP_SUB1 th]) THEN ASSUME_TAC th else NO_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VP_ADD_ADD; ADD_0] THEN
  REWRITE_TAC[ARITH_RULE `16 * (i + 2) + 16 = 16 * (i + 3)`] THEN
  MATCH_MP_TAC VP_ZF THEN ASM_REWRITE_TAC[];;

let VPAES_ROUNDS_ADD1 = prove
 (`!i ks x. vpaes_rounds (i + 1) ks x =
            vpaes_mid (i + 1) (vpaes_io (vpaes_rounds i ks x)) (vpaes_jo (vpaes_rounds i ks x))
                      (EL (i + 1) ks)`,
  REWRITE_TAC[GSYM ADD1; vpaes_rounds]);;

let VP_MID_TERM w =
  find_term (fun t -> is_comb t &&
    (try fst(dest_const(fst(strip_comb t))) = "vpaes_mid" && length(snd(strip_comb t)) = 4
     with Failure _ -> false)) w;;

let VP_ROUND_CASE_TAC : tactic =
  fun (asl,w as gl) ->
  let m = VP_MID_TERM w in
  (SUBGOAL_THEN `aarch32_nowrap (word_add key (word (16 * (i + 2))):int32) 16` ASSUME_TAC THENL
    [MATCH_MP_TAC AARCH32_NOWRAP_OFFSET THEN EXISTS_TAC `244` THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `i < n` THEN UNDISCH_TAC `n <= 13` THEN ARITH_TAC;
     ALL_TAC] THEN
   MAP_EVERY (fun (v,c) -> GHOST_INTRO_TAC v c)
    [`q0:int128`,`read Q0`; `q1:int128`,`read Q1`; `q4:int128`,`read Q4`] THEN
   ENSURES_INIT_TAC "s0" THEN
   VP_KEY_HALVES_TAC [`i + 2`] THEN
   VP_STEPS_TAC (1--10) THEN
   VP_FOLD_TAC `Q0` `vpaes_a a b k` [vpaes_a] THEN
   VP_STEPS_TAC (11--16) THEN
   VP_FOLD_TAC `Q2` `vpaes_a2 a b` [vpaes_a2] THEN
   VP_STEPS_TAC (17--24) THEN
   VP_FOLD_TAC `Q0` m [vpaes_mid] THEN
   VP_STEPS_TAC (25--41) THEN
   VP_FOLD_TAC `Q2` (mk_comb(`vpaes_io`, m)) [vpaes_io] THEN
   VP_STEPS_TAC [42] THEN
   VP_FOLD_TAC `Q3` (mk_comb(`vpaes_jo`, m)) [vpaes_jo] THEN
   VP_STEPS_TAC [43] THEN
   VP_BODY_FINAL_TAC) gl;;

let VP_LAST_TERM w =
  find_term (fun t -> is_comb t &&
    (try fst(dest_const(fst(strip_comb t))) = "vpaes_last" && length(snd(strip_comb t)) = 4
     with Failure _ -> false)) w;;

let VP_EXIT_CASE_TAC : tactic =
  fun (asl,w as gl) ->
  let m = VP_LAST_TERM w in
  (MAP_EVERY (fun (v,c) -> GHOST_INTRO_TAC v c)
    [`q0:int128`,`read Q0`; `q1:int128`,`read Q1`; `q4:int128`,`read Q4`] THEN
   ENSURES_INIT_TAC "s0" THEN
   VP_STEPS_TAC (1--14) THEN
   VP_FOLD_TAC `Q0` m [vpaes_last] THEN
   VP_STEPS_TAC (15--16) THEN
   ENSURES_FINAL_STATE_TAC THEN
   REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
   ASM_REWRITE_TAC[] THEN
   CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
   REWRITE_TAC[AARCH32_JOIN_HALVES]) gl;;

(* ------------------------------------------------------------------------- *)
(* The routine.                                                              *)
(* ------------------------------------------------------------------------- *)

(* From after vpaes_encrypt's push and vpush to its vpop: the block at inp
   is x, the n + 2 round keys at key, in vpaes's form, are kv, and the
   rounds field at key + 240 is n; the routine leaves vpaes's cipher of x
   at out. aws-lc's key setup writes n as 9, 11, or 13. *)
let VPAES_ENCRYPT_CORRECT = prove
 (`!inp out key n kv x pc.
     0 < n /\ n <= 13 /\ 128 divides pc /\ aarch32_nowrap (word pc) 0x320 /\
     aarch32_nowrap inp 16 /\ aarch32_nowrap out 16 /\ aarch32_nowrap key 244 /\
     nonoverlapping (word pc,0x320) (out,16)
     ==> ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) vpaes_encrypt_mc /\
               read PC s = word (pc + 0x308) /\
               C_ARGUMENTS [inp; out; key] s /\
               read (memory :> bytes128 inp) s = x /\
               read (memory :> bytes32 (word_add key (word 240))) s = word n /\
               (!j. j < n + 2
                    ==> read (memory :> bytes128 (word_add key (word(16 * j)))) s =
                        EL j kv))
          (\s. read PC s = word (pc + 0x318) /\
               read (memory :> bytes128 out) s = vpaes_cipher n kv x)
          (MAYCHANGE [PC; LR; R8; R9; R10; R11] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes128 out] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; fst VPAES_ENCRYPT_EXEC; NONOVERLAPPING_CLAUSES;
              VPAES_KEY_BLOCKS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_PUP_TAC `n:num` `pc + 0x210` `pc + 0x2bc` VPAES_INV THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (* In: the preheat's tables, the input transform and round key 0, and
       the first round's top, through its BNE. *)
    REWRITE_TAC[vpaes_rounds] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    MAP_EVERY (fun (v,c) -> GHOST_INTRO_TAC v c)
     [`q1:int128`,`read Q1`; `q2:int128`,`read Q2`; `q3:int128`,`read Q3`;
      `q4:int128`,`read Q4`; `q5:int128`,`read Q5`] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VPAES_BYTES128_HALVES o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o concl)) THEN
    VP_KEY_HALVES_TAC [`0`; `1`] THEN
    VP_STEPS_TAC (1--24) THEN
    VP_FOLD_TAC `Q0` `vpaes_first (EL 0 kv) x` [vpaes_first] THEN
    VP_STEPS_TAC (25--42) THEN
    VP_FOLD_TAC `Q2` `vpaes_io (vpaes_first (EL 0 kv) x)` [vpaes_io] THEN
    VP_STEPS_TAC [43] THEN
    VP_FOLD_TAC `Q3` `vpaes_jo (vpaes_first (EL 0 kv) x)` [vpaes_jo] THEN
    VP_STEPS_TAC [44] THEN
    SUBGOAL_THEN `~(val(word n:int32) = 0)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC(ARITH_RULE `m = n /\ 0 < n ==> ~(m = 0)`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN
      UNDISCH_TAC `n <= 13` THEN ARITH_TAC;
      ALL_TAC] THEN
    VP_STEPS_TAC [45] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SUB_0];

    (* Round i + 1, from the head to the next round's top: the rotations it
       reads, at R11, are those for (i + 1) MOD 4. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[VPAES_ROUNDS_ADD1; ARITH_RULE `(i + 1) + 2 = i + 3 /\ (i + 1) + 1 = i + 2`] THEN
    ABBREV_TAC `y = vpaes_rounds i kv (vpaes_first (EL 0 kv) x)` THEN
    ABBREV_TAC `a = vpaes_io y` THEN ABBREV_TAC `b = vpaes_jo y` THEN
    ABBREV_TAC `k = EL (i + 1) (kv:int128 list)` THEN
    GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [VPAES_MID_MOD] THEN
    SUBGOAL_THEN `(i + 2) MOD 4 = ((i + 1) MOD 4 + 1) MOD 4` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `i + 2 = (i + 1) + 1`] THEN
      MP_TAC(SPECL [`i + 1`; `1`; `4`] MOD_ADD_MOD) THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(i + 1) MOD 4 < 4` MP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`(i + 1) MOD 4`,`r:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN VP_ROUND_CASE_TAC;

    (* Back to the head while rounds remain. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `read ZF (s0:aarch32state) <=> (i:num) = n` THEN
    ASM_SIMP_TAC[LT_IMP_NE] THEN DISCH_TAC THEN
    AARCH32_STEPS_TAC VPAES_ENCRYPT_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (* Out: the last round, whose ShiftRows reads sr at (n + 1) MOD 4, the
       return from the core, and the store. *)
    REWRITE_TAC[vpaes_cipher] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ABBREV_TAC `y = vpaes_rounds n kv (vpaes_first (EL 0 kv) x)` THEN
    ABBREV_TAC `a = vpaes_io y` THEN ABBREV_TAC `b = vpaes_jo y` THEN
    ABBREV_TAC `k = EL (n + 1) (kv:int128 list)` THEN
    GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [VPAES_LAST_MOD] THEN
    SUBGOAL_THEN `(n + 1) MOD 4 < 4` MP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`(n + 1) MOD 4`,`r:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN VP_EXIT_CASE_TAC]);;

(* From entry to return, through the prologue's push of R7-R11 and LR and
   vpush of D8-D11 into the 56 bytes below SP, and the epilogue's pops. *)
let VPAES_ENCRYPT_SUBROUTINE_CORRECT = prove
 (`!inp out key n kv x pc stackpointer returnaddress.
     0 < n /\ n <= 13 /\ 128 divides pc /\ aarch32_nowrap (word pc) 0x320 /\
     aarch32_nowrap inp 16 /\ aarch32_nowrap out 16 /\ aarch32_nowrap key 244 /\
     nonoverlapping (word pc,0x320) (out,16) /\
     aarch32_bx_target returnaddress /\ aligned 4 stackpointer /\
     aarch32_nowrap (word_sub stackpointer (word 56)) 56 /\
     ALL (nonoverlapping (word_sub stackpointer (word 56),56))
         [word pc,0x320; inp,16; out,16; key,244]
     ==> ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) vpaes_encrypt_mc /\
               read PC s = word (pc + 0x300) /\
               read SP s = stackpointer /\
               read LR s = returnaddress /\
               C_ARGUMENTS [inp; out; key] s /\
               read (memory :> bytes128 inp) s = x /\
               read (memory :> bytes32 (word_add key (word 240))) s = word n /\
               (!j. j < n + 2
                    ==> read (memory :> bytes128 (word_add key (word(16 * j)))) s =
                        EL j kv))
          (\s. read PC s = returnaddress /\
               read (memory :> bytes128 out) s = vpaes_cipher n kv x)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes128 out] ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 56),56)])`,
  REWRITE_TAC[fst VPAES_ENCRYPT_EXEC; VPAES_KEY_BLOCKS] THEN
  AARCH32_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(2,2) ~qreglist:`[Q4; Q5]`
    VPAES_ENCRYPT_EXEC
    (REWRITE_RULE[fst VPAES_ENCRYPT_EXEC; VPAES_KEY_BLOCKS] VPAES_ENCRYPT_CORRECT)
    `[R7; R8; R9; R10; R11]` 56);;

(* AES-128, AES-192, or AES-256, with n 9, 11, or 13: given the round keys
   ks in the form vpaes_schedule puts them, the routine leaves FIPS 197's
   cipher of the block, each in a block's byte order. *)
let VPAES_ENCRYPT_FIPS197_SUBROUTINE_CORRECT = prove
 (`!inp out key n ks x pc stackpointer returnaddress.
     (n = 9 \/ n = 11 \/ n = 13) /\ 128 divides pc /\ aarch32_nowrap (word pc) 0x320 /\
     aarch32_nowrap inp 16 /\ aarch32_nowrap out 16 /\ aarch32_nowrap key 244 /\
     nonoverlapping (word pc,0x320) (out,16) /\
     aarch32_bx_target returnaddress /\ aligned 4 stackpointer /\
     aarch32_nowrap (word_sub stackpointer (word 56)) 56 /\
     ALL (nonoverlapping (word_sub stackpointer (word 56),56))
         [word pc,0x320; inp,16; out,16; key,244]
     ==> ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) vpaes_encrypt_mc /\
               read PC s = word (pc + 0x300) /\
               read SP s = stackpointer /\
               read LR s = returnaddress /\
               C_ARGUMENTS [inp; out; key] s /\
               read (memory :> bytes128 inp) s = x /\
               read (memory :> bytes32 (word_add key (word 240))) s = word n /\
               (!j. j < n + 2
                    ==> read (memory :> bytes128 (word_add key (word(16 * j)))) s =
                        EL j (vpaes_schedule n ks)))
          (\s. read PC s = returnaddress /\
               read (memory :> bytes128 out) s =
               word_bytereverse (aes_fips_cipher n (word_bytereverse x) ks))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes128 out] ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 56),56)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `ODD n /\ 0 < n /\ n <= 13` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VPAES_CIPHER] THEN
  MATCH_MP_TAC VPAES_ENCRYPT_SUBROUTINE_CORRECT THEN ASM_REWRITE_TAC[]);;
