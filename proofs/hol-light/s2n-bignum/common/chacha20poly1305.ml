(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of ChaCha20, Poly1305, and AEAD_CHACHA20_POLY1305           *)
(* (RFC 8439).                                                               *)
(*                                                                           *)
(* Keys, nonces, messages, and tags are byte lists, as the RFC writes them;  *)
(* ChaCha20's state is a list of 16 int32 words, and Poly1305's accumulator  *)
(* a number. Like common/bignum.ml it uses num_of_bytelist and               *)
(* bytelist_of_num from common/words2.ml and SUB_LIST from common/misc.ml,   *)
(* so it loads after an architecture's proofs/base.ml.                       *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* The ChaCha20 block function (RFC 8439, sections 2.1 to 2.3).              *)
(* ------------------------------------------------------------------------- *)

let chacha20_quarter_round = new_definition
 `chacha20_quarter_round (a:int32,b:int32,c:int32,d:int32) =
    let a = word_add a b in
    let d = word_rol (word_xor d a) 16 in
    let c = word_add c d in
    let b = word_rol (word_xor b c) 12 in
    let a = word_add a b in
    let d = word_rol (word_xor d a) 8 in
    let c = word_add c d in
    let b = word_rol (word_xor b c) 7 in
    (a,b,c,d)`;;

(* The column rounds then the diagonal rounds: section 2.3.1's inner_block. *)

let chacha20_double_round = new_definition
 `chacha20_double_round (s:int32 list) =
    let (x0,x4,x8,x12) =
      chacha20_quarter_round (EL 0 s,EL 4 s,EL 8 s,EL 12 s) in
    let (x1,x5,x9,x13) =
      chacha20_quarter_round (EL 1 s,EL 5 s,EL 9 s,EL 13 s) in
    let (x2,x6,x10,x14) =
      chacha20_quarter_round (EL 2 s,EL 6 s,EL 10 s,EL 14 s) in
    let (x3,x7,x11,x15) =
      chacha20_quarter_round (EL 3 s,EL 7 s,EL 11 s,EL 15 s) in
    let (x0,x5,x10,x15) = chacha20_quarter_round (x0,x5,x10,x15) in
    let (x1,x6,x11,x12) = chacha20_quarter_round (x1,x6,x11,x12) in
    let (x2,x7,x8,x13) = chacha20_quarter_round (x2,x7,x8,x13) in
    let (x3,x4,x9,x14) = chacha20_quarter_round (x3,x4,x9,x14) in
    [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15]`;;

let chacha20_rounds = define
 `chacha20_rounds 0 (s:int32 list) = s /\
  chacha20_rounds (SUC n) s = chacha20_double_round (chacha20_rounds n s)`;;

(* The first n little-endian words of a byte list. *)

let chacha20_words = new_definition
 `chacha20_words n (b:byte list) : int32 list =
    list_of_seq (\i. word(num_of_bytelist(SUB_LIST(4 * i,4) b))) n`;;

(* Section 2.3's initial state for a 32-byte key, a block counter, and a     *)
(* 12-byte nonce.                                                            *)

let chacha20_state = new_definition
 `chacha20_state (key:byte list) (counter:int32) (nonce:byte list) =
    APPEND [word 0x61707865; word 0x3320646e; word 0x79622d32; word 0x6b206574]
      (APPEND (chacha20_words 8 key) (CONS counter (chacha20_words 3 nonce)))`;;

(* The 64-byte keystream block: 20 rounds, the initial state added word by  *)
(* word, serialized little-endian.                                           *)

let chacha20_block = new_definition
 `chacha20_block key counter nonce : byte list =
    let s = chacha20_state key counter nonce in
    ITLIST (\w l. APPEND (bytelist_of_num 4 (val(w:int32))) l)
      (MAP2 word_add (chacha20_rounds 10 s) s) []`;;

(* ------------------------------------------------------------------------- *)
(* ChaCha20 encryption (RFC 8439, section 2.4): the message XOR the          *)
(* keystream from block counter on, the 32-bit counter wrapping.             *)
(* ------------------------------------------------------------------------- *)

let chacha20_keystream = define
 `chacha20_keystream key counter nonce 0 = [] /\
  chacha20_keystream key counter nonce (SUC n) =
    APPEND (chacha20_keystream key counter nonce n)
      (chacha20_block key (word_add counter (word n)) nonce)`;;

(* MAP2 runs over the message, never longer than the keystream. *)

let chacha20_encrypt = new_definition
 `chacha20_encrypt key counter nonce (msg:byte list) =
    MAP2 word_xor msg
      (chacha20_keystream key counter nonce ((LENGTH msg + 63) DIV 64))`;;

(* ------------------------------------------------------------------------- *)
(* Poly1305 (RFC 8439, section 2.5).                                         *)
(* ------------------------------------------------------------------------- *)

let p_1305 = new_definition `p_1305 = 2 EXP 130 - 5`;;

let poly1305_clamp = new_definition
 `poly1305_clamp r =
    val(word_and (word r:int128) (word 0x0ffffffc0ffffffc0ffffffc0fffffff))`;;

(* The accumulator after the first n 16-byte blocks of msg, the last one cut *)
(* to the message, each with a one byte after it.                            *)

let poly1305_acc = define
 `poly1305_acc r (msg:byte list) 0 = 0 /\
  poly1305_acc r msg (SUC n) =
    let b = SUB_LIST(16 * n,16) msg in
    ((poly1305_acc r msg n + num_of_bytelist b + 2 EXP (8 * LENGTH b)) * r)
    MOD p_1305`;;

let poly1305_mac = new_definition
 `poly1305_mac (key:byte list) (msg:byte list) =
    let r = poly1305_clamp(num_of_bytelist(SUB_LIST(0,16) key)) in
    let s = num_of_bytelist(SUB_LIST(16,16) key) in
    bytelist_of_num 16 (poly1305_acc r msg ((LENGTH msg + 15) DIV 16) + s)`;;

(* ------------------------------------------------------------------------- *)
(* AEAD_CHACHA20_POLY1305 (RFC 8439, sections 2.6 and 2.8).                  *)
(* ------------------------------------------------------------------------- *)

(* Section 2.6's poly1305_key_gen. *)

let chacha20_poly1305_key_gen = new_definition
 `chacha20_poly1305_key_gen key nonce =
    SUB_LIST(0,32) (chacha20_block key (word 0) nonce)`;;

let chacha20_poly1305_pad16 = new_definition
 `chacha20_poly1305_pad16 (x:byte list) =
    REPLICATE ((16 - LENGTH x MOD 16) MOD 16) (word 0:byte)`;;

(* Section 2.8.1's mac_data. *)

let chacha20_poly1305_mac_data = new_definition
 `chacha20_poly1305_mac_data (aad:byte list) (ct:byte list) =
    APPEND aad (APPEND (chacha20_poly1305_pad16 aad)
      (APPEND ct (APPEND (chacha20_poly1305_pad16 ct)
        (APPEND (bytelist_of_num 8 (LENGTH aad))
          (bytelist_of_num 8 (LENGTH ct))))))`;;

(* The tag over the AAD and the ciphertext. *)

let chacha20_poly1305_tag = new_definition
 `chacha20_poly1305_tag key nonce aad ct =
    poly1305_mac (chacha20_poly1305_key_gen key nonce)
      (chacha20_poly1305_mac_data aad ct)`;;

(* Encryption: the ciphertext, ChaCha20 from block 1, and its tag. *)

let chacha20_poly1305_seal = new_definition
 `chacha20_poly1305_seal key nonce aad msg =
    let ct = chacha20_encrypt key (word 1) nonce msg in
    (ct,chacha20_poly1305_tag key nonce aad ct)`;;

(* Decryption: the plaintext, and whether tag is the ciphertext's. *)

let chacha20_poly1305_open = new_definition
 `chacha20_poly1305_open key nonce aad ct tag =
    (chacha20_encrypt key (word 1) nonce ct,
     (chacha20_poly1305_tag key nonce aad ct = tag))`;;

(* ------------------------------------------------------------------------- *)
(* Evaluation on literal arguments, call by value: each let-bound value and  *)
(* each argument is reduced to a literal before it is substituted, so the    *)
(* terms stay small.                                                         *)
(* ------------------------------------------------------------------------- *)

let CHACHA20_POLY1305_CONV : conv =
  let num_rec th path =
    let th0,th1 = CONJ_PAIR th in
    GEN_REWRITE_CONV I [th0] ORELSEC
    (path num_CONV THENC GEN_REWRITE_CONV I [th1]) in
  let rec head_beta tm =
    match tm with
      Comb(Abs(_,_),_) -> BETA_CONV tm
    | Comb(Comb(_,_) as f,x) -> (RATOR_CONV head_beta THENC TRY_CONV BETA_CONV) tm
    | _ -> failwith "head_beta" in
  let step = FIRST_CONV
   [NUM_RED_CONV; WORD_RED_CONV; head_beta; EL_CONV; LENGTH_CONV;
    SUB_LIST_CONV; LIST_OF_SEQ_CONV;
    GEN_REWRITE_CONV I
     [chacha20_quarter_round; chacha20_double_round; chacha20_words;
      chacha20_state; chacha20_block; chacha20_encrypt; p_1305;
      poly1305_clamp; poly1305_mac; chacha20_poly1305_key_gen;
      chacha20_poly1305_pad16; chacha20_poly1305_mac_data;
      chacha20_poly1305_tag; chacha20_poly1305_seal;
      chacha20_poly1305_open; APPEND; ITLIST; MAP2_DEF; HD; TL;
      num_of_bytelist; CONS_11; NOT_CONS_NIL; REFL_CLAUSE;
      AND_CLAUSES];
    num_rec chacha20_rounds (RATOR_CONV o RAND_CONV);
    num_rec chacha20_keystream RAND_CONV;
    num_rec poly1305_acc RAND_CONV;
    num_rec bytelist_of_num (RATOR_CONV o RAND_CONV);
    num_rec REPLICATE (RATOR_CONV o RAND_CONV)] in
  let rec args tm =
    match tm with
      Comb(f,x) -> COMB2_CONV args eval tm
    | _ -> REFL tm
  and eval tm =
    if is_numeral tm || is_abs tm then REFL tm
    else if is_let tm then (RAND_CONV eval THENC let_CONV THENC eval) tm
    else
      let th = args tm in
      let tm' = rand(concl th) in
      match try Some(step tm') with Failure _ -> None with
        Some th' when not(aconv tm' (rand(concl th'))) ->
          TRANS th (TRANS th' (eval(rand(concl th'))))
      | _ -> th in
  eval;;

(* ------------------------------------------------------------------------- *)
(* Known answers: RFC 8439's sections 2.4.2, 2.5.2, and 2.8.2. Failure of    *)
(* one means the spec is wrong.                                              *)
(* ------------------------------------------------------------------------- *)

let CHACHA20_POLY1305_KAT =
  let bytes l = mk_list(map (fun n ->
    mk_comb(`word:num->byte`,mk_small_numeral n)) l,`:byte`) in
  let hex s =
    let d i = int_of_string("0x" ^ String.sub s (2 * i) 2) in
    bytes(map d (0--(String.length s / 2 - 1)))
  and ascii s =
    bytes(map (fun i -> Char.code(String.get s i)) (0--(String.length s - 1))) in
  let kat tm = prove(tm,CONV_TAC(LAND_CONV CHACHA20_POLY1305_CONV) THEN
                        REFL_TAC) in
  let sunscreen = ascii
   ("Ladies and Gentlemen of the class of '99: If I could offer you only " ^
    "one tip for the future, sunscreen would be it.") in
  let encrypt = kat(list_mk_comb(`(=):byte list->byte list->bool`,
   [list_mk_comb(`chacha20_encrypt`,
     [hex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
      `word 1:int32`; hex "000000000000004a00000000"; sunscreen]);
    hex ("6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0b" ^
         "f91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d8" ^
         "07ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab7793736" ^
         "5af90bbf74a35be6b40b8eedf2785e42874d")]))
  and mac = kat(list_mk_comb(`(=):byte list->byte list->bool`,
   [list_mk_comb(`poly1305_mac`,
     [hex "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b";
      ascii "Cryptographic Forum Research Group"]);
    hex "a8061dc1305136c6c22b8baf0c0127a9"])) in
  let key = hex "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
  and nonce = hex "070000004041424344454647"
  and aad = hex "50515253c0c1c2c3c4c5c6c7"
  and ct = hex ("d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736" ^
    "ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b" ^
    "3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3f" ^
    "f4def08e4b7a9de576d26586cec64b6116")
  and tag = hex "1ae10b594f09e26a7e902ecbd0600691"
  and bad = hex "1ae10b594f09e26a7e902ecbd0600690" in
  let seal = kat(mk_eq(list_mk_comb(`chacha20_poly1305_seal`,
                                    [key; nonce; aad; sunscreen]),
                       mk_pair(ct,tag)))
  and opened = kat(mk_eq(list_mk_comb(`chacha20_poly1305_open`,
                                      [key; nonce; aad; ct; tag]),
                         mk_pair(sunscreen,`T`)))
  and refused = kat(mk_eq(list_mk_comb(`chacha20_poly1305_open`,
                                       [key; nonce; aad; ct; bad]),
                          mk_pair(sunscreen,`F`))) in
  end_itlist CONJ [encrypt; mac; seal; opened; refused];;
