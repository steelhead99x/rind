(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The crypto extension's SHA-1 steps, which s2n-bignum's aarch64 model,     *)
(* written for SHA-256 and SHA-512, does not define: SHA1C, SHA1P, SHA1M,    *)
(* SHA1H, SHA1SU0, and SHA1SU1, as DDI 0487's pseudocode states them, with   *)
(* arm/proofs/sha256.ml's choose and majority. Each takes its operands as    *)
(* the instruction names them, the destination first.                       *)
(* ========================================================================= *)

needs "arm/proofs/sha256.ml";;

let sha1_parity = new_definition
 `sha1_parity (x:int32) (y:int32) (z:int32) : int32 =
    word_xor x (word_xor y z)`;;

(* One of SHA1hash's four rounds, on Y:X as one 160-bit word, Y on top: Y
   gains ROL(X<31:0>, 5), the round's function `f` of X's other words, and
   word `e` of W; X<63:32> rotates left by 30; and Y:X rotates left by 32. *)

let sha1_round = new_definition
 `sha1_round (f:int32->int32->int32->int32) e (w:int128) (yx:160 word) =
    word_rol
     ((word_join:int32->int128->160 word)
       (word_add (word_subword yx (128,32))
         (word_add (word_rol (word_subword yx (0,32):int32) 5)
           (word_add (f (word_subword yx (32,32)) (word_subword yx (64,32))
                        (word_subword yx (96,32)))
                     (word_subword w (32 * e,32)))))
       (word_insert (word_subword yx (0,128):int128) (32,32)
          (word_rol (word_subword yx (32,32):int32) 30))) 32`;;

let sha1hash = new_definition
 `sha1hash f (x:int128) (y:int32) (w:int128) : int128 =
    word_subword
     (sha1_round f 3 w (sha1_round f 2 w (sha1_round f 1 w
       (sha1_round f 0 w (word_join y x:160 word))))) (0,128)`;;

let sha1c = new_definition
 `sha1c (d:int128) (n:int128) (m:int128) =
    sha1hash sha_choose d (word_subword n (0,32)) m`;;

let sha1p = new_definition
 `sha1p (d:int128) (n:int128) (m:int128) =
    sha1hash sha1_parity d (word_subword n (0,32)) m`;;

let sha1m = new_definition
 `sha1m (d:int128) (n:int128) (m:int128) =
    sha1hash sha_maj d (word_subword n (0,32)) m`;;

let sha1h = new_definition
 `sha1h (m:int128) : int128 =
    word_zx (word_rol (word_subword m (0,32):int32) 30)`;;

let sha1su0 = new_definition
 `sha1su0 (d:int128) (n:int128) (m:int128) : int128 =
    word_xor d (word_xor (word_join (word_subword n (0,64):int64)
                                    (word_subword d (64,64):int64)) m)`;;

(* T = d EOR LSR(m, 32); each word of T rotates left by one, and the top
   word takes ROL(T<31:0>, 2) too. *)

let sha1su1 = new_definition
 `sha1su1 (d:int128) (m:int128) : int128 =
    word_xor (usimd4 (\x:int32. word_rol x 1) (word_xor d (word_ushr m 32)))
             (word_join (word_rol (word_subword (word_xor d (word_ushr m 32))
                                                (0,32):int32) 2)
                        (word 0:96 word))`;;

(* Reduce each on numerals, a round at a time from the innermost, as the
   extra word conversions the cosimulation applies do arm/proofs/sha256.ml's
   and arm/proofs/utils/aes.ml's. *)

let SHA1_ROUND_RED_CONV =
  let conv =
    REWR_CONV sha1_round THENC
    REWRITE_CONV[sha_choose; sha1_parity; sha_maj] THENC
    DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV) in
  fun tm ->
    match tm with
      Comb(Comb(Comb(Comb(Const("sha1_round",_),_),e),
                Comb(Const("word",_),w)),Comb(Const("word",_),yx))
        when is_numeral e && is_numeral w && is_numeral yx -> conv tm
    | _ -> failwith "SHA1_ROUND_RED_CONV";;

let SHA1_REDUCE_CONV =
  let hash =
    REWR_CONV sha1hash THENC
    DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV ORELSEC
               SHA1_ROUND_RED_CONV) in
  let convs =
    ["sha1c",(REWR_CONV sha1c THENC hash);
     "sha1p",(REWR_CONV sha1p THENC hash);
     "sha1m",(REWR_CONV sha1m THENC hash);
     "sha1h",(REWR_CONV sha1h THENC WORD_REDUCE_CONV);
     "sha1su0",(REWR_CONV sha1su0 THENC WORD_REDUCE_CONV);
     "sha1su1",(REWR_CONV sha1su1 THENC
                REWRITE_CONV[usimd4; usimd2] THENC
                DEPTH_CONV DIMINDEX_CONV THENC
                TOP_DEPTH_CONV BETA_CONV THENC WORD_REDUCE_CONV)] in
  let is_wordlit t =
    match t with
      Comb(Const("word",_),n) -> is_numeral n
    | _ -> false in
  fun tm ->
    let f,args = strip_comb tm in
    match f with
      Const(name,_) when can (assoc name) convs && args <> [] &&
                         forall is_wordlit args ->
        assoc name convs tm
    | _ -> failwith "SHA1_REDUCE_CONV";;
