(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES on the AES-NI instructions, and AES-CTR's 32-bit counter blocks, which *)
(* rind's proofs of aws-lc's AES-CTR and AES-CBC routines state results in.   *)
(* ========================================================================= *)

(* aes_hw_encrypt ks b is the cipher of the block b under the round keys
   ks = [k0; ...; kn], each a 128-bit word read little-endian from memory as
   aws-lc's AES_KEY holds them: b XOR k0, AESENC with k1 to k(n-1), then
   AESENCLAST with kn, which s2n-bignum's x86/proofs/aes.ml defines as Intel's
   manual does. aes_hw_decrypt is the same with AESDEC and AESDECLAST, FIPS
   197's equivalent inverse cipher on the round keys aws-lc's
   aes_hw_set_decrypt_key writes. That these are FIPS 197's cipher and inverse
   cipher of the key rind expanded is proven in Lean, over rind's models of the
   same instructions (Rind/X86_64/AesKey.lean). *)

needs "x86/proofs/base.ml";;

let aes_hw_rounds = define
 `(!s:int128. aes_hw_rounds [] s = s) /\
  (!k ks s:int128. aes_hw_rounds (CONS k ks) s = aes_hw_rounds ks (aesenc s k))`;;

let aes_hw_encrypt = new_definition
 `aes_hw_encrypt (ks:int128 list) (b:int128) =
    aesenclast (aes_hw_rounds (BUTLAST (TL ks)) (word_xor b (HD ks))) (LAST ks)`;;

let aes_hw_dec_rounds = define
 `(!s:int128. aes_hw_dec_rounds [] s = s) /\
  (!k ks s:int128. aes_hw_dec_rounds (CONS k ks) s =
                   aes_hw_dec_rounds ks (aesdec s k))`;;

let aes_hw_decrypt = new_definition
 `aes_hw_decrypt (ks:int128 list) (b:int128) =
    aesdeclast (aes_hw_dec_rounds (BUTLAST (TL ks)) (word_xor b (HD ks)))
               (LAST ks)`;;

(* The counter block i after iv, as aws-lc's CTR32 routines count: bytes 12 to
   15 of the block, its top 32 bits read little-endian, are a big-endian
   counter that adds i modulo 2^32; the other 12 bytes stay. *)
let aes_ctr32_block = new_definition
 `aes_ctr32_block (iv:int128) (i:num) : int128 =
    word_join
      (word_bytereverse
         (word_add (word_bytereverse (word_subword iv (96,32):int32))
                   (word i)):int32)
      (word_subword iv (0,96):96 word)`;;
