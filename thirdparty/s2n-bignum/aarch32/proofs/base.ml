(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Load basic background needed for the A32 proofs.                          *)
(* ========================================================================= *)

loads "update_database.ml";;
prioritize_num();;

needs "Library/iter.ml";;
needs "Library/rstc.ml";;
needs "Library/bitsize.ml";;
needs "Library/pocklington.ml";;
needs "Library/integer.ml";;
needs "Library/words.ml";;
needs "Library/bitmatch.ml";;
loadt "Library/records.ml";;

loadt "common/overlap.ml";;
loadt "common/for_hollight.ml";;
loadt "common/words2.ml";;
loadt "common/misc.ml";;
loadt "common/components.ml";;
loadt "common/alignment.ml";;
loadt "common/relational.ml";;
loadt "common/interval.ml";;
loadt "common/elf.ml";;
loadt "common/safety.ml";;
loadt "common/execution.ml";;

(* The crypto extension's AES rounds and SHA-256 steps are the aarch64
   model's, and its SHA-1 steps this model's own. *)

loadt "arm/proofs/sha256.ml";;
loadt "arm/proofs/utils/aes.ml";;
loadt "aarch32/proofs/sha1.ml";;

extra_word_CONV :=
  [SHA256H_REDUCE_CONV; SHA256H2_REDUCE_CONV; SHA256SU0_REDUCE_CONV;
   SHA256SU1_REDUCE_CONV; AESE_REDUCE_CONV; AESMC_REDUCE_CONV;
   AESD_REDUCE_CONV; AESIMC_REDUCE_CONV; SHA1_REDUCE_CONV] @
  !extra_word_CONV;;

loadt "aarch32/proofs/instruction.ml";;
loadt "aarch32/proofs/decode.ml";;
loadt "aarch32/proofs/aarch32.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

loadt "common/wordlist.ml";;
