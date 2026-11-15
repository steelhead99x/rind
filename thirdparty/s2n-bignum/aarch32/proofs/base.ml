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

loadt "aarch32/proofs/instruction.ml";;
loadt "aarch32/proofs/decode.ml";;
loadt "aarch32/proofs/aarch32.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

loadt "common/wordlist.ml";;
