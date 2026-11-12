(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA-512 block compression with the Armv8.2 SHA-512 instructions, as       *)
(* rind's build emits it.                                                    *)
(* ========================================================================= *)

(* rind's naked function low::aarch64::sha512::sha512_block_data_order_hw is
   aws-lc's sha512_block_data_order_hw (crypto/fipsmodule/sha/asm/
   sha512-armv8.pl, the ARMv8.2 path), which reads its round constants from
   the K512 table beside it. Its result is s2n-bignum's FIPS 180-4 spec,
   sha512_hash_blocks, from s2n-bignum pull request #420, which
   proofs/hol-light/s2n-bignum/ holds until it merges. The loop body runs the
   80 rounds as 40 steps of two, each a SHA512H/SHA512H2 pair whose working
   state rotates through five registers, and the message schedule as 32
   SHA512SU0/SHA512SU1 pairs. The proof steps it symbolically, rewriting each
   step to the spec's rounds and schedule words as it goes, so no case split
   on the data is needed. *)

needs "arm/proofs/base.ml";;
needs "x86/proofs/utils/sha512_spec.ml";;

(* admin/prove writes the function's object, as rind's release build emits
   it, to aarch64/sha512_block_data_order_hw.o: its instructions as .text,
   with relocations, and the K512 table as .rodata. The definition fails
   unless the instructions and relocations are these, and sha512_hw_k512 is
   the table's bytes, which SHA512_HW_K512_PAIRS checks against FIPS 180-4's
   constants. *)
let sha512_hw_mc,sha512_hw_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(fun _ -> "sha512_hw_k512")
    "sha512_hw_mc" "aarch64/sha512_block_data_order_hw.o"
(fun w BL ADR ADRP ADD_rri64 -> [
  w 0xa9bf7bfd;         (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  w 0x910003fd;         (* arm_ADD X29 SP (rvalue (word 0)) *)
  w 0x4cdf2030;         (* arm_LDP4 Q16 Q17 Q18 Q19 X1 (Postimmediate_Offset (word 64)) *)
  w 0x4cdf2034;         (* arm_LDP4 Q20 Q21 Q22 Q23 X1 (Postimmediate_Offset (word 64)) *)
  w 0x4c402c00;         (* arm_LDP4 Q0 Q1 Q2 Q3 X0 No_Offset *)
  ADRP (mk_var("sha512_hw_k512",`:num`),0,20,3);
  ADD_rri64 (mk_var("sha512_hw_k512",`:num`),0,3,3);
  w 0x4e200a10;         (* arm_REV64_VEC Q16 Q16 8 *)
  w 0x4e200a31;         (* arm_REV64_VEC Q17 Q17 8 *)
  w 0x4e200a52;         (* arm_REV64_VEC Q18 Q18 8 *)
  w 0x4e200a73;         (* arm_REV64_VEC Q19 Q19 8 *)
  w 0x4e200a94;         (* arm_REV64_VEC Q20 Q20 8 *)
  w 0x4e200ab5;         (* arm_REV64_VEC Q21 Q21 8 *)
  w 0x4e200ad6;         (* arm_REV64_VEC Q22 Q22 8 *)
  w 0x4e200af7;         (* arm_REV64_VEC Q23 Q23 8 *)
  w 0x14000001;         (* arm_B (word 4) *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0xf1000442;         (* arm_SUBS X2 X2 (rvalue (word 1)) *)
  w 0xd1020024;         (* arm_SUB X4 X1 (rvalue (word 128)) *)
  w 0x4ea01c1a;         (* arm_MOV_VEC Q26 Q0 128 *)
  w 0x4ea11c3b;         (* arm_MOV_VEC Q27 Q1 128 *)
  w 0x4ea21c5c;         (* arm_MOV_VEC Q28 Q2 128 *)
  w 0x4ea31c7d;         (* arm_MOV_VEC Q29 Q3 128 *)
  w 0x9a841021;         (* arm_CSEL X1 X1 X4 Condition_NE *)
  w 0x4ef08718;         (* arm_ADD_VEC Q24 Q24 Q16 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e034045;         (* arm_EXT Q5 Q2 Q3 64 *)
  w 0x6e024026;         (* arm_EXT Q6 Q1 Q2 64 *)
  w 0x4ef88463;         (* arm_ADD_VEC Q3 Q3 Q24 64 128 *)
  w 0xcec08230;         (* arm_SHA512SU0 Q16 Q17 *)
  w 0x6e154287;         (* arm_EXT Q7 Q20 Q21 64 *)
  w 0xce6680a3;         (* arm_SHA512H Q3 Q5 Q6 *)
  w 0xce678af0;         (* arm_SHA512SU1 Q16 Q23 Q7 *)
  w 0x4ee38424;         (* arm_ADD_VEC Q4 Q1 Q3 64 128 *)
  w 0xce608423;         (* arm_SHA512H2 Q3 Q1 Q0 *)
  w 0x4ef18739;         (* arm_ADD_VEC Q25 Q25 Q17 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e024085;         (* arm_EXT Q5 Q4 Q2 64 *)
  w 0x6e044006;         (* arm_EXT Q6 Q0 Q4 64 *)
  w 0x4ef98442;         (* arm_ADD_VEC Q2 Q2 Q25 64 128 *)
  w 0xcec08251;         (* arm_SHA512SU0 Q17 Q18 *)
  w 0x6e1642a7;         (* arm_EXT Q7 Q21 Q22 64 *)
  w 0xce6680a2;         (* arm_SHA512H Q2 Q5 Q6 *)
  w 0xce678a11;         (* arm_SHA512SU1 Q17 Q16 Q7 *)
  w 0x4ee28401;         (* arm_ADD_VEC Q1 Q0 Q2 64 128 *)
  w 0xce638402;         (* arm_SHA512H2 Q2 Q0 Q3 *)
  w 0x4ef28718;         (* arm_ADD_VEC Q24 Q24 Q18 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e044025;         (* arm_EXT Q5 Q1 Q4 64 *)
  w 0x6e014066;         (* arm_EXT Q6 Q3 Q1 64 *)
  w 0x4ef88484;         (* arm_ADD_VEC Q4 Q4 Q24 64 128 *)
  w 0xcec08272;         (* arm_SHA512SU0 Q18 Q19 *)
  w 0x6e1742c7;         (* arm_EXT Q7 Q22 Q23 64 *)
  w 0xce6680a4;         (* arm_SHA512H Q4 Q5 Q6 *)
  w 0xce678a32;         (* arm_SHA512SU1 Q18 Q17 Q7 *)
  w 0x4ee48460;         (* arm_ADD_VEC Q0 Q3 Q4 64 128 *)
  w 0xce628464;         (* arm_SHA512H2 Q4 Q3 Q2 *)
  w 0x4ef38739;         (* arm_ADD_VEC Q25 Q25 Q19 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e014005;         (* arm_EXT Q5 Q0 Q1 64 *)
  w 0x6e004046;         (* arm_EXT Q6 Q2 Q0 64 *)
  w 0x4ef98421;         (* arm_ADD_VEC Q1 Q1 Q25 64 128 *)
  w 0xcec08293;         (* arm_SHA512SU0 Q19 Q20 *)
  w 0x6e1042e7;         (* arm_EXT Q7 Q23 Q16 64 *)
  w 0xce6680a1;         (* arm_SHA512H Q1 Q5 Q6 *)
  w 0xce678a53;         (* arm_SHA512SU1 Q19 Q18 Q7 *)
  w 0x4ee18443;         (* arm_ADD_VEC Q3 Q2 Q1 64 128 *)
  w 0xce648441;         (* arm_SHA512H2 Q1 Q2 Q4 *)
  w 0x4ef48718;         (* arm_ADD_VEC Q24 Q24 Q20 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e004065;         (* arm_EXT Q5 Q3 Q0 64 *)
  w 0x6e034086;         (* arm_EXT Q6 Q4 Q3 64 *)
  w 0x4ef88400;         (* arm_ADD_VEC Q0 Q0 Q24 64 128 *)
  w 0xcec082b4;         (* arm_SHA512SU0 Q20 Q21 *)
  w 0x6e114207;         (* arm_EXT Q7 Q16 Q17 64 *)
  w 0xce6680a0;         (* arm_SHA512H Q0 Q5 Q6 *)
  w 0xce678a74;         (* arm_SHA512SU1 Q20 Q19 Q7 *)
  w 0x4ee08482;         (* arm_ADD_VEC Q2 Q4 Q0 64 128 *)
  w 0xce618480;         (* arm_SHA512H2 Q0 Q4 Q1 *)
  w 0x4ef58739;         (* arm_ADD_VEC Q25 Q25 Q21 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e034045;         (* arm_EXT Q5 Q2 Q3 64 *)
  w 0x6e024026;         (* arm_EXT Q6 Q1 Q2 64 *)
  w 0x4ef98463;         (* arm_ADD_VEC Q3 Q3 Q25 64 128 *)
  w 0xcec082d5;         (* arm_SHA512SU0 Q21 Q22 *)
  w 0x6e124227;         (* arm_EXT Q7 Q17 Q18 64 *)
  w 0xce6680a3;         (* arm_SHA512H Q3 Q5 Q6 *)
  w 0xce678a95;         (* arm_SHA512SU1 Q21 Q20 Q7 *)
  w 0x4ee38424;         (* arm_ADD_VEC Q4 Q1 Q3 64 128 *)
  w 0xce608423;         (* arm_SHA512H2 Q3 Q1 Q0 *)
  w 0x4ef68718;         (* arm_ADD_VEC Q24 Q24 Q22 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e024085;         (* arm_EXT Q5 Q4 Q2 64 *)
  w 0x6e044006;         (* arm_EXT Q6 Q0 Q4 64 *)
  w 0x4ef88442;         (* arm_ADD_VEC Q2 Q2 Q24 64 128 *)
  w 0xcec082f6;         (* arm_SHA512SU0 Q22 Q23 *)
  w 0x6e134247;         (* arm_EXT Q7 Q18 Q19 64 *)
  w 0xce6680a2;         (* arm_SHA512H Q2 Q5 Q6 *)
  w 0xce678ab6;         (* arm_SHA512SU1 Q22 Q21 Q7 *)
  w 0x4ee28401;         (* arm_ADD_VEC Q1 Q0 Q2 64 128 *)
  w 0xce638402;         (* arm_SHA512H2 Q2 Q0 Q3 *)
  w 0x4ef78739;         (* arm_ADD_VEC Q25 Q25 Q23 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e044025;         (* arm_EXT Q5 Q1 Q4 64 *)
  w 0x6e014066;         (* arm_EXT Q6 Q3 Q1 64 *)
  w 0x4ef98484;         (* arm_ADD_VEC Q4 Q4 Q25 64 128 *)
  w 0xcec08217;         (* arm_SHA512SU0 Q23 Q16 *)
  w 0x6e144267;         (* arm_EXT Q7 Q19 Q20 64 *)
  w 0xce6680a4;         (* arm_SHA512H Q4 Q5 Q6 *)
  w 0xce678ad7;         (* arm_SHA512SU1 Q23 Q22 Q7 *)
  w 0x4ee48460;         (* arm_ADD_VEC Q0 Q3 Q4 64 128 *)
  w 0xce628464;         (* arm_SHA512H2 Q4 Q3 Q2 *)
  w 0x4ef08718;         (* arm_ADD_VEC Q24 Q24 Q16 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e014005;         (* arm_EXT Q5 Q0 Q1 64 *)
  w 0x6e004046;         (* arm_EXT Q6 Q2 Q0 64 *)
  w 0x4ef88421;         (* arm_ADD_VEC Q1 Q1 Q24 64 128 *)
  w 0xcec08230;         (* arm_SHA512SU0 Q16 Q17 *)
  w 0x6e154287;         (* arm_EXT Q7 Q20 Q21 64 *)
  w 0xce6680a1;         (* arm_SHA512H Q1 Q5 Q6 *)
  w 0xce678af0;         (* arm_SHA512SU1 Q16 Q23 Q7 *)
  w 0x4ee18443;         (* arm_ADD_VEC Q3 Q2 Q1 64 128 *)
  w 0xce648441;         (* arm_SHA512H2 Q1 Q2 Q4 *)
  w 0x4ef18739;         (* arm_ADD_VEC Q25 Q25 Q17 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e004065;         (* arm_EXT Q5 Q3 Q0 64 *)
  w 0x6e034086;         (* arm_EXT Q6 Q4 Q3 64 *)
  w 0x4ef98400;         (* arm_ADD_VEC Q0 Q0 Q25 64 128 *)
  w 0xcec08251;         (* arm_SHA512SU0 Q17 Q18 *)
  w 0x6e1642a7;         (* arm_EXT Q7 Q21 Q22 64 *)
  w 0xce6680a0;         (* arm_SHA512H Q0 Q5 Q6 *)
  w 0xce678a11;         (* arm_SHA512SU1 Q17 Q16 Q7 *)
  w 0x4ee08482;         (* arm_ADD_VEC Q2 Q4 Q0 64 128 *)
  w 0xce618480;         (* arm_SHA512H2 Q0 Q4 Q1 *)
  w 0x4ef28718;         (* arm_ADD_VEC Q24 Q24 Q18 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e034045;         (* arm_EXT Q5 Q2 Q3 64 *)
  w 0x6e024026;         (* arm_EXT Q6 Q1 Q2 64 *)
  w 0x4ef88463;         (* arm_ADD_VEC Q3 Q3 Q24 64 128 *)
  w 0xcec08272;         (* arm_SHA512SU0 Q18 Q19 *)
  w 0x6e1742c7;         (* arm_EXT Q7 Q22 Q23 64 *)
  w 0xce6680a3;         (* arm_SHA512H Q3 Q5 Q6 *)
  w 0xce678a32;         (* arm_SHA512SU1 Q18 Q17 Q7 *)
  w 0x4ee38424;         (* arm_ADD_VEC Q4 Q1 Q3 64 128 *)
  w 0xce608423;         (* arm_SHA512H2 Q3 Q1 Q0 *)
  w 0x4ef38739;         (* arm_ADD_VEC Q25 Q25 Q19 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e024085;         (* arm_EXT Q5 Q4 Q2 64 *)
  w 0x6e044006;         (* arm_EXT Q6 Q0 Q4 64 *)
  w 0x4ef98442;         (* arm_ADD_VEC Q2 Q2 Q25 64 128 *)
  w 0xcec08293;         (* arm_SHA512SU0 Q19 Q20 *)
  w 0x6e1042e7;         (* arm_EXT Q7 Q23 Q16 64 *)
  w 0xce6680a2;         (* arm_SHA512H Q2 Q5 Q6 *)
  w 0xce678a53;         (* arm_SHA512SU1 Q19 Q18 Q7 *)
  w 0x4ee28401;         (* arm_ADD_VEC Q1 Q0 Q2 64 128 *)
  w 0xce638402;         (* arm_SHA512H2 Q2 Q0 Q3 *)
  w 0x4ef48718;         (* arm_ADD_VEC Q24 Q24 Q20 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e044025;         (* arm_EXT Q5 Q1 Q4 64 *)
  w 0x6e014066;         (* arm_EXT Q6 Q3 Q1 64 *)
  w 0x4ef88484;         (* arm_ADD_VEC Q4 Q4 Q24 64 128 *)
  w 0xcec082b4;         (* arm_SHA512SU0 Q20 Q21 *)
  w 0x6e114207;         (* arm_EXT Q7 Q16 Q17 64 *)
  w 0xce6680a4;         (* arm_SHA512H Q4 Q5 Q6 *)
  w 0xce678a74;         (* arm_SHA512SU1 Q20 Q19 Q7 *)
  w 0x4ee48460;         (* arm_ADD_VEC Q0 Q3 Q4 64 128 *)
  w 0xce628464;         (* arm_SHA512H2 Q4 Q3 Q2 *)
  w 0x4ef58739;         (* arm_ADD_VEC Q25 Q25 Q21 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e014005;         (* arm_EXT Q5 Q0 Q1 64 *)
  w 0x6e004046;         (* arm_EXT Q6 Q2 Q0 64 *)
  w 0x4ef98421;         (* arm_ADD_VEC Q1 Q1 Q25 64 128 *)
  w 0xcec082d5;         (* arm_SHA512SU0 Q21 Q22 *)
  w 0x6e124227;         (* arm_EXT Q7 Q17 Q18 64 *)
  w 0xce6680a1;         (* arm_SHA512H Q1 Q5 Q6 *)
  w 0xce678a95;         (* arm_SHA512SU1 Q21 Q20 Q7 *)
  w 0x4ee18443;         (* arm_ADD_VEC Q3 Q2 Q1 64 128 *)
  w 0xce648441;         (* arm_SHA512H2 Q1 Q2 Q4 *)
  w 0x4ef68718;         (* arm_ADD_VEC Q24 Q24 Q22 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e004065;         (* arm_EXT Q5 Q3 Q0 64 *)
  w 0x6e034086;         (* arm_EXT Q6 Q4 Q3 64 *)
  w 0x4ef88400;         (* arm_ADD_VEC Q0 Q0 Q24 64 128 *)
  w 0xcec082f6;         (* arm_SHA512SU0 Q22 Q23 *)
  w 0x6e134247;         (* arm_EXT Q7 Q18 Q19 64 *)
  w 0xce6680a0;         (* arm_SHA512H Q0 Q5 Q6 *)
  w 0xce678ab6;         (* arm_SHA512SU1 Q22 Q21 Q7 *)
  w 0x4ee08482;         (* arm_ADD_VEC Q2 Q4 Q0 64 128 *)
  w 0xce618480;         (* arm_SHA512H2 Q0 Q4 Q1 *)
  w 0x4ef78739;         (* arm_ADD_VEC Q25 Q25 Q23 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e034045;         (* arm_EXT Q5 Q2 Q3 64 *)
  w 0x6e024026;         (* arm_EXT Q6 Q1 Q2 64 *)
  w 0x4ef98463;         (* arm_ADD_VEC Q3 Q3 Q25 64 128 *)
  w 0xcec08217;         (* arm_SHA512SU0 Q23 Q16 *)
  w 0x6e144267;         (* arm_EXT Q7 Q19 Q20 64 *)
  w 0xce6680a3;         (* arm_SHA512H Q3 Q5 Q6 *)
  w 0xce678ad7;         (* arm_SHA512SU1 Q23 Q22 Q7 *)
  w 0x4ee38424;         (* arm_ADD_VEC Q4 Q1 Q3 64 128 *)
  w 0xce608423;         (* arm_SHA512H2 Q3 Q1 Q0 *)
  w 0x4ef08718;         (* arm_ADD_VEC Q24 Q24 Q16 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e024085;         (* arm_EXT Q5 Q4 Q2 64 *)
  w 0x6e044006;         (* arm_EXT Q6 Q0 Q4 64 *)
  w 0x4ef88442;         (* arm_ADD_VEC Q2 Q2 Q24 64 128 *)
  w 0xcec08230;         (* arm_SHA512SU0 Q16 Q17 *)
  w 0x6e154287;         (* arm_EXT Q7 Q20 Q21 64 *)
  w 0xce6680a2;         (* arm_SHA512H Q2 Q5 Q6 *)
  w 0xce678af0;         (* arm_SHA512SU1 Q16 Q23 Q7 *)
  w 0x4ee28401;         (* arm_ADD_VEC Q1 Q0 Q2 64 128 *)
  w 0xce638402;         (* arm_SHA512H2 Q2 Q0 Q3 *)
  w 0x4ef18739;         (* arm_ADD_VEC Q25 Q25 Q17 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e044025;         (* arm_EXT Q5 Q1 Q4 64 *)
  w 0x6e014066;         (* arm_EXT Q6 Q3 Q1 64 *)
  w 0x4ef98484;         (* arm_ADD_VEC Q4 Q4 Q25 64 128 *)
  w 0xcec08251;         (* arm_SHA512SU0 Q17 Q18 *)
  w 0x6e1642a7;         (* arm_EXT Q7 Q21 Q22 64 *)
  w 0xce6680a4;         (* arm_SHA512H Q4 Q5 Q6 *)
  w 0xce678a11;         (* arm_SHA512SU1 Q17 Q16 Q7 *)
  w 0x4ee48460;         (* arm_ADD_VEC Q0 Q3 Q4 64 128 *)
  w 0xce628464;         (* arm_SHA512H2 Q4 Q3 Q2 *)
  w 0x4ef28718;         (* arm_ADD_VEC Q24 Q24 Q18 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e014005;         (* arm_EXT Q5 Q0 Q1 64 *)
  w 0x6e004046;         (* arm_EXT Q6 Q2 Q0 64 *)
  w 0x4ef88421;         (* arm_ADD_VEC Q1 Q1 Q24 64 128 *)
  w 0xcec08272;         (* arm_SHA512SU0 Q18 Q19 *)
  w 0x6e1742c7;         (* arm_EXT Q7 Q22 Q23 64 *)
  w 0xce6680a1;         (* arm_SHA512H Q1 Q5 Q6 *)
  w 0xce678a32;         (* arm_SHA512SU1 Q18 Q17 Q7 *)
  w 0x4ee18443;         (* arm_ADD_VEC Q3 Q2 Q1 64 128 *)
  w 0xce648441;         (* arm_SHA512H2 Q1 Q2 Q4 *)
  w 0x4ef38739;         (* arm_ADD_VEC Q25 Q25 Q19 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e004065;         (* arm_EXT Q5 Q3 Q0 64 *)
  w 0x6e034086;         (* arm_EXT Q6 Q4 Q3 64 *)
  w 0x4ef98400;         (* arm_ADD_VEC Q0 Q0 Q25 64 128 *)
  w 0xcec08293;         (* arm_SHA512SU0 Q19 Q20 *)
  w 0x6e1042e7;         (* arm_EXT Q7 Q23 Q16 64 *)
  w 0xce6680a0;         (* arm_SHA512H Q0 Q5 Q6 *)
  w 0xce678a53;         (* arm_SHA512SU1 Q19 Q18 Q7 *)
  w 0x4ee08482;         (* arm_ADD_VEC Q2 Q4 Q0 64 128 *)
  w 0xce618480;         (* arm_SHA512H2 Q0 Q4 Q1 *)
  w 0x4ef48718;         (* arm_ADD_VEC Q24 Q24 Q20 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e034045;         (* arm_EXT Q5 Q2 Q3 64 *)
  w 0x6e024026;         (* arm_EXT Q6 Q1 Q2 64 *)
  w 0x4ef88463;         (* arm_ADD_VEC Q3 Q3 Q24 64 128 *)
  w 0xcec082b4;         (* arm_SHA512SU0 Q20 Q21 *)
  w 0x6e114207;         (* arm_EXT Q7 Q16 Q17 64 *)
  w 0xce6680a3;         (* arm_SHA512H Q3 Q5 Q6 *)
  w 0xce678a74;         (* arm_SHA512SU1 Q20 Q19 Q7 *)
  w 0x4ee38424;         (* arm_ADD_VEC Q4 Q1 Q3 64 128 *)
  w 0xce608423;         (* arm_SHA512H2 Q3 Q1 Q0 *)
  w 0x4ef58739;         (* arm_ADD_VEC Q25 Q25 Q21 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e024085;         (* arm_EXT Q5 Q4 Q2 64 *)
  w 0x6e044006;         (* arm_EXT Q6 Q0 Q4 64 *)
  w 0x4ef98442;         (* arm_ADD_VEC Q2 Q2 Q25 64 128 *)
  w 0xcec082d5;         (* arm_SHA512SU0 Q21 Q22 *)
  w 0x6e124227;         (* arm_EXT Q7 Q17 Q18 64 *)
  w 0xce6680a2;         (* arm_SHA512H Q2 Q5 Q6 *)
  w 0xce678a95;         (* arm_SHA512SU1 Q21 Q20 Q7 *)
  w 0x4ee28401;         (* arm_ADD_VEC Q1 Q0 Q2 64 128 *)
  w 0xce638402;         (* arm_SHA512H2 Q2 Q0 Q3 *)
  w 0x4ef68718;         (* arm_ADD_VEC Q24 Q24 Q22 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e044025;         (* arm_EXT Q5 Q1 Q4 64 *)
  w 0x6e014066;         (* arm_EXT Q6 Q3 Q1 64 *)
  w 0x4ef88484;         (* arm_ADD_VEC Q4 Q4 Q24 64 128 *)
  w 0xcec082f6;         (* arm_SHA512SU0 Q22 Q23 *)
  w 0x6e134247;         (* arm_EXT Q7 Q18 Q19 64 *)
  w 0xce6680a4;         (* arm_SHA512H Q4 Q5 Q6 *)
  w 0xce678ab6;         (* arm_SHA512SU1 Q22 Q21 Q7 *)
  w 0x4ee48460;         (* arm_ADD_VEC Q0 Q3 Q4 64 128 *)
  w 0xce628464;         (* arm_SHA512H2 Q4 Q3 Q2 *)
  w 0x4ef78739;         (* arm_ADD_VEC Q25 Q25 Q23 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e014005;         (* arm_EXT Q5 Q0 Q1 64 *)
  w 0x6e004046;         (* arm_EXT Q6 Q2 Q0 64 *)
  w 0x4ef98421;         (* arm_ADD_VEC Q1 Q1 Q25 64 128 *)
  w 0xcec08217;         (* arm_SHA512SU0 Q23 Q16 *)
  w 0x6e144267;         (* arm_EXT Q7 Q19 Q20 64 *)
  w 0xce6680a1;         (* arm_SHA512H Q1 Q5 Q6 *)
  w 0xce678ad7;         (* arm_SHA512SU1 Q23 Q22 Q7 *)
  w 0x4ee18443;         (* arm_ADD_VEC Q3 Q2 Q1 64 128 *)
  w 0xce648441;         (* arm_SHA512H2 Q1 Q2 Q4 *)
  w 0x4ef08718;         (* arm_ADD_VEC Q24 Q24 Q16 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e004065;         (* arm_EXT Q5 Q3 Q0 64 *)
  w 0x6e034086;         (* arm_EXT Q6 Q4 Q3 64 *)
  w 0x4ef88400;         (* arm_ADD_VEC Q0 Q0 Q24 64 128 *)
  w 0xcec08230;         (* arm_SHA512SU0 Q16 Q17 *)
  w 0x6e154287;         (* arm_EXT Q7 Q20 Q21 64 *)
  w 0xce6680a0;         (* arm_SHA512H Q0 Q5 Q6 *)
  w 0xce678af0;         (* arm_SHA512SU1 Q16 Q23 Q7 *)
  w 0x4ee08482;         (* arm_ADD_VEC Q2 Q4 Q0 64 128 *)
  w 0xce618480;         (* arm_SHA512H2 Q0 Q4 Q1 *)
  w 0x4ef18739;         (* arm_ADD_VEC Q25 Q25 Q17 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e034045;         (* arm_EXT Q5 Q2 Q3 64 *)
  w 0x6e024026;         (* arm_EXT Q6 Q1 Q2 64 *)
  w 0x4ef98463;         (* arm_ADD_VEC Q3 Q3 Q25 64 128 *)
  w 0xcec08251;         (* arm_SHA512SU0 Q17 Q18 *)
  w 0x6e1642a7;         (* arm_EXT Q7 Q21 Q22 64 *)
  w 0xce6680a3;         (* arm_SHA512H Q3 Q5 Q6 *)
  w 0xce678a11;         (* arm_SHA512SU1 Q17 Q16 Q7 *)
  w 0x4ee38424;         (* arm_ADD_VEC Q4 Q1 Q3 64 128 *)
  w 0xce608423;         (* arm_SHA512H2 Q3 Q1 Q0 *)
  w 0x4ef28718;         (* arm_ADD_VEC Q24 Q24 Q18 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e024085;         (* arm_EXT Q5 Q4 Q2 64 *)
  w 0x6e044006;         (* arm_EXT Q6 Q0 Q4 64 *)
  w 0x4ef88442;         (* arm_ADD_VEC Q2 Q2 Q24 64 128 *)
  w 0xcec08272;         (* arm_SHA512SU0 Q18 Q19 *)
  w 0x6e1742c7;         (* arm_EXT Q7 Q22 Q23 64 *)
  w 0xce6680a2;         (* arm_SHA512H Q2 Q5 Q6 *)
  w 0xce678a32;         (* arm_SHA512SU1 Q18 Q17 Q7 *)
  w 0x4ee28401;         (* arm_ADD_VEC Q1 Q0 Q2 64 128 *)
  w 0xce638402;         (* arm_SHA512H2 Q2 Q0 Q3 *)
  w 0x4ef38739;         (* arm_ADD_VEC Q25 Q25 Q19 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e044025;         (* arm_EXT Q5 Q1 Q4 64 *)
  w 0x6e014066;         (* arm_EXT Q6 Q3 Q1 64 *)
  w 0x4ef98484;         (* arm_ADD_VEC Q4 Q4 Q25 64 128 *)
  w 0xcec08293;         (* arm_SHA512SU0 Q19 Q20 *)
  w 0x6e1042e7;         (* arm_EXT Q7 Q23 Q16 64 *)
  w 0xce6680a4;         (* arm_SHA512H Q4 Q5 Q6 *)
  w 0xce678a53;         (* arm_SHA512SU1 Q19 Q18 Q7 *)
  w 0x4ee48460;         (* arm_ADD_VEC Q0 Q3 Q4 64 128 *)
  w 0xce628464;         (* arm_SHA512H2 Q4 Q3 Q2 *)
  w 0x4ef48718;         (* arm_ADD_VEC Q24 Q24 Q20 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e014005;         (* arm_EXT Q5 Q0 Q1 64 *)
  w 0x6e004046;         (* arm_EXT Q6 Q2 Q0 64 *)
  w 0x4ef88421;         (* arm_ADD_VEC Q1 Q1 Q24 64 128 *)
  w 0xcec082b4;         (* arm_SHA512SU0 Q20 Q21 *)
  w 0x6e114207;         (* arm_EXT Q7 Q16 Q17 64 *)
  w 0xce6680a1;         (* arm_SHA512H Q1 Q5 Q6 *)
  w 0xce678a74;         (* arm_SHA512SU1 Q20 Q19 Q7 *)
  w 0x4ee18443;         (* arm_ADD_VEC Q3 Q2 Q1 64 128 *)
  w 0xce648441;         (* arm_SHA512H2 Q1 Q2 Q4 *)
  w 0x4ef58739;         (* arm_ADD_VEC Q25 Q25 Q21 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e004065;         (* arm_EXT Q5 Q3 Q0 64 *)
  w 0x6e034086;         (* arm_EXT Q6 Q4 Q3 64 *)
  w 0x4ef98400;         (* arm_ADD_VEC Q0 Q0 Q25 64 128 *)
  w 0xcec082d5;         (* arm_SHA512SU0 Q21 Q22 *)
  w 0x6e124227;         (* arm_EXT Q7 Q17 Q18 64 *)
  w 0xce6680a0;         (* arm_SHA512H Q0 Q5 Q6 *)
  w 0xce678a95;         (* arm_SHA512SU1 Q21 Q20 Q7 *)
  w 0x4ee08482;         (* arm_ADD_VEC Q2 Q4 Q0 64 128 *)
  w 0xce618480;         (* arm_SHA512H2 Q0 Q4 Q1 *)
  w 0x4ef68718;         (* arm_ADD_VEC Q24 Q24 Q22 64 128 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e034045;         (* arm_EXT Q5 Q2 Q3 64 *)
  w 0x6e024026;         (* arm_EXT Q6 Q1 Q2 64 *)
  w 0x4ef88463;         (* arm_ADD_VEC Q3 Q3 Q24 64 128 *)
  w 0xcec082f6;         (* arm_SHA512SU0 Q22 Q23 *)
  w 0x6e134247;         (* arm_EXT Q7 Q18 Q19 64 *)
  w 0xce6680a3;         (* arm_SHA512H Q3 Q5 Q6 *)
  w 0xce678ab6;         (* arm_SHA512SU1 Q22 Q21 Q7 *)
  w 0x4ee38424;         (* arm_ADD_VEC Q4 Q1 Q3 64 128 *)
  w 0xce608423;         (* arm_SHA512H2 Q3 Q1 Q0 *)
  w 0x4ef78739;         (* arm_ADD_VEC Q25 Q25 Q23 64 128 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e024085;         (* arm_EXT Q5 Q4 Q2 64 *)
  w 0x6e044006;         (* arm_EXT Q6 Q0 Q4 64 *)
  w 0x4ef98442;         (* arm_ADD_VEC Q2 Q2 Q25 64 128 *)
  w 0xcec08217;         (* arm_SHA512SU0 Q23 Q16 *)
  w 0x6e144267;         (* arm_EXT Q7 Q19 Q20 64 *)
  w 0xce6680a2;         (* arm_SHA512H Q2 Q5 Q6 *)
  w 0xce678ad7;         (* arm_SHA512SU1 Q23 Q22 Q7 *)
  w 0x4ee28401;         (* arm_ADD_VEC Q1 Q0 Q2 64 128 *)
  w 0xce638402;         (* arm_SHA512H2 Q2 Q0 Q3 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ef08718;         (* arm_ADD_VEC Q24 Q24 Q16 64 128 *)
  w 0x4cdf7030;         (* arm_LDR Q16 X1 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e044025;         (* arm_EXT Q5 Q1 Q4 64 *)
  w 0x6e014066;         (* arm_EXT Q6 Q3 Q1 64 *)
  w 0x4ef88484;         (* arm_ADD_VEC Q4 Q4 Q24 64 128 *)
  w 0xce6680a4;         (* arm_SHA512H Q4 Q5 Q6 *)
  w 0x4e200a10;         (* arm_REV64_VEC Q16 Q16 8 *)
  w 0x4ee48460;         (* arm_ADD_VEC Q0 Q3 Q4 64 128 *)
  w 0xce628464;         (* arm_SHA512H2 Q4 Q3 Q2 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ef18739;         (* arm_ADD_VEC Q25 Q25 Q17 64 128 *)
  w 0x4cdf7031;         (* arm_LDR Q17 X1 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e014005;         (* arm_EXT Q5 Q0 Q1 64 *)
  w 0x6e004046;         (* arm_EXT Q6 Q2 Q0 64 *)
  w 0x4ef98421;         (* arm_ADD_VEC Q1 Q1 Q25 64 128 *)
  w 0xce6680a1;         (* arm_SHA512H Q1 Q5 Q6 *)
  w 0x4e200a31;         (* arm_REV64_VEC Q17 Q17 8 *)
  w 0x4ee18443;         (* arm_ADD_VEC Q3 Q2 Q1 64 128 *)
  w 0xce648441;         (* arm_SHA512H2 Q1 Q2 Q4 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ef28718;         (* arm_ADD_VEC Q24 Q24 Q18 64 128 *)
  w 0x4cdf7032;         (* arm_LDR Q18 X1 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e004065;         (* arm_EXT Q5 Q3 Q0 64 *)
  w 0x6e034086;         (* arm_EXT Q6 Q4 Q3 64 *)
  w 0x4ef88400;         (* arm_ADD_VEC Q0 Q0 Q24 64 128 *)
  w 0xce6680a0;         (* arm_SHA512H Q0 Q5 Q6 *)
  w 0x4e200a52;         (* arm_REV64_VEC Q18 Q18 8 *)
  w 0x4ee08482;         (* arm_ADD_VEC Q2 Q4 Q0 64 128 *)
  w 0xce618480;         (* arm_SHA512H2 Q0 Q4 Q1 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ef38739;         (* arm_ADD_VEC Q25 Q25 Q19 64 128 *)
  w 0x4cdf7033;         (* arm_LDR Q19 X1 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e034045;         (* arm_EXT Q5 Q2 Q3 64 *)
  w 0x6e024026;         (* arm_EXT Q6 Q1 Q2 64 *)
  w 0x4ef98463;         (* arm_ADD_VEC Q3 Q3 Q25 64 128 *)
  w 0xce6680a3;         (* arm_SHA512H Q3 Q5 Q6 *)
  w 0x4e200a73;         (* arm_REV64_VEC Q19 Q19 8 *)
  w 0x4ee38424;         (* arm_ADD_VEC Q4 Q1 Q3 64 128 *)
  w 0xce608423;         (* arm_SHA512H2 Q3 Q1 Q0 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ef48718;         (* arm_ADD_VEC Q24 Q24 Q20 64 128 *)
  w 0x4cdf7034;         (* arm_LDR Q20 X1 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e024085;         (* arm_EXT Q5 Q4 Q2 64 *)
  w 0x6e044006;         (* arm_EXT Q6 Q0 Q4 64 *)
  w 0x4ef88442;         (* arm_ADD_VEC Q2 Q2 Q24 64 128 *)
  w 0xce6680a2;         (* arm_SHA512H Q2 Q5 Q6 *)
  w 0x4e200a94;         (* arm_REV64_VEC Q20 Q20 8 *)
  w 0x4ee28401;         (* arm_ADD_VEC Q1 Q0 Q2 64 128 *)
  w 0xce638402;         (* arm_SHA512H2 Q2 Q0 Q3 *)
  w 0x4cdf7c78;         (* arm_LDR Q24 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ef58739;         (* arm_ADD_VEC Q25 Q25 Q21 64 128 *)
  w 0x4cdf7035;         (* arm_LDR Q21 X1 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e044025;         (* arm_EXT Q5 Q1 Q4 64 *)
  w 0x6e014066;         (* arm_EXT Q6 Q3 Q1 64 *)
  w 0x4ef98484;         (* arm_ADD_VEC Q4 Q4 Q25 64 128 *)
  w 0xce6680a4;         (* arm_SHA512H Q4 Q5 Q6 *)
  w 0x4e200ab5;         (* arm_REV64_VEC Q21 Q21 8 *)
  w 0x4ee48460;         (* arm_ADD_VEC Q0 Q3 Q4 64 128 *)
  w 0xce628464;         (* arm_SHA512H2 Q4 Q3 Q2 *)
  w 0x4cdf7c79;         (* arm_LDR Q25 X3 (Postimmediate_Offset (word 16)) *)
  w 0x4ef68718;         (* arm_ADD_VEC Q24 Q24 Q22 64 128 *)
  w 0x4cdf7036;         (* arm_LDR Q22 X1 (Postimmediate_Offset (word 16)) *)
  w 0x6e184318;         (* arm_EXT Q24 Q24 Q24 64 *)
  w 0x6e014005;         (* arm_EXT Q5 Q0 Q1 64 *)
  w 0x6e004046;         (* arm_EXT Q6 Q2 Q0 64 *)
  w 0x4ef88421;         (* arm_ADD_VEC Q1 Q1 Q24 64 128 *)
  w 0xce6680a1;         (* arm_SHA512H Q1 Q5 Q6 *)
  w 0x4e200ad6;         (* arm_REV64_VEC Q22 Q22 8 *)
  w 0x4ee18443;         (* arm_ADD_VEC Q3 Q2 Q1 64 128 *)
  w 0xce648441;         (* arm_SHA512H2 Q1 Q2 Q4 *)
  w 0xd10a0063;         (* arm_SUB X3 X3 (rvalue (word 640)) *)
  w 0x4ef78739;         (* arm_ADD_VEC Q25 Q25 Q23 64 128 *)
  w 0x4cdf7037;         (* arm_LDR Q23 X1 (Postimmediate_Offset (word 16)) *)
  w 0x6e194339;         (* arm_EXT Q25 Q25 Q25 64 *)
  w 0x6e004065;         (* arm_EXT Q5 Q3 Q0 64 *)
  w 0x6e034086;         (* arm_EXT Q6 Q4 Q3 64 *)
  w 0x4ef98400;         (* arm_ADD_VEC Q0 Q0 Q25 64 128 *)
  w 0xce6680a0;         (* arm_SHA512H Q0 Q5 Q6 *)
  w 0x4e200af7;         (* arm_REV64_VEC Q23 Q23 8 *)
  w 0x4ee08482;         (* arm_ADD_VEC Q2 Q4 Q0 64 128 *)
  w 0xce618480;         (* arm_SHA512H2 Q0 Q4 Q1 *)
  w 0x4efa8400;         (* arm_ADD_VEC Q0 Q0 Q26 64 128 *)
  w 0x4efb8421;         (* arm_ADD_VEC Q1 Q1 Q27 64 128 *)
  w 0x4efc8442;         (* arm_ADD_VEC Q2 Q2 Q28 64 128 *)
  w 0x4efd8463;         (* arm_ADD_VEC Q3 Q3 Q29 64 128 *)
  w 0xb5ffc382;         (* arm_CBNZ X2 (word 2095216) *)
  w 0x4c002c00;         (* arm_STP4 Q0 Q1 Q2 Q3 X0 No_Offset *)
  w 0xf84107fd;         (* arm_LDR X29 SP (Postimmediate_Offset (word 16)) *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;
let sha512_hw_k512 = last sha512_hw_data;;
let SHA512_HW_EXEC = ARM_MK_EXEC_RULE sha512_hw_mc;;

(* ------------------------------------------------------------------------- *)
(* A 128-bit register as two 64-bit lanes.                                   *)
(* ------------------------------------------------------------------------- *)

let sha512_pair = new_definition
 `sha512_pair (lo:int64) (hi:int64) : int128 = word_join hi lo`;;

let SHA512_PAIR_SUBWORDS = prove
 (`!lo hi:int64.
     word_subword (sha512_pair lo hi) (0,64) = lo /\
     word_subword (sha512_pair lo hi) (64,64) = hi /\
     word_subword (sha512_pair lo hi) (7,57):57 word = word_subword lo (7,57) /\
     word_subword (sha512_pair lo hi) (71,57):57 word = word_subword hi (7,57) /\
     word_subword (sha512_pair lo hi) (6,58):58 word = word_subword lo (6,58) /\
     word_subword (sha512_pair lo hi) (70,58):58 word = word_subword hi (6,58)`,
  REWRITE_TAC[sha512_pair] THEN CONV_TAC WORD_BLAST);;

let SHA512_JOIN_PAIR = prove
 (`!lo hi:int64. (word_join:int64->int64->int128) hi lo = sha512_pair lo hi`,
  REWRITE_TAC[sha512_pair]);;

let SHA512_EXT_PAIR = prove
 (`!a b c d:int64.
     word_subword ((word_join:int128->int128->256 word) (sha512_pair c d) (sha512_pair a b)) (64,128) =
     sha512_pair b c`,
  REWRITE_TAC[sha512_pair] THEN CONV_TAC WORD_BLAST);;

let SHA512_PAIR_INJ = prove
 (`!a b c d:int64. sha512_pair a b = sha512_pair c d <=> a = c /\ b = d`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(AP_TERM `\q:int128. (word_subword q (0,64):int64)` th) THEN
                       MP_TAC(AP_TERM `\q:int128. (word_subword q (64,64):int64)` th)) THEN
  REWRITE_TAC[SHA512_PAIR_SUBWORDS] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The instructions' functions as the spec's.                                *)
(* ------------------------------------------------------------------------- *)

let SHA512_INSN_FUNCTIONS = prove
 (`(!x y z:int64. word_xor (word_and x y) (word_and (word_not x) z) = sha512_choose x y z) /\
   (!x y z:int64. word_xor (word_and z y) (word_xor (word_and z x) (word_and y x)) = sha512_maj x y z) /\
   (!x y z:int64. word_xor (word_and x y) (word_xor (word_and x z) (word_and z y)) = sha512_maj x y z) /\
   (!x:int64. word_xor (word_ror x 14) (word_xor (word_ror x 18) (word_ror x 41)) = sha512_hash_sigma_1 x) /\
   (!x:int64. word_xor (word_ror x 28) (word_xor (word_ror x 34) (word_ror x 39)) = sha512_hash_sigma_0 x) /\
   (!x:int64. word_xor (word_ror x 1) (word_xor (word_ror x 8)
                ((word_join:7 word->57 word->int64) (word 0) (word_subword x (7,57)))) = sha512_msg_sigma_0 x) /\
   (!x:int64. word_xor (word_ror x 19) (word_xor (word_ror x 61)
                ((word_join:6 word->58 word->int64) (word 0) (word_subword x (6,58)))) = sha512_msg_sigma_1 x)`,
  REWRITE_TAC[sha512_choose; sha512_maj; sha512_hash_sigma_0; sha512_hash_sigma_1;
              sha512_msg_sigma_0; sha512_msg_sigma_1] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* SHA512H and SHA512H2 as two rounds of the spec.                           *)
(* ------------------------------------------------------------------------- *)

let SHA512_ROUND_ELS = prove
 (`!l k w. sha512_round l k w =
           sha512_round [EL 0 l; EL 1 l; EL 2 l; EL 3 l; EL 4 l; EL 5 l; EL 6 l; EL 7 l] k w`,
  REWRITE_TAC[sha512_round] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let SHA512H_2ROUNDS = prove
 (`!l k0 w0 k1 w1.
     let h = sha512h (sha512_pair (word_add (EL 6 l) (word_add k1 w1))
                                  (word_add (EL 7 l) (word_add k0 w0)))
                     (sha512_pair (EL 5 l) (EL 6 l)) (sha512_pair (EL 3 l) (EL 4 l)) in
     let l2 = sha512_round (sha512_round l k0 w0) k1 w1 in
     sha512_pair (word_add (EL 2 l) (word_subword h (0,64)))
                 (word_add (EL 3 l) (word_subword h (64,64))) =
     sha512_pair (EL 4 l2) (EL 5 l2) /\
     sha512h2 h (sha512_pair (EL 2 l) (EL 3 l)) (sha512_pair (EL 0 l) (EL 1 l)) =
     sha512_pair (EL 0 l2) (EL 1 l2)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[SHA512_ROUND_ELS] THEN
  REWRITE_TAC[sha512h; sha512h2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA512_PAIR_SUBWORDS; SHA512_JOIN_PAIR; SHA512_INSN_FUNCTIONS] THEN
  REWRITE_TAC[sha512_round] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[SHA512_PAIR_INJ; WORD_ADD_AC]);;

(* ------------------------------------------------------------------------- *)
(* SHA512SU0 and SHA512SU1 as the message schedule.                          *)
(* ------------------------------------------------------------------------- *)

let SHA512SU_SCHEDULE = prove
 (`!w0 w1 w2 w3 w9 w10 w14 w15:int64.
     sha512su1 (sha512su0 (sha512_pair w0 w1) (sha512_pair w2 w3))
               (sha512_pair w14 w15) (sha512_pair w9 w10) =
     sha512_pair
       (word_add (word_add (sha512_msg_sigma_1 w14) w9) (word_add (sha512_msg_sigma_0 w1) w0))
       (word_add (word_add (sha512_msg_sigma_1 w15) w10) (word_add (sha512_msg_sigma_0 w2) w1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sha512su0] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA512_PAIR_SUBWORDS; SHA512_JOIN_PAIR; SHA512_INSN_FUNCTIONS] THEN
  REWRITE_TAC[sha512su1] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SHA512_PAIR_SUBWORDS; SHA512_JOIN_PAIR; SHA512_INSN_FUNCTIONS] THEN
  REWRITE_TAC[SHA512_PAIR_INJ; WORD_ADD_AC]);;

(* REV64 on a register of two byte-reversed words, as the simulator expands
   it from the instruction's definition. *)
let SHA512_REV64_PAIR =
  let body = body(rhs(concl arm_REV64_VEC_ALT)) in
  let body = subst [`8`,`esize:num`] body in
  let upd = rhs(concl((TOP_DEPTH_CONV let_CONV THENC NUM_REDUCE_CONV THENC REWRITE_CONV[]) body)) in
  let e = rand(rator upd) in
  let n = find_term (fun t -> try fst(dest_const(rator(rator t))) = "read" with _ -> false) e in
  let x = `x:int128` in
  let e = subst [x,n] e in
  prove(mk_forall(x, mk_eq(e,
    `sha512_pair (word_bytereverse (word_subword (x:int128) (0,64):int64))
                 (word_bytereverse (word_subword (x:int128) (64,64):int64))`)),
        REWRITE_TAC[sha512_pair] THEN CONV_TAC WORD_BLAST);;
let SHA512_BYTEREVERSE_BYTEREVERSE = prove
 (`!x:int64. word_bytereverse (word_bytereverse x) = x`, CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Two rounds and two schedule words at a time, for the loop body.           *)
(* ------------------------------------------------------------------------- *)

let SHA512_ROUNDS_STEP = prove
 (`!m hs n.
     let l = sha512_compress_rounds m hs n in
     let h = sha512h
               (sha512_pair
                  (word_add (EL 6 l) (word_add (EL (n+1) sha512_constants) (sha512_msg_schedule m (n+1))))
                  (word_add (EL 7 l) (word_add (EL n sha512_constants) (sha512_msg_schedule m n))))
               (sha512_pair (EL 5 l) (EL 6 l)) (sha512_pair (EL 3 l) (EL 4 l)) in
     sha512_pair (word_add (EL 2 l) (word_subword h (0,64)))
                 (word_add (EL 3 l) (word_subword h (64,64))) =
     sha512_pair (EL 4 (sha512_compress_rounds m hs (n+2)))
                 (EL 5 (sha512_compress_rounds m hs (n+2))) /\
     sha512h2 h (sha512_pair (EL 2 l) (EL 3 l)) (sha512_pair (EL 0 l) (EL 1 l)) =
     sha512_pair (EL 0 (sha512_compress_rounds m hs (n+2)))
                 (EL 1 (sha512_compress_rounds m hs (n+2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `n + 2 = (n + 1) + 1`] THEN
  REWRITE_TAC[sha512_compress_rounds] THEN
  MP_TAC(ISPECL [`sha512_compress_rounds m hs n`; `EL n sha512_constants`;
                 `sha512_msg_schedule m n`; `EL (n+1) sha512_constants`;
                 `sha512_msg_schedule m (n+1)`] SHA512H_2ROUNDS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP_TAC[]);;

let SHA512_MSG_SCHEDULE_REC = prove
 (`!m t. sha512_msg_schedule m (t + 16) =
         word_add (word_add (sha512_msg_sigma_1 (sha512_msg_schedule m (t + 14)))
                            (sha512_msg_schedule m (t + 9)))
                  (word_add (sha512_msg_sigma_0 (sha512_msg_schedule m (t + 1)))
                            (sha512_msg_schedule m t))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [sha512_msg_schedule] THEN
  REWRITE_TAC[ARITH_RULE `~(t + 16 < 16) /\ (t + 16) - 2 = t + 14 /\ (t + 16) - 7 = t + 9 /\
                          (t + 16) - 15 = t + 1 /\ (t + 16) - 16 = t`]);;

let SHA512_SCHED_STEP = prove
 (`!m t.
     sha512su1
       (sha512su0 (sha512_pair (sha512_msg_schedule m t) (sha512_msg_schedule m (t+1)))
                  (sha512_pair (sha512_msg_schedule m (t+2)) (sha512_msg_schedule m (t+3))))
       (sha512_pair (sha512_msg_schedule m (t+14)) (sha512_msg_schedule m (t+15)))
       (sha512_pair (sha512_msg_schedule m (t+9)) (sha512_msg_schedule m (t+10))) =
     sha512_pair (sha512_msg_schedule m (t+16)) (sha512_msg_schedule m (t+17))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SHA512SU_SCHEDULE; SHA512_PAIR_INJ] THEN
  REWRITE_TAC[SHA512_MSG_SCHEDULE_REC; ARITH_RULE `t + 17 = (t + 1) + 16`] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[]);;

(* Every word of the working state after n rounds is one that round n, n-1,
   n-2, or n-3 made, or one of the initial state's: the registers hold each
   word under that one name, whichever step it is read in. *)
let SHA512_ROUNDS_SHIFT = prove
 (`!m hs k.
     EL 1 (sha512_compress_rounds m hs (k + 1)) = EL 0 (sha512_compress_rounds m hs k) /\
     EL 2 (sha512_compress_rounds m hs (k + 1)) = EL 1 (sha512_compress_rounds m hs k) /\
     EL 3 (sha512_compress_rounds m hs (k + 1)) = EL 2 (sha512_compress_rounds m hs k) /\
     EL 5 (sha512_compress_rounds m hs (k + 1)) = EL 4 (sha512_compress_rounds m hs k) /\
     EL 6 (sha512_compress_rounds m hs (k + 1)) = EL 5 (sha512_compress_rounds m hs k) /\
     EL 7 (sha512_compress_rounds m hs (k + 1)) = EL 6 (sha512_compress_rounds m hs k)`,
  REWRITE_TAC[sha512_compress_rounds; sha512_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

let SHA512_NORM_THS =
  CONJUNCT1 sha512_compress_rounds ::
  map (fun k -> CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
         (SPECL [`m:int64 list`; `hs:int64 list`; mk_small_numeral k] SHA512_ROUNDS_SHIFT))
      (0--79);;
let SHA512_NORM_RULE = REWRITE_RULE SHA512_NORM_THS;;

let SHA512_ROUNDS_AT n =
  SHA512_NORM_RULE(CONV_RULE(TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV NUM_ADD_CONV)
    (SPECL [`m:int64 list`; `hs:int64 list`; mk_small_numeral n] SHA512_ROUNDS_STEP));;
let SHA512_SCHED_AT t =
  CONV_RULE(DEPTH_CONV NUM_ADD_CONV) (SPECL [`m:int64 list`; mk_small_numeral t] SHA512_SCHED_STEP);;
let SHA512_BODY_THS =
  map SHA512_ROUNDS_AT (map (( * ) 2) (0--39)) @ map SHA512_SCHED_AT (map (( * ) 2) (0--31));;

let SHA512_SIMP_QREG_TAC =
  let is_qread th =
    let c = concl th in
    is_eq c && (let l = lhs c in
      try let r,_ = dest_comb l in let rd,comp = dest_comb r in
          name_of rd = "read" && is_const comp && String.sub (name_of comp) 0 1 = "Q"
      with _ -> false) in
  let rule = REWRITE_RULE SHA512_BODY_THS o
             REWRITE_RULE[SHA512_PAIR_SUBWORDS; SHA512_JOIN_PAIR; SHA512_EXT_PAIR;
                          SHA512_BYTEREVERSE_BYTEREVERSE] o
             REWRITE_RULE[SHA512_REV64_PAIR] in
  RULE_ASSUM_TAC(fun th -> if is_qread th then rule th else th);;

let SHA512_STEPS_TAC ns =
  MAP_EVERY (fun n -> ARM_STEPS_TAC SHA512_HW_EXEC [n] THEN SHA512_SIMP_QREG_TAC) ns;;

(* ------------------------------------------------------------------------- *)
(* The round constants and the message words in memory.                      *)
(* ------------------------------------------------------------------------- *)

let SHA512_READ_PAIR = prove
 (`!a s. read (memory :> bytes128 a) s =
         sha512_pair (read (memory :> bytes64 a) s)
                     (read (memory :> bytes64 (word_add a (word 8))) s)`,
  REWRITE_TAC[CONJUNCT1(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT); sha512_pair]);;

let sha512_pair_of f i = list_mk_comb(`sha512_pair`, [f i; f (i+1)]);;

let SHA512_HW_K512_PAIRS =
  let kconst t = mk_comb(mk_comb(`EL:num->int64 list->int64`, mk_small_numeral t), `sha512_constants`) in
  let at j = mk_comb(`word:num->int64`, mk_binop `(+):num->num->num` `k:num` (mk_small_numeral (16*j))) in
  let kfacts = list_mk_conj(map (fun j ->
    mk_eq(subst [at j,`a:int64`] `read (memory :> bytes128 a) s`, sha512_pair_of kconst (2*j))) (0--39)) in
  prove
  (mk_forall(`s:armstate`, mk_forall(`k:num`, mk_imp(`bytes_loaded s (word (k + 0)) sha512_hw_k512`, kfacts))),
   REPEAT GEN_TAC THEN REWRITE_TAC[sha512_hw_k512] THEN
   CONV_TAC(LAND_CONV DATA64_CONV) THEN STRIP_TAC THEN
   REWRITE_TAC[SHA512_READ_PAIR; GSYM WORD_ADD] THEN
   REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
   ASM_REWRITE_TAC[sha512_pair; sha512_constants] THEN
   CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC WORD_REDUCE_CONV);;

let sha512_hw_inputs = new_definition
 `sha512_hw_inputs (k512:num) (data:int64) (n:num) (m:num->int64 list) (M:int64->byte) <=>
    read (bytelist (word k512,LENGTH sha512_hw_k512)) M = sha512_hw_k512 /\
    !i j. i < n /\ j < 16
          ==> read (bytes64 (word_add data (word (128 * i + 8 * j)))) M =
              word_bytereverse (EL j (m i))`;;

let SHA512_MSCH_SMALL =
  map (fun t -> CONV_RULE(RAND_CONV(RATOR_CONV(LAND_CONV NUM_LT_CONV) THENC REWRITE_CONV[]))
                  (REWR_CONV sha512_msg_schedule (mk_comb(`sha512_msg_schedule mm`, mk_small_numeral t))))
      (0--15);;

(* Block b's sixteen words, read 16 bytes at a time from where it starts. *)
let SHA512_HW_BLOCK =
  let wd t = mk_comb(`word_bytereverse:int64->int64`,
                     mk_comb(`sha512_msg_schedule (m(b:num))`, mk_small_numeral t)) in
  let at q = if q = 0 then `word_add data (word (128 * b)):int64`
             else mk_comb(mk_comb(`word_add:int64->int64->int64`, `word_add data (word (128 * b)):int64`),
                          mk_comb(`word:num->int64`, mk_small_numeral (16*q))) in
  let facts = list_mk_conj(map (fun q ->
    mk_eq(subst [at q,`a:int64`] `read (memory :> bytes128 a) (s:armstate)`, sha512_pair_of wd (2*q))) (0--7)) in
  prove
  (list_mk_forall([`k512:num`; `data:int64`; `n:num`; `m:num->int64 list`; `s:armstate`; `b:num`],
     mk_imp(`sha512_hw_inputs k512 data n m (read memory s) /\ b < n`, facts)),
   REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   DISCH_THEN(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [sha512_hw_inputs]) THEN
   DISCH_THEN(fun th -> MP_TAC(end_itlist CONJ (map (fun j -> SPECL [`b:num`; mk_small_numeral j] th) (0--15)))) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
   STRIP_TAC THEN
   REWRITE_TAC(SHA512_READ_PAIR :: READ_COMPONENT_COMPOSE :: SHA512_MSCH_SMALL) THEN
   ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
   REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the loop, from after the prologue to before the epilogue.  *)
(* ------------------------------------------------------------------------- *)

let SHA512_MEM0_TAC =
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("memory",_)),_)),Var("mem0",_)) ->
        RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th
    | _ -> failwith "SHA512_MEM0_TAC");;

let SHA512_K512_TAC =
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [sha512_hw_inputs]) THEN
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("memory",_)),_)),Var("mem0",_)) ->
        REWRITE_TAC[SYM th; GSYM READ_COMPONENT_COMPOSE]
    | _ -> failwith "") THEN
  REWRITE_TAC[GSYM bytes_loaded] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `k512 = k512 + 0`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SHA512_HW_K512_PAIRS) THEN
  REWRITE_TAC[ADD_CLAUSES; WORD_ADD; WORD_ADD_0] THEN STRIP_TAC;;

let SHA512_BLOCK_TAC =
  ABBREV_TAC `b = if i + 1 < n then i + 1 else i` THEN
  SUBGOAL_THEN `b < n` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k512:num`; `data:int64`; `n:num`; `m:num->int64 list`; `s0:armstate`; `b:num`]
    SHA512_HW_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `d = word_add data (word (128 * b)):int64` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th);;


let SHA512_BODY_INIT_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SHA512_BLOCK_TAC THEN SHA512_MEM0_TAC THEN SHA512_K512_TAC;;

let SHA512_CSEL_TAC =
  SUBGOAL_THEN `word_sub (word (n - i)) (word 1):int64 = word (n - (i + 1))` SUBST_ALL_TAC THENL
   [REWRITE_TAC[ARITH_RULE `n - (i + 1) = (n - i) - 1`] THEN
    MP_TAC(ISPECL [`n - i`; `1`] (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
    ALL_TAC] THEN
  SUBGOAL_THEN `val (word (n - (i + 1)):int64) = n - (i + 1)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(if ~(n - (i + 1) = 0) then word_add data (word (128 * (i + 1)))
     else word_sub (word_add data (word (128 * (i + 1)))) (word 128)):int64 = d`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EXPAND_TAC "d" THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[ARITH_RULE `n - (i + 1) = 0 <=> ~(i + 1 < n)`] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; WORD_ADD] THEN CONV_TAC WORD_RULE;
    ALL_TAC];;

let SHA512_READ_PAIR_SPLIT = prove
 (`!a s x y.
     read (memory :> bytes128 a) s = sha512_pair x y
     ==> read (memory :> bytes64 a) s = x /\
         read (memory :> bytes64 (word_add a (word 8))) s = y`,
  REWRITE_TAC[SHA512_READ_PAIR; SHA512_PAIR_INJ]);;

let SHA512_HW_CORRECT = prove
 (`!pc k512 state data n h0 h1 h2 h3 h4 h5 h6 h7 m.
     0 < n /\ n < 2 EXP 64 /\
     nonoverlapping (word pc,0x7e0) (state,64) /\
     adrp_within_bounds (word k512) (word (pc + 20))
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) (sha512_hw_mc pc k512) /\
               read PC s = word(pc + 0x8) /\
               C_ARGUMENTS [state; data; word n] s /\
               bytes_loaded s (word k512) sha512_hw_k512 /\
               read (memory :> bytes64 state) s = h0 /\
               read (memory :> bytes64 (word_add state (word 8))) s = h1 /\
               read (memory :> bytes64 (word_add state (word 16))) s = h2 /\
               read (memory :> bytes64 (word_add state (word 24))) s = h3 /\
               read (memory :> bytes64 (word_add state (word 32))) s = h4 /\
               read (memory :> bytes64 (word_add state (word 40))) s = h5 /\
               read (memory :> bytes64 (word_add state (word 48))) s = h6 /\
               read (memory :> bytes64 (word_add state (word 56))) s = h7 /\
               (!i j. i < n /\ j < 16
                      ==> read (memory :> bytes64 (word_add data (word (128 * i + 8 * j)))) s =
                          word_bytereverse (EL j (m i))))
          (\s. read PC s = word(pc + 0x7d8) /\
               let h' = sha512_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] n in
               read (memory :> bytes64 state) s = EL 0 h' /\
               read (memory :> bytes64 (word_add state (word 8))) s = EL 1 h' /\
               read (memory :> bytes64 (word_add state (word 16))) s = EL 2 h' /\
               read (memory :> bytes64 (word_add state (word 24))) s = EL 3 h' /\
               read (memory :> bytes64 (word_add state (word 32))) s = EL 4 h' /\
               read (memory :> bytes64 (word_add state (word 40))) s = EL 5 h' /\
               read (memory :> bytes64 (word_add state (word 48))) s = EL 6 h' /\
               read (memory :> bytes64 (word_add state (word 56))) s = EL 7 h')
          (MAYCHANGE [PC; X1; X2; X3; X4] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(state,64)])`,
  MAP_EVERY X_GEN_TAC [`pc:num`; `k512:num`; `state:int64`; `data:int64`; `n:num`;
    `h0:int64`; `h1:int64`; `h2:int64`; `h3:int64`; `h4:int64`; `h5:int64`; `h6:int64`; `h7:int64`;
    `m:num->int64 list`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst SHA512_HW_EXEC; bytes_loaded] THEN
  STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `n:num` `pc + 0x40` `pc + 0x7d0`
   `\i s. read X0 s = state /\
          read X2 s = word (n - i) /\
          read X3 s = word k512 /\
          read Q0 s = sha512_pair (EL 0 (sha512_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i)) (EL 1 (sha512_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i)) /\
          read Q1 s = sha512_pair (EL 2 (sha512_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i)) (EL 3 (sha512_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i)) /\
          read Q2 s = sha512_pair (EL 4 (sha512_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i)) (EL 5 (sha512_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i)) /\
          read Q3 s = sha512_pair (EL 6 (sha512_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i)) (EL 7 (sha512_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i)) /\
          (i < n ==> read X1 s = word_add data (word (128 * (i + 1))) /\
                     read Q16 s = sha512_pair (sha512_msg_schedule (m i) 0) (sha512_msg_schedule (m i) 1) /\
                     read Q17 s = sha512_pair (sha512_msg_schedule (m i) 2) (sha512_msg_schedule (m i) 3) /\
                     read Q18 s = sha512_pair (sha512_msg_schedule (m i) 4) (sha512_msg_schedule (m i) 5) /\
                     read Q19 s = sha512_pair (sha512_msg_schedule (m i) 6) (sha512_msg_schedule (m i) 7) /\
                     read Q20 s = sha512_pair (sha512_msg_schedule (m i) 8) (sha512_msg_schedule (m i) 9) /\
                     read Q21 s = sha512_pair (sha512_msg_schedule (m i) 10) (sha512_msg_schedule (m i) 11) /\
                     read Q22 s = sha512_pair (sha512_msg_schedule (m i) 12) (sha512_msg_schedule (m i) 13) /\
                     read Q23 s = sha512_pair (sha512_msg_schedule (m i) 14) (sha512_msg_schedule (m i) 15)) /\
          sha512_hw_inputs k512 data n m (read memory s)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (* The prologue loads the state and the first block. *)
    GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `sha512_hw_inputs k512 data n m (read memory s0)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[sha512_hw_inputs; GSYM READ_COMPONENT_COMPOSE]; ALL_TAC] THEN
    MP_TAC(SPECL [`k512:num`; `data:int64`; `n:num`; `m:num->int64 list`; `s0:armstate`; `0`]
    SHA512_HW_BLOCK) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN STRIP_TAC THEN
    SUBGOAL_THEN
    `read (memory :> bytes128 state) s0 = sha512_pair h0 h1 /\
    read (memory :> bytes128 (word_add state (word 16))) s0 = sha512_pair h2 h3 /\
    read (memory :> bytes128 (word_add state (word 32))) s0 = sha512_pair h4 h5 /\
    read (memory :> bytes128 (word_add state (word 48))) s0 = sha512_pair h6 h7`
    STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[SHA512_READ_PAIR; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
    SHA512_STEPS_TAC (1--14) THEN
    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[sha512_hash_blocks; SUB_0] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];

    (* The body: 80 rounds of block i, and block i + 1 loaded, or block i
       again after the last, so no load is past the input. *)
    SHA512_BODY_INIT_TAC THEN SHA512_STEPS_TAC (1--8) THEN SHA512_CSEL_TAC THEN
    SHA512_STEPS_TAC (9--484) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ADD; sha512_hash_blocks; sha512_block] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC SHA512_NORM_THS THEN DISCH_TAC THEN
    SUBGOAL_THEN `b = i + 1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `(if i + 1 < n then i + 1 else i) = b` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(ACCEPT_TAC o SYM); ALL_TAC] THEN
    EXPAND_TAC "d" THEN
    REWRITE_TAC[ARITH_RULE `128 * ((i + 1) + 1) = 128 * (i + 1) + 128`; WORD_ADD; WORD_ADD_ASSOC];

    (* The branch back. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `mem0:int64->byte` `read memory` THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN SHA512_MEM0_TAC THEN
    ARM_STEPS_TAC SHA512_HW_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val (word (n - i):int64) = n - i` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> ~(n - i = 0)`]];

    (* The fall-through after the last block, and the store. *)
    REWRITE_TAC[SUB_REFL; LT_REFL] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC SHA512_HW_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP SHA512_READ_PAIR_SPLIT o
      check (can (term_match [] `read (memory :> bytes128 a) s = sha512_pair x y`) o concl))) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the whole function, with its frame and return.             *)
(* ------------------------------------------------------------------------- *)

let SHA512_HW_BYTES_LOADED = prove
 (`bytes_loaded s tab sha512_hw_k512 <=>
   read (memory :> bytes(tab,704)) s = num_of_bytelist sha512_hw_k512`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV) (AP_TERM `LENGTH:byte list->num` sha512_hw_k512)]);;

let SHA512_HW_SUBROUTINE_CORRECT = prove
 (`!pc k512 state data n h0 h1 h2 h3 h4 h5 h6 h7 m stackpointer returnaddress.
     0 < n /\ n < 2 EXP 64 /\
     aligned 16 stackpointer /\
     adrp_within_bounds (word k512) (word (pc + 20)) /\
     ALLPAIRS nonoverlapping
       [(state,64); (word_sub stackpointer (word 16),16)]
       [(word pc,0x7e0); (data,128 * n); (word k512,704)] /\
     nonoverlapping (state,64) (word_sub stackpointer (word 16),16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) (sha512_hw_mc pc k512) /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [state; data; word n] s /\
               bytes_loaded s (word k512) sha512_hw_k512 /\
               read (memory :> bytes64 state) s = h0 /\
               read (memory :> bytes64 (word_add state (word 8))) s = h1 /\
               read (memory :> bytes64 (word_add state (word 16))) s = h2 /\
               read (memory :> bytes64 (word_add state (word 24))) s = h3 /\
               read (memory :> bytes64 (word_add state (word 32))) s = h4 /\
               read (memory :> bytes64 (word_add state (word 40))) s = h5 /\
               read (memory :> bytes64 (word_add state (word 48))) s = h6 /\
               read (memory :> bytes64 (word_add state (word 56))) s = h7 /\
               (!i j. i < n /\ j < 16
                      ==> read (memory :> bytes64 (word_add data (word (128 * i + 8 * j)))) s =
                          word_bytereverse (EL j (m i))))
          (\s. read PC s = returnaddress /\
               let h' = sha512_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] n in
               read (memory :> bytes64 state) s = EL 0 h' /\
               read (memory :> bytes64 (word_add state (word 8))) s = EL 1 h' /\
               read (memory :> bytes64 (word_add state (word 16))) s = EL 2 h' /\
               read (memory :> bytes64 (word_add state (word 24))) s = EL 3 h' /\
               read (memory :> bytes64 (word_add state (word 32))) s = EL 4 h' /\
               read (memory :> bytes64 (word_add state (word 40))) s = EL 5 h' /\
               read (memory :> bytes64 (word_add state (word 48))) s = EL 6 h' /\
               read (memory :> bytes64 (word_add state (word 56))) s = EL 7 h')
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(state,64);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  REWRITE_TAC[SHA512_HW_BYTES_LOADED; fst SHA512_HW_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(2,1) SHA512_HW_EXEC
    (REWRITE_RULE[SHA512_HW_BYTES_LOADED; fst SHA512_HW_EXEC] SHA512_HW_CORRECT)
    `[X29; X30]` 16);;
