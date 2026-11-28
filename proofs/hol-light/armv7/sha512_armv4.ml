(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* aws-lc's sha512-armv4, as rind's build emits it.                          *)
(* ========================================================================= *)

(* The A32 code rind's low::arm::sha_armv4 assembles from aws-lc's
   sha512-armv4: the table K512 and the routines
   sha512_block_data_order_nohw and sha512_block_data_order_neon, which
   reach K512 through the address an ADR gives it. So the code these
   theorems are about is the whole of it, from K512 at pc. Each theorem
   holds for a caller in A32 or T32, so it covers every armv7 target.

   SHA512_BLOCK_DATA_ORDER_NEON_SUBROUTINE_CORRECT: the NEON routine, which
   rind runs where the CPU has NEON, stores to the state s2n-bignum's
   FIPS 180-4 spec, sha512_hash_blocks, of its blocks from the state, for
   one block or more, as rind calls it. *)

needs "aarch32/proofs/base.ml";;
needs "x86/proofs/utils/sha512_spec.ml";;

(* admin/prove writes the code's bytes, from K512 through the end of
   sha512_block_data_order_neon, as rind's release build for
   armv7-unknown-linux-gnueabihf emits them, to armv7/sha512_armv4.bin, and
   the definition fails unless they are these: K512 at 0,
   sha512_block_data_order_nohw at 0x280, and sha512_block_data_order_neon
   at 0x740, after the padding that aligns it. *)

let sha512_armv4_mc = define_assert_word_list "sha512_armv4_mc"
  (term_of_bytes (load_file "armv7/sha512_armv4.bin"))
[
  0xd728ae22; (* data *)
  0x428a2f98; (* data *)
  0x23ef65cd; (* data *)
  0x71374491; (* data *)
  0xec4d3b2f; (* data *)
  0xb5c0fbcf; (* data *)
  0x8189dbbc; (* data *)
  0xe9b5dba5; (* data *)
  0xf348b538; (* data *)
  0x3956c25b; (* data *)
  0xb605d019; (* data *)
  0x59f111f1; (* data *)
  0xaf194f9b; (* data *)
  0x923f82a4; (* data *)
  0xda6d8118; (* data *)
  0xab1c5ed5; (* data *)
  0xa3030242; (* data *)
  0xd807aa98; (* data *)
  0x45706fbe; (* data *)
  0x12835b01; (* data *)
  0x4ee4b28c; (* data *)
  0x243185be; (* data *)
  0xd5ffb4e2; (* data *)
  0x550c7dc3; (* data *)
  0xf27b896f; (* data *)
  0x72be5d74; (* data *)
  0x3b1696b1; (* data *)
  0x80deb1fe; (* data *)
  0x25c71235; (* data *)
  0x9bdc06a7; (* data *)
  0xcf692694; (* data *)
  0xc19bf174; (* data *)
  0x9ef14ad2; (* data *)
  0xe49b69c1; (* data *)
  0x384f25e3; (* data *)
  0xefbe4786; (* data *)
  0x8b8cd5b5; (* data *)
  0x0fc19dc6; (* data *)
  0x77ac9c65; (* data *)
  0x240ca1cc; (* data *)
  0x592b0275; (* data *)
  0x2de92c6f; (* data *)
  0x6ea6e483; (* data *)
  0x4a7484aa; (* data *)
  0xbd41fbd4; (* data *)
  0x5cb0a9dc; (* data *)
  0x831153b5; (* data *)
  0x76f988da; (* data *)
  0xee66dfab; (* data *)
  0x983e5152; (* data *)
  0x2db43210; (* data *)
  0xa831c66d; (* data *)
  0x98fb213f; (* data *)
  0xb00327c8; (* data *)
  0xbeef0ee4; (* data *)
  0xbf597fc7; (* data *)
  0x3da88fc2; (* data *)
  0xc6e00bf3; (* data *)
  0x930aa725; (* data *)
  0xd5a79147; (* data *)
  0xe003826f; (* data *)
  0x06ca6351; (* data *)
  0x0a0e6e70; (* data *)
  0x14292967; (* data *)
  0x46d22ffc; (* data *)
  0x27b70a85; (* data *)
  0x5c26c926; (* data *)
  0x2e1b2138; (* data *)
  0x5ac42aed; (* data *)
  0x4d2c6dfc; (* data *)
  0x9d95b3df; (* data *)
  0x53380d13; (* data *)
  0x8baf63de; (* data *)
  0x650a7354; (* data *)
  0x3c77b2a8; (* data *)
  0x766a0abb; (* data *)
  0x47edaee6; (* data *)
  0x81c2c92e; (* data *)
  0x1482353b; (* data *)
  0x92722c85; (* data *)
  0x4cf10364; (* data *)
  0xa2bfe8a1; (* data *)
  0xbc423001; (* data *)
  0xa81a664b; (* data *)
  0xd0f89791; (* data *)
  0xc24b8b70; (* data *)
  0x0654be30; (* data *)
  0xc76c51a3; (* data *)
  0xd6ef5218; (* data *)
  0xd192e819; (* data *)
  0x5565a910; (* data *)
  0xd6990624; (* data *)
  0x5771202a; (* data *)
  0xf40e3585; (* data *)
  0x32bbd1b8; (* data *)
  0x106aa070; (* data *)
  0xb8d2d0c8; (* data *)
  0x19a4c116; (* data *)
  0x5141ab53; (* data *)
  0x1e376c08; (* data *)
  0xdf8eeb99; (* data *)
  0x2748774c; (* data *)
  0xe19b48a8; (* data *)
  0x34b0bcb5; (* data *)
  0xc5c95a63; (* data *)
  0x391c0cb3; (* data *)
  0xe3418acb; (* data *)
  0x4ed8aa4a; (* data *)
  0x7763e373; (* data *)
  0x5b9cca4f; (* data *)
  0xd6b2b8a3; (* data *)
  0x682e6ff3; (* data *)
  0x5defb2fc; (* data *)
  0x748f82ee; (* data *)
  0x43172f60; (* data *)
  0x78a5636f; (* data *)
  0xa1f0ab72; (* data *)
  0x84c87814; (* data *)
  0x1a6439ec; (* data *)
  0x8cc70208; (* data *)
  0x23631e28; (* data *)
  0x90befffa; (* data *)
  0xde82bde9; (* data *)
  0xa4506ceb; (* data *)
  0xb2c67915; (* data *)
  0xbef9a3f7; (* data *)
  0xe372532b; (* data *)
  0xc67178f2; (* data *)
  0xea26619c; (* data *)
  0xca273ece; (* data *)
  0x21c0c207; (* data *)
  0xd186b8c7; (* data *)
  0xcde0eb1e; (* data *)
  0xeada7dd6; (* data *)
  0xee6ed178; (* data *)
  0xf57d4f7f; (* data *)
  0x72176fba; (* data *)
  0x06f067aa; (* data *)
  0xa2c898a6; (* data *)
  0x0a637dc5; (* data *)
  0xbef90dae; (* data *)
  0x113f9804; (* data *)
  0x131c471b; (* data *)
  0x1b710b35; (* data *)
  0x23047d84; (* data *)
  0x28db77f5; (* data *)
  0x40c72493; (* data *)
  0x32caab7b; (* data *)
  0x15c9bebc; (* data *)
  0x3c9ebe0a; (* data *)
  0x9c100d4c; (* data *)
  0x431d67c4; (* data *)
  0xcb3e42b6; (* data *)
  0x4cc5d4be; (* data *)
  0xfc657e2a; (* data *)
  0x597f299c; (* data *)
  0x3ad6faec; (* data *)
  0x5fcb6fab; (* data *)
  0x4a475817; (* data *)
  0x6c44198c; (* data *)
  0xe0812382; (* add r2, r1, r2, lsl #7 *)
  0xe92d5ff0; (* push {r4, r5, r6, r7, r8, r9, r10, r11, r12, lr} *)
  0xe24fee29; (* sub lr, pc, #656 *)
  0xe24dd048; (* sub sp, sp, #72 *)
  0xe5907020; (* ldr r7, [r0, #0x20] *)
  0xe5908024; (* ldr r8, [r0, #0x24] *)
  0xe5909030; (* ldr r9, [r0, #0x30] *)
  0xe590a034; (* ldr r10, [r0, #0x34] *)
  0xe590b038; (* ldr r11, [r0, #0x38] *)
  0xe590c03c; (* ldr r12, [r0, #0x3c] *)
  0xe58d9030; (* str r9, [sp, #0x30] *)
  0xe58da034; (* str r10, [sp, #0x34] *)
  0xe58db038; (* str r11, [sp, #0x38] *)
  0xe58dc03c; (* str r12, [sp, #0x3c] *)
  0xe5905000; (* ldr r5, [r0] *)
  0xe5906004; (* ldr r6, [r0, #0x4] *)
  0xe5903008; (* ldr r3, [r0, #0x8] *)
  0xe590400c; (* ldr r4, [r0, #0xc] *)
  0xe5909010; (* ldr r9, [r0, #0x10] *)
  0xe590a014; (* ldr r10, [r0, #0x14] *)
  0xe590b018; (* ldr r11, [r0, #0x18] *)
  0xe590c01c; (* ldr r12, [r0, #0x1c] *)
  0xe58d3008; (* str r3, [sp, #0x8] *)
  0xe58d400c; (* str r4, [sp, #0xc] *)
  0xe58d9010; (* str r9, [sp, #0x10] *)
  0xe58da014; (* str r10, [sp, #0x14] *)
  0xe58db018; (* str r11, [sp, #0x18] *)
  0xe58dc01c; (* str r12, [sp, #0x1c] *)
  0xe5903028; (* ldr r3, [r0, #0x28] *)
  0xe590402c; (* ldr r4, [r0, #0x2c] *)
  0xe58d3028; (* str r3, [sp, #0x28] *)
  0xe58d402c; (* str r4, [sp, #0x2c] *)
  0xe5913004; (* ldr r3, [r1, #0x4] *)
  0xe4914008; (* ldr r4, [r1], #8 *)
  0xe6bf3f33; (* rev r3, r3 *)
  0xe6bf4f34; (* rev r4, r4 *)
  0xe1a09727; (* lsr r9, r7, #14 *)
  0xe58d3040; (* str r3, [sp, #0x40] *)
  0xe1a0a728; (* lsr r10, r8, #14 *)
  0xe58d4044; (* str r4, [sp, #0x44] *)
  0xe0299908; (* eor r9, r9, r8, lsl #18 *)
  0xe59db038; (* ldr r11, [sp, #0x38] *)
  0xe02aa907; (* eor r10, r10, r7, lsl #18 *)
  0xe59dc03c; (* ldr r12, [sp, #0x3c] *)
  0xe0299927; (* eor r9, r9, r7, lsr #18 *)
  0xe02aa928; (* eor r10, r10, r8, lsr #18 *)
  0xe0299708; (* eor r9, r9, r8, lsl #14 *)
  0xe02aa707; (* eor r10, r10, r7, lsl #14 *)
  0xe02994a8; (* eor r9, r9, r8, lsr #9 *)
  0xe02aa4a7; (* eor r10, r10, r7, lsr #9 *)
  0xe0299b87; (* eor r9, r9, r7, lsl #23 *)
  0xe02aab88; (* eor r10, r10, r8, lsl #23 *)
  0xe0933009; (* adds r3, r3, r9 *)
  0xe59d9028; (* ldr r9, [sp, #0x28] *)
  0xe0a4400a; (* adc r4, r4, r10 *)
  0xe59da02c; (* ldr r10, [sp, #0x2c] *)
  0xe093300b; (* adds r3, r3, r11 *)
  0xe59db030; (* ldr r11, [sp, #0x30] *)
  0xe0a4400c; (* adc r4, r4, r12 *)
  0xe59dc034; (* ldr r12, [sp, #0x34] *)
  0xe029900b; (* eor r9, r9, r11 *)
  0xe58d7020; (* str r7, [sp, #0x20] *)
  0xe02aa00c; (* eor r10, r10, r12 *)
  0xe58d8024; (* str r8, [sp, #0x24] *)
  0xe0099007; (* and r9, r9, r7 *)
  0xe58d5000; (* str r5, [sp] *)
  0xe00aa008; (* and r10, r10, r8 *)
  0xe58d6004; (* str r6, [sp, #0x4] *)
  0xe029900b; (* eor r9, r9, r11 *)
  0xe59eb000; (* ldr r11, [lr] *)
  0xe02aa00c; (* eor r10, r10, r12 *)
  0xe59ec004; (* ldr r12, [lr, #0x4] *)
  0xe0933009; (* adds r3, r3, r9 *)
  0xe59d7018; (* ldr r7, [sp, #0x18] *)
  0xe0a4400a; (* adc r4, r4, r10 *)
  0xe59d801c; (* ldr r8, [sp, #0x1c] *)
  0xe093300b; (* adds r3, r3, r11 *)
  0xe20b90ff; (* and r9, r11, #255 *)
  0xe0a4400c; (* adc r4, r4, r12 *)
  0xe0977003; (* adds r7, r7, r3 *)
  0xe59db008; (* ldr r11, [sp, #0x8] *)
  0xe0a88004; (* adc r8, r8, r4 *)
  0xe3390094; (* teq r9, #148 *)
  0xe59dc010; (* ldr r12, [sp, #0x10] *)
  0x038ee001; (* orreq lr, lr, #1 *)
  0xe1a09e25; (* lsr r9, r5, #28 *)
  0xe1a0ae26; (* lsr r10, r6, #28 *)
  0xe0299206; (* eor r9, r9, r6, lsl #4 *)
  0xe02aa205; (* eor r10, r10, r5, lsl #4 *)
  0xe0299126; (* eor r9, r9, r6, lsr #2 *)
  0xe02aa125; (* eor r10, r10, r5, lsr #2 *)
  0xe0299f05; (* eor r9, r9, r5, lsl #30 *)
  0xe02aaf06; (* eor r10, r10, r6, lsl #30 *)
  0xe02993a6; (* eor r9, r9, r6, lsr #7 *)
  0xe02aa3a5; (* eor r10, r10, r5, lsr #7 *)
  0xe0299c85; (* eor r9, r9, r5, lsl #25 *)
  0xe02aac86; (* eor r10, r10, r6, lsl #25 *)
  0xe0933009; (* adds r3, r3, r9 *)
  0xe005900b; (* and r9, r5, r11 *)
  0xe0a4400a; (* adc r4, r4, r10 *)
  0xe59da00c; (* ldr r10, [sp, #0xc] *)
  0xe185500b; (* orr r5, r5, r11 *)
  0xe59db014; (* ldr r11, [sp, #0x14] *)
  0xe005500c; (* and r5, r5, r12 *)
  0xe006c00a; (* and r12, r6, r10 *)
  0xe186600a; (* orr r6, r6, r10 *)
  0xe1855009; (* orr r5, r5, r9 *)
  0xe006600b; (* and r6, r6, r11 *)
  0xe0955003; (* adds r5, r5, r3 *)
  0xe186600c; (* orr r6, r6, r12 *)
  0xe24dd008; (* sub sp, sp, #8 *)
  0xe0a66004; (* adc r6, r6, r4 *)
  0xe31e0001; (* tst lr, #1 *)
  0xe28ee008; (* add lr, lr, #8 *)
  0xe31e0001; (* tst lr, #1 *)
  0x0affffab; (* beq 0x300 *)
  0xe59d90b8; (* ldr r9, [sp, #0xb8] *)
  0xe59da0bc; (* ldr r10, [sp, #0xbc] *)
  0xe3cee001; (* bic lr, lr, #1 *)
  0xe1a030a9; (* lsr r3, r9, #1 *)
  0xe59db050; (* ldr r11, [sp, #0x50] *)
  0xe1a040aa; (* lsr r4, r10, #1 *)
  0xe59dc054; (* ldr r12, [sp, #0x54] *)
  0xe0233f8a; (* eor r3, r3, r10, lsl #31 *)
  0xe0244f89; (* eor r4, r4, r9, lsl #31 *)
  0xe0233429; (* eor r3, r3, r9, lsr #8 *)
  0xe024442a; (* eor r4, r4, r10, lsr #8 *)
  0xe0233c0a; (* eor r3, r3, r10, lsl #24 *)
  0xe0244c09; (* eor r4, r4, r9, lsl #24 *)
  0xe02333a9; (* eor r3, r3, r9, lsr #7 *)
  0xe02443aa; (* eor r4, r4, r10, lsr #7 *)
  0xe0233c8a; (* eor r3, r3, r10, lsl #25 *)
  0xe1a099ab; (* lsr r9, r11, #19 *)
  0xe1a0a9ac; (* lsr r10, r12, #19 *)
  0xe029968c; (* eor r9, r9, r12, lsl #13 *)
  0xe02aa68b; (* eor r10, r10, r11, lsl #13 *)
  0xe0299eac; (* eor r9, r9, r12, lsr #29 *)
  0xe02aaeab; (* eor r10, r10, r11, lsr #29 *)
  0xe029918b; (* eor r9, r9, r11, lsl #3 *)
  0xe02aa18c; (* eor r10, r10, r12, lsl #3 *)
  0xe029932b; (* eor r9, r9, r11, lsr #6 *)
  0xe02aa32c; (* eor r10, r10, r12, lsr #6 *)
  0xe59db078; (* ldr r11, [sp, #0x78] *)
  0xe0299d0c; (* eor r9, r9, r12, lsl #26 *)
  0xe59dc07c; (* ldr r12, [sp, #0x7c] *)
  0xe0933009; (* adds r3, r3, r9 *)
  0xe59d90c0; (* ldr r9, [sp, #0xc0] *)
  0xe0a4400a; (* adc r4, r4, r10 *)
  0xe59da0c4; (* ldr r10, [sp, #0xc4] *)
  0xe093300b; (* adds r3, r3, r11 *)
  0xe0a4400c; (* adc r4, r4, r12 *)
  0xe0933009; (* adds r3, r3, r9 *)
  0xe0a4400a; (* adc r4, r4, r10 *)
  0xe1a09727; (* lsr r9, r7, #14 *)
  0xe58d3040; (* str r3, [sp, #0x40] *)
  0xe1a0a728; (* lsr r10, r8, #14 *)
  0xe58d4044; (* str r4, [sp, #0x44] *)
  0xe0299908; (* eor r9, r9, r8, lsl #18 *)
  0xe59db038; (* ldr r11, [sp, #0x38] *)
  0xe02aa907; (* eor r10, r10, r7, lsl #18 *)
  0xe59dc03c; (* ldr r12, [sp, #0x3c] *)
  0xe0299927; (* eor r9, r9, r7, lsr #18 *)
  0xe02aa928; (* eor r10, r10, r8, lsr #18 *)
  0xe0299708; (* eor r9, r9, r8, lsl #14 *)
  0xe02aa707; (* eor r10, r10, r7, lsl #14 *)
  0xe02994a8; (* eor r9, r9, r8, lsr #9 *)
  0xe02aa4a7; (* eor r10, r10, r7, lsr #9 *)
  0xe0299b87; (* eor r9, r9, r7, lsl #23 *)
  0xe02aab88; (* eor r10, r10, r8, lsl #23 *)
  0xe0933009; (* adds r3, r3, r9 *)
  0xe59d9028; (* ldr r9, [sp, #0x28] *)
  0xe0a4400a; (* adc r4, r4, r10 *)
  0xe59da02c; (* ldr r10, [sp, #0x2c] *)
  0xe093300b; (* adds r3, r3, r11 *)
  0xe59db030; (* ldr r11, [sp, #0x30] *)
  0xe0a4400c; (* adc r4, r4, r12 *)
  0xe59dc034; (* ldr r12, [sp, #0x34] *)
  0xe029900b; (* eor r9, r9, r11 *)
  0xe58d7020; (* str r7, [sp, #0x20] *)
  0xe02aa00c; (* eor r10, r10, r12 *)
  0xe58d8024; (* str r8, [sp, #0x24] *)
  0xe0099007; (* and r9, r9, r7 *)
  0xe58d5000; (* str r5, [sp] *)
  0xe00aa008; (* and r10, r10, r8 *)
  0xe58d6004; (* str r6, [sp, #0x4] *)
  0xe029900b; (* eor r9, r9, r11 *)
  0xe59eb000; (* ldr r11, [lr] *)
  0xe02aa00c; (* eor r10, r10, r12 *)
  0xe59ec004; (* ldr r12, [lr, #0x4] *)
  0xe0933009; (* adds r3, r3, r9 *)
  0xe59d7018; (* ldr r7, [sp, #0x18] *)
  0xe0a4400a; (* adc r4, r4, r10 *)
  0xe59d801c; (* ldr r8, [sp, #0x1c] *)
  0xe093300b; (* adds r3, r3, r11 *)
  0xe20b90ff; (* and r9, r11, #255 *)
  0xe0a4400c; (* adc r4, r4, r12 *)
  0xe0977003; (* adds r7, r7, r3 *)
  0xe59db008; (* ldr r11, [sp, #0x8] *)
  0xe0a88004; (* adc r8, r8, r4 *)
  0xe3390017; (* teq r9, #23 *)
  0xe59dc010; (* ldr r12, [sp, #0x10] *)
  0x038ee001; (* orreq lr, lr, #1 *)
  0xe1a09e25; (* lsr r9, r5, #28 *)
  0xe1a0ae26; (* lsr r10, r6, #28 *)
  0xe0299206; (* eor r9, r9, r6, lsl #4 *)
  0xe02aa205; (* eor r10, r10, r5, lsl #4 *)
  0xe0299126; (* eor r9, r9, r6, lsr #2 *)
  0xe02aa125; (* eor r10, r10, r5, lsr #2 *)
  0xe0299f05; (* eor r9, r9, r5, lsl #30 *)
  0xe02aaf06; (* eor r10, r10, r6, lsl #30 *)
  0xe02993a6; (* eor r9, r9, r6, lsr #7 *)
  0xe02aa3a5; (* eor r10, r10, r5, lsr #7 *)
  0xe0299c85; (* eor r9, r9, r5, lsl #25 *)
  0xe02aac86; (* eor r10, r10, r6, lsl #25 *)
  0xe0933009; (* adds r3, r3, r9 *)
  0xe005900b; (* and r9, r5, r11 *)
  0xe0a4400a; (* adc r4, r4, r10 *)
  0xe59da00c; (* ldr r10, [sp, #0xc] *)
  0xe185500b; (* orr r5, r5, r11 *)
  0xe59db014; (* ldr r11, [sp, #0x14] *)
  0xe005500c; (* and r5, r5, r12 *)
  0xe006c00a; (* and r12, r6, r10 *)
  0xe186600a; (* orr r6, r6, r10 *)
  0xe1855009; (* orr r5, r5, r9 *)
  0xe006600b; (* and r6, r6, r11 *)
  0xe0955003; (* adds r5, r5, r3 *)
  0xe186600c; (* orr r6, r6, r12 *)
  0xe24dd008; (* sub sp, sp, #8 *)
  0xe0a66004; (* adc r6, r6, r4 *)
  0xe31e0001; (* tst lr, #1 *)
  0xe28ee008; (* add lr, lr, #8 *)
  0x059d90b8; (* ldreq r9, [sp, #0xb8] *)
  0x059da0bc; (* ldreq r10, [sp, #0xbc] *)
  0x0affff8c; (* beq 0x45c *)
  0xe3cee001; (* bic lr, lr, #1 *)
  0xe59d3008; (* ldr r3, [sp, #0x8] *)
  0xe59d400c; (* ldr r4, [sp, #0xc] *)
  0xe5909000; (* ldr r9, [r0] *)
  0xe590a004; (* ldr r10, [r0, #0x4] *)
  0xe590b008; (* ldr r11, [r0, #0x8] *)
  0xe590c00c; (* ldr r12, [r0, #0xc] *)
  0xe0959009; (* adds r9, r5, r9 *)
  0xe5809000; (* str r9, [r0] *)
  0xe0a6a00a; (* adc r10, r6, r10 *)
  0xe580a004; (* str r10, [r0, #0x4] *)
  0xe093b00b; (* adds r11, r3, r11 *)
  0xe580b008; (* str r11, [r0, #0x8] *)
  0xe0a4c00c; (* adc r12, r4, r12 *)
  0xe580c00c; (* str r12, [r0, #0xc] *)
  0xe59d5010; (* ldr r5, [sp, #0x10] *)
  0xe59d6014; (* ldr r6, [sp, #0x14] *)
  0xe59d3018; (* ldr r3, [sp, #0x18] *)
  0xe59d401c; (* ldr r4, [sp, #0x1c] *)
  0xe5909010; (* ldr r9, [r0, #0x10] *)
  0xe590a014; (* ldr r10, [r0, #0x14] *)
  0xe590b018; (* ldr r11, [r0, #0x18] *)
  0xe590c01c; (* ldr r12, [r0, #0x1c] *)
  0xe0959009; (* adds r9, r5, r9 *)
  0xe5809010; (* str r9, [r0, #0x10] *)
  0xe0a6a00a; (* adc r10, r6, r10 *)
  0xe580a014; (* str r10, [r0, #0x14] *)
  0xe093b00b; (* adds r11, r3, r11 *)
  0xe580b018; (* str r11, [r0, #0x18] *)
  0xe0a4c00c; (* adc r12, r4, r12 *)
  0xe580c01c; (* str r12, [r0, #0x1c] *)
  0xe59d3028; (* ldr r3, [sp, #0x28] *)
  0xe59d402c; (* ldr r4, [sp, #0x2c] *)
  0xe5909020; (* ldr r9, [r0, #0x20] *)
  0xe590a024; (* ldr r10, [r0, #0x24] *)
  0xe590b028; (* ldr r11, [r0, #0x28] *)
  0xe590c02c; (* ldr r12, [r0, #0x2c] *)
  0xe0977009; (* adds r7, r7, r9 *)
  0xe5807020; (* str r7, [r0, #0x20] *)
  0xe0a8800a; (* adc r8, r8, r10 *)
  0xe5808024; (* str r8, [r0, #0x24] *)
  0xe093b00b; (* adds r11, r3, r11 *)
  0xe580b028; (* str r11, [r0, #0x28] *)
  0xe0a4c00c; (* adc r12, r4, r12 *)
  0xe580c02c; (* str r12, [r0, #0x2c] *)
  0xe59d5030; (* ldr r5, [sp, #0x30] *)
  0xe59d6034; (* ldr r6, [sp, #0x34] *)
  0xe59d3038; (* ldr r3, [sp, #0x38] *)
  0xe59d403c; (* ldr r4, [sp, #0x3c] *)
  0xe5909030; (* ldr r9, [r0, #0x30] *)
  0xe590a034; (* ldr r10, [r0, #0x34] *)
  0xe590b038; (* ldr r11, [r0, #0x38] *)
  0xe590c03c; (* ldr r12, [r0, #0x3c] *)
  0xe0959009; (* adds r9, r5, r9 *)
  0xe5809030; (* str r9, [r0, #0x30] *)
  0xe0a6a00a; (* adc r10, r6, r10 *)
  0xe580a034; (* str r10, [r0, #0x34] *)
  0xe093b00b; (* adds r11, r3, r11 *)
  0xe580b038; (* str r11, [r0, #0x38] *)
  0xe0a4c00c; (* adc r12, r4, r12 *)
  0xe580c03c; (* str r12, [r0, #0x3c] *)
  0xe28ddd0a; (* add sp, sp, #640 *)
  0xe24eed0a; (* sub lr, lr, #640 *)
  0xe1310002; (* teq r1, r2 *)
  0x1afffede; (* bne 0x2a8 *)
  0xe28dd048; (* add sp, sp, #72 *)
  0xe8bd9ff0; (* pop {r4, r5, r6, r7, r8, r9, r10, r11, r12, pc} *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xf57ff05f; (* dmb sy *)
  0xe0812382; (* add r2, r1, r2, lsl #7 *)
  0xe24f3e75; (* sub r3, pc, #1872 *)
  0xed2d8b10; (* vpush {d8, d9, d10, d11, d12, d13, d14, d15} *)
  0xecd00b10; (* vldmia r0, {d16, d17, d18, d19, d20, d21, d22, d23} *)
  0xf3f280b4; (* vshr.u64 d24, d20, #0xe *)
  0xf42107cd; (* vld1.64 {d0}, [r1]! *)
  0xf3ee90b4; (* vshr.u64 d25, d20, #0x12 *)
  0xf3d7a0b4; (* vshr.u64 d26, d20, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b4; (* vsli.64 d24, d20, #0x32 *)
  0xf3ee95b4; (* vsli.64 d25, d20, #0x2e *)
  0xf264d1b4; (* vorr d29, d20, d20 *)
  0xf3d7a5b4; (* vsli.64 d26, d20, #0x17 *)
  0xf3b00000; (* vrev64.8 d0, d0 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf355d1b6; (* vbsl d29, d21, d22 *)
  0xf3e480b0; (* vshr.u64 d24, d16, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a7; (* vadd.i64 d27, d29, d23 *)
  0xf3de90b0; (* vshr.u64 d25, d16, #0x22 *)
  0xf3e485b0; (* vsli.64 d24, d16, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b0; (* vshr.u64 d26, d16, #0x27 *)
  0xf27cc880; (* vadd.i64 d28, d28, d0 *)
  0xf3de95b0; (* vsli.64 d25, d16, #0x1e *)
  0xf340e1b1; (* veor d30, d16, d17 *)
  0xf3d9a5b0; (* vsli.64 d26, d16, #0x19 *)
  0xf34871b9; (* veor d23, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf352e1b1; (* vbsl d30, d18, d17 *)
  0xf34771ba; (* veor d23, d23, d26 *)
  0xf27338ab; (* vadd.i64 d19, d19, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b3; (* vshr.u64 d24, d19, #0xe *)
  0xf42117cd; (* vld1.64 {d1}, [r1]! *)
  0xf3ee90b3; (* vshr.u64 d25, d19, #0x12 *)
  0xf27778ae; (* vadd.i64 d23, d23, d30 *)
  0xf3d7a0b3; (* vshr.u64 d26, d19, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b3; (* vsli.64 d24, d19, #0x32 *)
  0xf3ee95b3; (* vsli.64 d25, d19, #0x2e *)
  0xf263d1b3; (* vorr d29, d19, d19 *)
  0xf3d7a5b3; (* vsli.64 d26, d19, #0x17 *)
  0xf3b01001; (* vrev64.8 d1, d1 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf354d1b5; (* vbsl d29, d20, d21 *)
  0xf3e480b7; (* vshr.u64 d24, d23, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a6; (* vadd.i64 d27, d29, d22 *)
  0xf3de90b7; (* vshr.u64 d25, d23, #0x22 *)
  0xf3e485b7; (* vsli.64 d24, d23, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b7; (* vshr.u64 d26, d23, #0x27 *)
  0xf27cc881; (* vadd.i64 d28, d28, d1 *)
  0xf3de95b7; (* vsli.64 d25, d23, #0x1e *)
  0xf347e1b0; (* veor d30, d23, d16 *)
  0xf3d9a5b7; (* vsli.64 d26, d23, #0x19 *)
  0xf34861b9; (* veor d22, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf351e1b0; (* vbsl d30, d17, d16 *)
  0xf34661ba; (* veor d22, d22, d26 *)
  0xf27228ab; (* vadd.i64 d18, d18, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b2; (* vshr.u64 d24, d18, #0xe *)
  0xf42127cd; (* vld1.64 {d2}, [r1]! *)
  0xf3ee90b2; (* vshr.u64 d25, d18, #0x12 *)
  0xf27668ae; (* vadd.i64 d22, d22, d30 *)
  0xf3d7a0b2; (* vshr.u64 d26, d18, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b2; (* vsli.64 d24, d18, #0x32 *)
  0xf3ee95b2; (* vsli.64 d25, d18, #0x2e *)
  0xf262d1b2; (* vorr d29, d18, d18 *)
  0xf3d7a5b2; (* vsli.64 d26, d18, #0x17 *)
  0xf3b02002; (* vrev64.8 d2, d2 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf353d1b4; (* vbsl d29, d19, d20 *)
  0xf3e480b6; (* vshr.u64 d24, d22, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a5; (* vadd.i64 d27, d29, d21 *)
  0xf3de90b6; (* vshr.u64 d25, d22, #0x22 *)
  0xf3e485b6; (* vsli.64 d24, d22, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b6; (* vshr.u64 d26, d22, #0x27 *)
  0xf27cc882; (* vadd.i64 d28, d28, d2 *)
  0xf3de95b6; (* vsli.64 d25, d22, #0x1e *)
  0xf346e1b7; (* veor d30, d22, d23 *)
  0xf3d9a5b6; (* vsli.64 d26, d22, #0x19 *)
  0xf34851b9; (* veor d21, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf350e1b7; (* vbsl d30, d16, d23 *)
  0xf34551ba; (* veor d21, d21, d26 *)
  0xf27118ab; (* vadd.i64 d17, d17, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b1; (* vshr.u64 d24, d17, #0xe *)
  0xf42137cd; (* vld1.64 {d3}, [r1]! *)
  0xf3ee90b1; (* vshr.u64 d25, d17, #0x12 *)
  0xf27558ae; (* vadd.i64 d21, d21, d30 *)
  0xf3d7a0b1; (* vshr.u64 d26, d17, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b1; (* vsli.64 d24, d17, #0x32 *)
  0xf3ee95b1; (* vsli.64 d25, d17, #0x2e *)
  0xf261d1b1; (* vorr d29, d17, d17 *)
  0xf3d7a5b1; (* vsli.64 d26, d17, #0x17 *)
  0xf3b03003; (* vrev64.8 d3, d3 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf352d1b3; (* vbsl d29, d18, d19 *)
  0xf3e480b5; (* vshr.u64 d24, d21, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a4; (* vadd.i64 d27, d29, d20 *)
  0xf3de90b5; (* vshr.u64 d25, d21, #0x22 *)
  0xf3e485b5; (* vsli.64 d24, d21, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b5; (* vshr.u64 d26, d21, #0x27 *)
  0xf27cc883; (* vadd.i64 d28, d28, d3 *)
  0xf3de95b5; (* vsli.64 d25, d21, #0x1e *)
  0xf345e1b6; (* veor d30, d21, d22 *)
  0xf3d9a5b5; (* vsli.64 d26, d21, #0x19 *)
  0xf34841b9; (* veor d20, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf357e1b6; (* vbsl d30, d23, d22 *)
  0xf34441ba; (* veor d20, d20, d26 *)
  0xf27008ab; (* vadd.i64 d16, d16, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b0; (* vshr.u64 d24, d16, #0xe *)
  0xf42147cd; (* vld1.64 {d4}, [r1]! *)
  0xf3ee90b0; (* vshr.u64 d25, d16, #0x12 *)
  0xf27448ae; (* vadd.i64 d20, d20, d30 *)
  0xf3d7a0b0; (* vshr.u64 d26, d16, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b0; (* vsli.64 d24, d16, #0x32 *)
  0xf3ee95b0; (* vsli.64 d25, d16, #0x2e *)
  0xf260d1b0; (* vorr d29, d16, d16 *)
  0xf3d7a5b0; (* vsli.64 d26, d16, #0x17 *)
  0xf3b04004; (* vrev64.8 d4, d4 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf351d1b2; (* vbsl d29, d17, d18 *)
  0xf3e480b4; (* vshr.u64 d24, d20, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a3; (* vadd.i64 d27, d29, d19 *)
  0xf3de90b4; (* vshr.u64 d25, d20, #0x22 *)
  0xf3e485b4; (* vsli.64 d24, d20, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b4; (* vshr.u64 d26, d20, #0x27 *)
  0xf27cc884; (* vadd.i64 d28, d28, d4 *)
  0xf3de95b4; (* vsli.64 d25, d20, #0x1e *)
  0xf344e1b5; (* veor d30, d20, d21 *)
  0xf3d9a5b4; (* vsli.64 d26, d20, #0x19 *)
  0xf34831b9; (* veor d19, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf356e1b5; (* vbsl d30, d22, d21 *)
  0xf34331ba; (* veor d19, d19, d26 *)
  0xf27778ab; (* vadd.i64 d23, d23, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b7; (* vshr.u64 d24, d23, #0xe *)
  0xf42157cd; (* vld1.64 {d5}, [r1]! *)
  0xf3ee90b7; (* vshr.u64 d25, d23, #0x12 *)
  0xf27338ae; (* vadd.i64 d19, d19, d30 *)
  0xf3d7a0b7; (* vshr.u64 d26, d23, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b7; (* vsli.64 d24, d23, #0x32 *)
  0xf3ee95b7; (* vsli.64 d25, d23, #0x2e *)
  0xf267d1b7; (* vorr d29, d23, d23 *)
  0xf3d7a5b7; (* vsli.64 d26, d23, #0x17 *)
  0xf3b05005; (* vrev64.8 d5, d5 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf350d1b1; (* vbsl d29, d16, d17 *)
  0xf3e480b3; (* vshr.u64 d24, d19, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a2; (* vadd.i64 d27, d29, d18 *)
  0xf3de90b3; (* vshr.u64 d25, d19, #0x22 *)
  0xf3e485b3; (* vsli.64 d24, d19, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b3; (* vshr.u64 d26, d19, #0x27 *)
  0xf27cc885; (* vadd.i64 d28, d28, d5 *)
  0xf3de95b3; (* vsli.64 d25, d19, #0x1e *)
  0xf343e1b4; (* veor d30, d19, d20 *)
  0xf3d9a5b3; (* vsli.64 d26, d19, #0x19 *)
  0xf34821b9; (* veor d18, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf355e1b4; (* vbsl d30, d21, d20 *)
  0xf34221ba; (* veor d18, d18, d26 *)
  0xf27668ab; (* vadd.i64 d22, d22, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b6; (* vshr.u64 d24, d22, #0xe *)
  0xf42167cd; (* vld1.64 {d6}, [r1]! *)
  0xf3ee90b6; (* vshr.u64 d25, d22, #0x12 *)
  0xf27228ae; (* vadd.i64 d18, d18, d30 *)
  0xf3d7a0b6; (* vshr.u64 d26, d22, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b6; (* vsli.64 d24, d22, #0x32 *)
  0xf3ee95b6; (* vsli.64 d25, d22, #0x2e *)
  0xf266d1b6; (* vorr d29, d22, d22 *)
  0xf3d7a5b6; (* vsli.64 d26, d22, #0x17 *)
  0xf3b06006; (* vrev64.8 d6, d6 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf357d1b0; (* vbsl d29, d23, d16 *)
  0xf3e480b2; (* vshr.u64 d24, d18, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a1; (* vadd.i64 d27, d29, d17 *)
  0xf3de90b2; (* vshr.u64 d25, d18, #0x22 *)
  0xf3e485b2; (* vsli.64 d24, d18, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b2; (* vshr.u64 d26, d18, #0x27 *)
  0xf27cc886; (* vadd.i64 d28, d28, d6 *)
  0xf3de95b2; (* vsli.64 d25, d18, #0x1e *)
  0xf342e1b3; (* veor d30, d18, d19 *)
  0xf3d9a5b2; (* vsli.64 d26, d18, #0x19 *)
  0xf34811b9; (* veor d17, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf354e1b3; (* vbsl d30, d20, d19 *)
  0xf34111ba; (* veor d17, d17, d26 *)
  0xf27558ab; (* vadd.i64 d21, d21, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b5; (* vshr.u64 d24, d21, #0xe *)
  0xf42177cd; (* vld1.64 {d7}, [r1]! *)
  0xf3ee90b5; (* vshr.u64 d25, d21, #0x12 *)
  0xf27118ae; (* vadd.i64 d17, d17, d30 *)
  0xf3d7a0b5; (* vshr.u64 d26, d21, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b5; (* vsli.64 d24, d21, #0x32 *)
  0xf3ee95b5; (* vsli.64 d25, d21, #0x2e *)
  0xf265d1b5; (* vorr d29, d21, d21 *)
  0xf3d7a5b5; (* vsli.64 d26, d21, #0x17 *)
  0xf3b07007; (* vrev64.8 d7, d7 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf356d1b7; (* vbsl d29, d22, d23 *)
  0xf3e480b1; (* vshr.u64 d24, d17, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a0; (* vadd.i64 d27, d29, d16 *)
  0xf3de90b1; (* vshr.u64 d25, d17, #0x22 *)
  0xf3e485b1; (* vsli.64 d24, d17, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b1; (* vshr.u64 d26, d17, #0x27 *)
  0xf27cc887; (* vadd.i64 d28, d28, d7 *)
  0xf3de95b1; (* vsli.64 d25, d17, #0x1e *)
  0xf341e1b2; (* veor d30, d17, d18 *)
  0xf3d9a5b1; (* vsli.64 d26, d17, #0x19 *)
  0xf34801b9; (* veor d16, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf353e1b2; (* vbsl d30, d19, d18 *)
  0xf34001ba; (* veor d16, d16, d26 *)
  0xf27448ab; (* vadd.i64 d20, d20, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b4; (* vshr.u64 d24, d20, #0xe *)
  0xf42187cd; (* vld1.64 {d8}, [r1]! *)
  0xf3ee90b4; (* vshr.u64 d25, d20, #0x12 *)
  0xf27008ae; (* vadd.i64 d16, d16, d30 *)
  0xf3d7a0b4; (* vshr.u64 d26, d20, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b4; (* vsli.64 d24, d20, #0x32 *)
  0xf3ee95b4; (* vsli.64 d25, d20, #0x2e *)
  0xf264d1b4; (* vorr d29, d20, d20 *)
  0xf3d7a5b4; (* vsli.64 d26, d20, #0x17 *)
  0xf3b08008; (* vrev64.8 d8, d8 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf355d1b6; (* vbsl d29, d21, d22 *)
  0xf3e480b0; (* vshr.u64 d24, d16, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a7; (* vadd.i64 d27, d29, d23 *)
  0xf3de90b0; (* vshr.u64 d25, d16, #0x22 *)
  0xf3e485b0; (* vsli.64 d24, d16, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b0; (* vshr.u64 d26, d16, #0x27 *)
  0xf27cc888; (* vadd.i64 d28, d28, d8 *)
  0xf3de95b0; (* vsli.64 d25, d16, #0x1e *)
  0xf340e1b1; (* veor d30, d16, d17 *)
  0xf3d9a5b0; (* vsli.64 d26, d16, #0x19 *)
  0xf34871b9; (* veor d23, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf352e1b1; (* vbsl d30, d18, d17 *)
  0xf34771ba; (* veor d23, d23, d26 *)
  0xf27338ab; (* vadd.i64 d19, d19, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b3; (* vshr.u64 d24, d19, #0xe *)
  0xf42197cd; (* vld1.64 {d9}, [r1]! *)
  0xf3ee90b3; (* vshr.u64 d25, d19, #0x12 *)
  0xf27778ae; (* vadd.i64 d23, d23, d30 *)
  0xf3d7a0b3; (* vshr.u64 d26, d19, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b3; (* vsli.64 d24, d19, #0x32 *)
  0xf3ee95b3; (* vsli.64 d25, d19, #0x2e *)
  0xf263d1b3; (* vorr d29, d19, d19 *)
  0xf3d7a5b3; (* vsli.64 d26, d19, #0x17 *)
  0xf3b09009; (* vrev64.8 d9, d9 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf354d1b5; (* vbsl d29, d20, d21 *)
  0xf3e480b7; (* vshr.u64 d24, d23, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a6; (* vadd.i64 d27, d29, d22 *)
  0xf3de90b7; (* vshr.u64 d25, d23, #0x22 *)
  0xf3e485b7; (* vsli.64 d24, d23, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b7; (* vshr.u64 d26, d23, #0x27 *)
  0xf27cc889; (* vadd.i64 d28, d28, d9 *)
  0xf3de95b7; (* vsli.64 d25, d23, #0x1e *)
  0xf347e1b0; (* veor d30, d23, d16 *)
  0xf3d9a5b7; (* vsli.64 d26, d23, #0x19 *)
  0xf34861b9; (* veor d22, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf351e1b0; (* vbsl d30, d17, d16 *)
  0xf34661ba; (* veor d22, d22, d26 *)
  0xf27228ab; (* vadd.i64 d18, d18, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b2; (* vshr.u64 d24, d18, #0xe *)
  0xf421a7cd; (* vld1.64 {d10}, [r1]! *)
  0xf3ee90b2; (* vshr.u64 d25, d18, #0x12 *)
  0xf27668ae; (* vadd.i64 d22, d22, d30 *)
  0xf3d7a0b2; (* vshr.u64 d26, d18, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b2; (* vsli.64 d24, d18, #0x32 *)
  0xf3ee95b2; (* vsli.64 d25, d18, #0x2e *)
  0xf262d1b2; (* vorr d29, d18, d18 *)
  0xf3d7a5b2; (* vsli.64 d26, d18, #0x17 *)
  0xf3b0a00a; (* vrev64.8 d10, d10 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf353d1b4; (* vbsl d29, d19, d20 *)
  0xf3e480b6; (* vshr.u64 d24, d22, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a5; (* vadd.i64 d27, d29, d21 *)
  0xf3de90b6; (* vshr.u64 d25, d22, #0x22 *)
  0xf3e485b6; (* vsli.64 d24, d22, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b6; (* vshr.u64 d26, d22, #0x27 *)
  0xf27cc88a; (* vadd.i64 d28, d28, d10 *)
  0xf3de95b6; (* vsli.64 d25, d22, #0x1e *)
  0xf346e1b7; (* veor d30, d22, d23 *)
  0xf3d9a5b6; (* vsli.64 d26, d22, #0x19 *)
  0xf34851b9; (* veor d21, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf350e1b7; (* vbsl d30, d16, d23 *)
  0xf34551ba; (* veor d21, d21, d26 *)
  0xf27118ab; (* vadd.i64 d17, d17, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b1; (* vshr.u64 d24, d17, #0xe *)
  0xf421b7cd; (* vld1.64 {d11}, [r1]! *)
  0xf3ee90b1; (* vshr.u64 d25, d17, #0x12 *)
  0xf27558ae; (* vadd.i64 d21, d21, d30 *)
  0xf3d7a0b1; (* vshr.u64 d26, d17, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b1; (* vsli.64 d24, d17, #0x32 *)
  0xf3ee95b1; (* vsli.64 d25, d17, #0x2e *)
  0xf261d1b1; (* vorr d29, d17, d17 *)
  0xf3d7a5b1; (* vsli.64 d26, d17, #0x17 *)
  0xf3b0b00b; (* vrev64.8 d11, d11 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf352d1b3; (* vbsl d29, d18, d19 *)
  0xf3e480b5; (* vshr.u64 d24, d21, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a4; (* vadd.i64 d27, d29, d20 *)
  0xf3de90b5; (* vshr.u64 d25, d21, #0x22 *)
  0xf3e485b5; (* vsli.64 d24, d21, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b5; (* vshr.u64 d26, d21, #0x27 *)
  0xf27cc88b; (* vadd.i64 d28, d28, d11 *)
  0xf3de95b5; (* vsli.64 d25, d21, #0x1e *)
  0xf345e1b6; (* veor d30, d21, d22 *)
  0xf3d9a5b5; (* vsli.64 d26, d21, #0x19 *)
  0xf34841b9; (* veor d20, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf357e1b6; (* vbsl d30, d23, d22 *)
  0xf34441ba; (* veor d20, d20, d26 *)
  0xf27008ab; (* vadd.i64 d16, d16, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b0; (* vshr.u64 d24, d16, #0xe *)
  0xf421c7cd; (* vld1.64 {d12}, [r1]! *)
  0xf3ee90b0; (* vshr.u64 d25, d16, #0x12 *)
  0xf27448ae; (* vadd.i64 d20, d20, d30 *)
  0xf3d7a0b0; (* vshr.u64 d26, d16, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b0; (* vsli.64 d24, d16, #0x32 *)
  0xf3ee95b0; (* vsli.64 d25, d16, #0x2e *)
  0xf260d1b0; (* vorr d29, d16, d16 *)
  0xf3d7a5b0; (* vsli.64 d26, d16, #0x17 *)
  0xf3b0c00c; (* vrev64.8 d12, d12 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf351d1b2; (* vbsl d29, d17, d18 *)
  0xf3e480b4; (* vshr.u64 d24, d20, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a3; (* vadd.i64 d27, d29, d19 *)
  0xf3de90b4; (* vshr.u64 d25, d20, #0x22 *)
  0xf3e485b4; (* vsli.64 d24, d20, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b4; (* vshr.u64 d26, d20, #0x27 *)
  0xf27cc88c; (* vadd.i64 d28, d28, d12 *)
  0xf3de95b4; (* vsli.64 d25, d20, #0x1e *)
  0xf344e1b5; (* veor d30, d20, d21 *)
  0xf3d9a5b4; (* vsli.64 d26, d20, #0x19 *)
  0xf34831b9; (* veor d19, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf356e1b5; (* vbsl d30, d22, d21 *)
  0xf34331ba; (* veor d19, d19, d26 *)
  0xf27778ab; (* vadd.i64 d23, d23, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b7; (* vshr.u64 d24, d23, #0xe *)
  0xf421d7cd; (* vld1.64 {d13}, [r1]! *)
  0xf3ee90b7; (* vshr.u64 d25, d23, #0x12 *)
  0xf27338ae; (* vadd.i64 d19, d19, d30 *)
  0xf3d7a0b7; (* vshr.u64 d26, d23, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b7; (* vsli.64 d24, d23, #0x32 *)
  0xf3ee95b7; (* vsli.64 d25, d23, #0x2e *)
  0xf267d1b7; (* vorr d29, d23, d23 *)
  0xf3d7a5b7; (* vsli.64 d26, d23, #0x17 *)
  0xf3b0d00d; (* vrev64.8 d13, d13 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf350d1b1; (* vbsl d29, d16, d17 *)
  0xf3e480b3; (* vshr.u64 d24, d19, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a2; (* vadd.i64 d27, d29, d18 *)
  0xf3de90b3; (* vshr.u64 d25, d19, #0x22 *)
  0xf3e485b3; (* vsli.64 d24, d19, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b3; (* vshr.u64 d26, d19, #0x27 *)
  0xf27cc88d; (* vadd.i64 d28, d28, d13 *)
  0xf3de95b3; (* vsli.64 d25, d19, #0x1e *)
  0xf343e1b4; (* veor d30, d19, d20 *)
  0xf3d9a5b3; (* vsli.64 d26, d19, #0x19 *)
  0xf34821b9; (* veor d18, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf355e1b4; (* vbsl d30, d21, d20 *)
  0xf34221ba; (* veor d18, d18, d26 *)
  0xf27668ab; (* vadd.i64 d22, d22, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b6; (* vshr.u64 d24, d22, #0xe *)
  0xf421e7cd; (* vld1.64 {d14}, [r1]! *)
  0xf3ee90b6; (* vshr.u64 d25, d22, #0x12 *)
  0xf27228ae; (* vadd.i64 d18, d18, d30 *)
  0xf3d7a0b6; (* vshr.u64 d26, d22, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b6; (* vsli.64 d24, d22, #0x32 *)
  0xf3ee95b6; (* vsli.64 d25, d22, #0x2e *)
  0xf266d1b6; (* vorr d29, d22, d22 *)
  0xf3d7a5b6; (* vsli.64 d26, d22, #0x17 *)
  0xf3b0e00e; (* vrev64.8 d14, d14 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf357d1b0; (* vbsl d29, d23, d16 *)
  0xf3e480b2; (* vshr.u64 d24, d18, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a1; (* vadd.i64 d27, d29, d17 *)
  0xf3de90b2; (* vshr.u64 d25, d18, #0x22 *)
  0xf3e485b2; (* vsli.64 d24, d18, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b2; (* vshr.u64 d26, d18, #0x27 *)
  0xf27cc88e; (* vadd.i64 d28, d28, d14 *)
  0xf3de95b2; (* vsli.64 d25, d18, #0x1e *)
  0xf342e1b3; (* veor d30, d18, d19 *)
  0xf3d9a5b2; (* vsli.64 d26, d18, #0x19 *)
  0xf34811b9; (* veor d17, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf354e1b3; (* vbsl d30, d20, d19 *)
  0xf34111ba; (* veor d17, d17, d26 *)
  0xf27558ab; (* vadd.i64 d21, d21, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b5; (* vshr.u64 d24, d21, #0xe *)
  0xf421f7cd; (* vld1.64 {d15}, [r1]! *)
  0xf3ee90b5; (* vshr.u64 d25, d21, #0x12 *)
  0xf27118ae; (* vadd.i64 d17, d17, d30 *)
  0xf3d7a0b5; (* vshr.u64 d26, d21, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b5; (* vsli.64 d24, d21, #0x32 *)
  0xf3ee95b5; (* vsli.64 d25, d21, #0x2e *)
  0xf265d1b5; (* vorr d29, d21, d21 *)
  0xf3d7a5b5; (* vsli.64 d26, d21, #0x17 *)
  0xf3b0f00f; (* vrev64.8 d15, d15 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf356d1b7; (* vbsl d29, d22, d23 *)
  0xf3e480b1; (* vshr.u64 d24, d17, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a0; (* vadd.i64 d27, d29, d16 *)
  0xf3de90b1; (* vshr.u64 d25, d17, #0x22 *)
  0xf3e485b1; (* vsli.64 d24, d17, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b1; (* vshr.u64 d26, d17, #0x27 *)
  0xf27cc88f; (* vadd.i64 d28, d28, d15 *)
  0xf3de95b1; (* vsli.64 d25, d17, #0x1e *)
  0xf341e1b2; (* veor d30, d17, d18 *)
  0xf3d9a5b1; (* vsli.64 d26, d17, #0x19 *)
  0xf34801b9; (* veor d16, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf353e1b2; (* vbsl d30, d19, d18 *)
  0xf34001ba; (* veor d16, d16, d26 *)
  0xf27448ab; (* vadd.i64 d20, d20, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xe3a0c004; (* mov r12, #4 *)
  0xe25cc001; (* subs r12, r12, #1 *)
  0xf3ed80de; (* vshr.u64 q12, q7, #0x13 *)
  0xf3c3a0de; (* vshr.u64 q13, q7, #0x3d *)
  0xf27008ae; (* vadd.i64 d16, d16, d30 *)
  0xf3fae0de; (* vshr.u64 q15, q7, #0x6 *)
  0xf3ed85de; (* vsli.64 q12, q7, #0x2d *)
  0xf2f0c842; (* vext.64 q14, q0, q1, #0x1 *)
  0xf3c3a5de; (* vsli.64 q13, q7, #0x3 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3ff80fc; (* vshr.u64 q12, q14, #0x1 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3f8a0fc; (* vshr.u64 q13, q14, #0x8 *)
  0xf230086e; (* vadd.i64 q0, q0, q15 *)
  0xf3f9e0fc; (* vshr.u64 q15, q14, #0x7 *)
  0xf3ff85fc; (* vsli.64 q12, q14, #0x3f *)
  0xf3f8a5fc; (* vsli.64 q13, q14, #0x38 *)
  0xf2f8c84a; (* vext.64 q14, q4, q5, #0x1 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3f280b4; (* vshr.u64 d24, d20, #0xe *)
  0xf230086c; (* vadd.i64 q0, q0, q14 *)
  0xf3ee90b4; (* vshr.u64 d25, d20, #0x12 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3d7a0b4; (* vshr.u64 d26, d20, #0x29 *)
  0xf230086e; (* vadd.i64 q0, q0, q15 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b4; (* vsli.64 d24, d20, #0x32 *)
  0xf3ee95b4; (* vsli.64 d25, d20, #0x2e *)
  0xf264d1b4; (* vorr d29, d20, d20 *)
  0xf3d7a5b4; (* vsli.64 d26, d20, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf355d1b6; (* vbsl d29, d21, d22 *)
  0xf3e480b0; (* vshr.u64 d24, d16, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a7; (* vadd.i64 d27, d29, d23 *)
  0xf3de90b0; (* vshr.u64 d25, d16, #0x22 *)
  0xf3e485b0; (* vsli.64 d24, d16, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b0; (* vshr.u64 d26, d16, #0x27 *)
  0xf27cc880; (* vadd.i64 d28, d28, d0 *)
  0xf3de95b0; (* vsli.64 d25, d16, #0x1e *)
  0xf340e1b1; (* veor d30, d16, d17 *)
  0xf3d9a5b0; (* vsli.64 d26, d16, #0x19 *)
  0xf34871b9; (* veor d23, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf352e1b1; (* vbsl d30, d18, d17 *)
  0xf34771ba; (* veor d23, d23, d26 *)
  0xf27338ab; (* vadd.i64 d19, d19, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b3; (* vshr.u64 d24, d19, #0xe *)
  0xf3ee90b3; (* vshr.u64 d25, d19, #0x12 *)
  0xf27778ae; (* vadd.i64 d23, d23, d30 *)
  0xf3d7a0b3; (* vshr.u64 d26, d19, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b3; (* vsli.64 d24, d19, #0x32 *)
  0xf3ee95b3; (* vsli.64 d25, d19, #0x2e *)
  0xf263d1b3; (* vorr d29, d19, d19 *)
  0xf3d7a5b3; (* vsli.64 d26, d19, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf354d1b5; (* vbsl d29, d20, d21 *)
  0xf3e480b7; (* vshr.u64 d24, d23, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a6; (* vadd.i64 d27, d29, d22 *)
  0xf3de90b7; (* vshr.u64 d25, d23, #0x22 *)
  0xf3e485b7; (* vsli.64 d24, d23, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b7; (* vshr.u64 d26, d23, #0x27 *)
  0xf27cc881; (* vadd.i64 d28, d28, d1 *)
  0xf3de95b7; (* vsli.64 d25, d23, #0x1e *)
  0xf347e1b0; (* veor d30, d23, d16 *)
  0xf3d9a5b7; (* vsli.64 d26, d23, #0x19 *)
  0xf34861b9; (* veor d22, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf351e1b0; (* vbsl d30, d17, d16 *)
  0xf34661ba; (* veor d22, d22, d26 *)
  0xf27228ab; (* vadd.i64 d18, d18, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3ed80d0; (* vshr.u64 q12, q0, #0x13 *)
  0xf3c3a0d0; (* vshr.u64 q13, q0, #0x3d *)
  0xf27668ae; (* vadd.i64 d22, d22, d30 *)
  0xf3fae0d0; (* vshr.u64 q15, q0, #0x6 *)
  0xf3ed85d0; (* vsli.64 q12, q0, #0x2d *)
  0xf2f2c844; (* vext.64 q14, q1, q2, #0x1 *)
  0xf3c3a5d0; (* vsli.64 q13, q0, #0x3 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3ff80fc; (* vshr.u64 q12, q14, #0x1 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3f8a0fc; (* vshr.u64 q13, q14, #0x8 *)
  0xf232286e; (* vadd.i64 q1, q1, q15 *)
  0xf3f9e0fc; (* vshr.u64 q15, q14, #0x7 *)
  0xf3ff85fc; (* vsli.64 q12, q14, #0x3f *)
  0xf3f8a5fc; (* vsli.64 q13, q14, #0x38 *)
  0xf2fac84c; (* vext.64 q14, q5, q6, #0x1 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3f280b2; (* vshr.u64 d24, d18, #0xe *)
  0xf232286c; (* vadd.i64 q1, q1, q14 *)
  0xf3ee90b2; (* vshr.u64 d25, d18, #0x12 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3d7a0b2; (* vshr.u64 d26, d18, #0x29 *)
  0xf232286e; (* vadd.i64 q1, q1, q15 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b2; (* vsli.64 d24, d18, #0x32 *)
  0xf3ee95b2; (* vsli.64 d25, d18, #0x2e *)
  0xf262d1b2; (* vorr d29, d18, d18 *)
  0xf3d7a5b2; (* vsli.64 d26, d18, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf353d1b4; (* vbsl d29, d19, d20 *)
  0xf3e480b6; (* vshr.u64 d24, d22, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a5; (* vadd.i64 d27, d29, d21 *)
  0xf3de90b6; (* vshr.u64 d25, d22, #0x22 *)
  0xf3e485b6; (* vsli.64 d24, d22, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b6; (* vshr.u64 d26, d22, #0x27 *)
  0xf27cc882; (* vadd.i64 d28, d28, d2 *)
  0xf3de95b6; (* vsli.64 d25, d22, #0x1e *)
  0xf346e1b7; (* veor d30, d22, d23 *)
  0xf3d9a5b6; (* vsli.64 d26, d22, #0x19 *)
  0xf34851b9; (* veor d21, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf350e1b7; (* vbsl d30, d16, d23 *)
  0xf34551ba; (* veor d21, d21, d26 *)
  0xf27118ab; (* vadd.i64 d17, d17, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b1; (* vshr.u64 d24, d17, #0xe *)
  0xf3ee90b1; (* vshr.u64 d25, d17, #0x12 *)
  0xf27558ae; (* vadd.i64 d21, d21, d30 *)
  0xf3d7a0b1; (* vshr.u64 d26, d17, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b1; (* vsli.64 d24, d17, #0x32 *)
  0xf3ee95b1; (* vsli.64 d25, d17, #0x2e *)
  0xf261d1b1; (* vorr d29, d17, d17 *)
  0xf3d7a5b1; (* vsli.64 d26, d17, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf352d1b3; (* vbsl d29, d18, d19 *)
  0xf3e480b5; (* vshr.u64 d24, d21, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a4; (* vadd.i64 d27, d29, d20 *)
  0xf3de90b5; (* vshr.u64 d25, d21, #0x22 *)
  0xf3e485b5; (* vsli.64 d24, d21, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b5; (* vshr.u64 d26, d21, #0x27 *)
  0xf27cc883; (* vadd.i64 d28, d28, d3 *)
  0xf3de95b5; (* vsli.64 d25, d21, #0x1e *)
  0xf345e1b6; (* veor d30, d21, d22 *)
  0xf3d9a5b5; (* vsli.64 d26, d21, #0x19 *)
  0xf34841b9; (* veor d20, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf357e1b6; (* vbsl d30, d23, d22 *)
  0xf34441ba; (* veor d20, d20, d26 *)
  0xf27008ab; (* vadd.i64 d16, d16, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3ed80d2; (* vshr.u64 q12, q1, #0x13 *)
  0xf3c3a0d2; (* vshr.u64 q13, q1, #0x3d *)
  0xf27448ae; (* vadd.i64 d20, d20, d30 *)
  0xf3fae0d2; (* vshr.u64 q15, q1, #0x6 *)
  0xf3ed85d2; (* vsli.64 q12, q1, #0x2d *)
  0xf2f4c846; (* vext.64 q14, q2, q3, #0x1 *)
  0xf3c3a5d2; (* vsli.64 q13, q1, #0x3 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3ff80fc; (* vshr.u64 q12, q14, #0x1 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3f8a0fc; (* vshr.u64 q13, q14, #0x8 *)
  0xf234486e; (* vadd.i64 q2, q2, q15 *)
  0xf3f9e0fc; (* vshr.u64 q15, q14, #0x7 *)
  0xf3ff85fc; (* vsli.64 q12, q14, #0x3f *)
  0xf3f8a5fc; (* vsli.64 q13, q14, #0x38 *)
  0xf2fcc84e; (* vext.64 q14, q6, q7, #0x1 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3f280b0; (* vshr.u64 d24, d16, #0xe *)
  0xf234486c; (* vadd.i64 q2, q2, q14 *)
  0xf3ee90b0; (* vshr.u64 d25, d16, #0x12 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3d7a0b0; (* vshr.u64 d26, d16, #0x29 *)
  0xf234486e; (* vadd.i64 q2, q2, q15 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b0; (* vsli.64 d24, d16, #0x32 *)
  0xf3ee95b0; (* vsli.64 d25, d16, #0x2e *)
  0xf260d1b0; (* vorr d29, d16, d16 *)
  0xf3d7a5b0; (* vsli.64 d26, d16, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf351d1b2; (* vbsl d29, d17, d18 *)
  0xf3e480b4; (* vshr.u64 d24, d20, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a3; (* vadd.i64 d27, d29, d19 *)
  0xf3de90b4; (* vshr.u64 d25, d20, #0x22 *)
  0xf3e485b4; (* vsli.64 d24, d20, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b4; (* vshr.u64 d26, d20, #0x27 *)
  0xf27cc884; (* vadd.i64 d28, d28, d4 *)
  0xf3de95b4; (* vsli.64 d25, d20, #0x1e *)
  0xf344e1b5; (* veor d30, d20, d21 *)
  0xf3d9a5b4; (* vsli.64 d26, d20, #0x19 *)
  0xf34831b9; (* veor d19, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf356e1b5; (* vbsl d30, d22, d21 *)
  0xf34331ba; (* veor d19, d19, d26 *)
  0xf27778ab; (* vadd.i64 d23, d23, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b7; (* vshr.u64 d24, d23, #0xe *)
  0xf3ee90b7; (* vshr.u64 d25, d23, #0x12 *)
  0xf27338ae; (* vadd.i64 d19, d19, d30 *)
  0xf3d7a0b7; (* vshr.u64 d26, d23, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b7; (* vsli.64 d24, d23, #0x32 *)
  0xf3ee95b7; (* vsli.64 d25, d23, #0x2e *)
  0xf267d1b7; (* vorr d29, d23, d23 *)
  0xf3d7a5b7; (* vsli.64 d26, d23, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf350d1b1; (* vbsl d29, d16, d17 *)
  0xf3e480b3; (* vshr.u64 d24, d19, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a2; (* vadd.i64 d27, d29, d18 *)
  0xf3de90b3; (* vshr.u64 d25, d19, #0x22 *)
  0xf3e485b3; (* vsli.64 d24, d19, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b3; (* vshr.u64 d26, d19, #0x27 *)
  0xf27cc885; (* vadd.i64 d28, d28, d5 *)
  0xf3de95b3; (* vsli.64 d25, d19, #0x1e *)
  0xf343e1b4; (* veor d30, d19, d20 *)
  0xf3d9a5b3; (* vsli.64 d26, d19, #0x19 *)
  0xf34821b9; (* veor d18, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf355e1b4; (* vbsl d30, d21, d20 *)
  0xf34221ba; (* veor d18, d18, d26 *)
  0xf27668ab; (* vadd.i64 d22, d22, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3ed80d4; (* vshr.u64 q12, q2, #0x13 *)
  0xf3c3a0d4; (* vshr.u64 q13, q2, #0x3d *)
  0xf27228ae; (* vadd.i64 d18, d18, d30 *)
  0xf3fae0d4; (* vshr.u64 q15, q2, #0x6 *)
  0xf3ed85d4; (* vsli.64 q12, q2, #0x2d *)
  0xf2f6c848; (* vext.64 q14, q3, q4, #0x1 *)
  0xf3c3a5d4; (* vsli.64 q13, q2, #0x3 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3ff80fc; (* vshr.u64 q12, q14, #0x1 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3f8a0fc; (* vshr.u64 q13, q14, #0x8 *)
  0xf236686e; (* vadd.i64 q3, q3, q15 *)
  0xf3f9e0fc; (* vshr.u64 q15, q14, #0x7 *)
  0xf3ff85fc; (* vsli.64 q12, q14, #0x3f *)
  0xf3f8a5fc; (* vsli.64 q13, q14, #0x38 *)
  0xf2fec840; (* vext.64 q14, q7, q0, #0x1 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3f280b6; (* vshr.u64 d24, d22, #0xe *)
  0xf236686c; (* vadd.i64 q3, q3, q14 *)
  0xf3ee90b6; (* vshr.u64 d25, d22, #0x12 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3d7a0b6; (* vshr.u64 d26, d22, #0x29 *)
  0xf236686e; (* vadd.i64 q3, q3, q15 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b6; (* vsli.64 d24, d22, #0x32 *)
  0xf3ee95b6; (* vsli.64 d25, d22, #0x2e *)
  0xf266d1b6; (* vorr d29, d22, d22 *)
  0xf3d7a5b6; (* vsli.64 d26, d22, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf357d1b0; (* vbsl d29, d23, d16 *)
  0xf3e480b2; (* vshr.u64 d24, d18, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a1; (* vadd.i64 d27, d29, d17 *)
  0xf3de90b2; (* vshr.u64 d25, d18, #0x22 *)
  0xf3e485b2; (* vsli.64 d24, d18, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b2; (* vshr.u64 d26, d18, #0x27 *)
  0xf27cc886; (* vadd.i64 d28, d28, d6 *)
  0xf3de95b2; (* vsli.64 d25, d18, #0x1e *)
  0xf342e1b3; (* veor d30, d18, d19 *)
  0xf3d9a5b2; (* vsli.64 d26, d18, #0x19 *)
  0xf34811b9; (* veor d17, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf354e1b3; (* vbsl d30, d20, d19 *)
  0xf34111ba; (* veor d17, d17, d26 *)
  0xf27558ab; (* vadd.i64 d21, d21, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b5; (* vshr.u64 d24, d21, #0xe *)
  0xf3ee90b5; (* vshr.u64 d25, d21, #0x12 *)
  0xf27118ae; (* vadd.i64 d17, d17, d30 *)
  0xf3d7a0b5; (* vshr.u64 d26, d21, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b5; (* vsli.64 d24, d21, #0x32 *)
  0xf3ee95b5; (* vsli.64 d25, d21, #0x2e *)
  0xf265d1b5; (* vorr d29, d21, d21 *)
  0xf3d7a5b5; (* vsli.64 d26, d21, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf356d1b7; (* vbsl d29, d22, d23 *)
  0xf3e480b1; (* vshr.u64 d24, d17, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a0; (* vadd.i64 d27, d29, d16 *)
  0xf3de90b1; (* vshr.u64 d25, d17, #0x22 *)
  0xf3e485b1; (* vsli.64 d24, d17, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b1; (* vshr.u64 d26, d17, #0x27 *)
  0xf27cc887; (* vadd.i64 d28, d28, d7 *)
  0xf3de95b1; (* vsli.64 d25, d17, #0x1e *)
  0xf341e1b2; (* veor d30, d17, d18 *)
  0xf3d9a5b1; (* vsli.64 d26, d17, #0x19 *)
  0xf34801b9; (* veor d16, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf353e1b2; (* vbsl d30, d19, d18 *)
  0xf34001ba; (* veor d16, d16, d26 *)
  0xf27448ab; (* vadd.i64 d20, d20, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3ed80d6; (* vshr.u64 q12, q3, #0x13 *)
  0xf3c3a0d6; (* vshr.u64 q13, q3, #0x3d *)
  0xf27008ae; (* vadd.i64 d16, d16, d30 *)
  0xf3fae0d6; (* vshr.u64 q15, q3, #0x6 *)
  0xf3ed85d6; (* vsli.64 q12, q3, #0x2d *)
  0xf2f8c84a; (* vext.64 q14, q4, q5, #0x1 *)
  0xf3c3a5d6; (* vsli.64 q13, q3, #0x3 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3ff80fc; (* vshr.u64 q12, q14, #0x1 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3f8a0fc; (* vshr.u64 q13, q14, #0x8 *)
  0xf238886e; (* vadd.i64 q4, q4, q15 *)
  0xf3f9e0fc; (* vshr.u64 q15, q14, #0x7 *)
  0xf3ff85fc; (* vsli.64 q12, q14, #0x3f *)
  0xf3f8a5fc; (* vsli.64 q13, q14, #0x38 *)
  0xf2f0c842; (* vext.64 q14, q0, q1, #0x1 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3f280b4; (* vshr.u64 d24, d20, #0xe *)
  0xf238886c; (* vadd.i64 q4, q4, q14 *)
  0xf3ee90b4; (* vshr.u64 d25, d20, #0x12 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3d7a0b4; (* vshr.u64 d26, d20, #0x29 *)
  0xf238886e; (* vadd.i64 q4, q4, q15 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b4; (* vsli.64 d24, d20, #0x32 *)
  0xf3ee95b4; (* vsli.64 d25, d20, #0x2e *)
  0xf264d1b4; (* vorr d29, d20, d20 *)
  0xf3d7a5b4; (* vsli.64 d26, d20, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf355d1b6; (* vbsl d29, d21, d22 *)
  0xf3e480b0; (* vshr.u64 d24, d16, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a7; (* vadd.i64 d27, d29, d23 *)
  0xf3de90b0; (* vshr.u64 d25, d16, #0x22 *)
  0xf3e485b0; (* vsli.64 d24, d16, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b0; (* vshr.u64 d26, d16, #0x27 *)
  0xf27cc888; (* vadd.i64 d28, d28, d8 *)
  0xf3de95b0; (* vsli.64 d25, d16, #0x1e *)
  0xf340e1b1; (* veor d30, d16, d17 *)
  0xf3d9a5b0; (* vsli.64 d26, d16, #0x19 *)
  0xf34871b9; (* veor d23, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf352e1b1; (* vbsl d30, d18, d17 *)
  0xf34771ba; (* veor d23, d23, d26 *)
  0xf27338ab; (* vadd.i64 d19, d19, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b3; (* vshr.u64 d24, d19, #0xe *)
  0xf3ee90b3; (* vshr.u64 d25, d19, #0x12 *)
  0xf27778ae; (* vadd.i64 d23, d23, d30 *)
  0xf3d7a0b3; (* vshr.u64 d26, d19, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b3; (* vsli.64 d24, d19, #0x32 *)
  0xf3ee95b3; (* vsli.64 d25, d19, #0x2e *)
  0xf263d1b3; (* vorr d29, d19, d19 *)
  0xf3d7a5b3; (* vsli.64 d26, d19, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf354d1b5; (* vbsl d29, d20, d21 *)
  0xf3e480b7; (* vshr.u64 d24, d23, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a6; (* vadd.i64 d27, d29, d22 *)
  0xf3de90b7; (* vshr.u64 d25, d23, #0x22 *)
  0xf3e485b7; (* vsli.64 d24, d23, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b7; (* vshr.u64 d26, d23, #0x27 *)
  0xf27cc889; (* vadd.i64 d28, d28, d9 *)
  0xf3de95b7; (* vsli.64 d25, d23, #0x1e *)
  0xf347e1b0; (* veor d30, d23, d16 *)
  0xf3d9a5b7; (* vsli.64 d26, d23, #0x19 *)
  0xf34861b9; (* veor d22, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf351e1b0; (* vbsl d30, d17, d16 *)
  0xf34661ba; (* veor d22, d22, d26 *)
  0xf27228ab; (* vadd.i64 d18, d18, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3ed80d8; (* vshr.u64 q12, q4, #0x13 *)
  0xf3c3a0d8; (* vshr.u64 q13, q4, #0x3d *)
  0xf27668ae; (* vadd.i64 d22, d22, d30 *)
  0xf3fae0d8; (* vshr.u64 q15, q4, #0x6 *)
  0xf3ed85d8; (* vsli.64 q12, q4, #0x2d *)
  0xf2fac84c; (* vext.64 q14, q5, q6, #0x1 *)
  0xf3c3a5d8; (* vsli.64 q13, q4, #0x3 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3ff80fc; (* vshr.u64 q12, q14, #0x1 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3f8a0fc; (* vshr.u64 q13, q14, #0x8 *)
  0xf23aa86e; (* vadd.i64 q5, q5, q15 *)
  0xf3f9e0fc; (* vshr.u64 q15, q14, #0x7 *)
  0xf3ff85fc; (* vsli.64 q12, q14, #0x3f *)
  0xf3f8a5fc; (* vsli.64 q13, q14, #0x38 *)
  0xf2f2c844; (* vext.64 q14, q1, q2, #0x1 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3f280b2; (* vshr.u64 d24, d18, #0xe *)
  0xf23aa86c; (* vadd.i64 q5, q5, q14 *)
  0xf3ee90b2; (* vshr.u64 d25, d18, #0x12 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3d7a0b2; (* vshr.u64 d26, d18, #0x29 *)
  0xf23aa86e; (* vadd.i64 q5, q5, q15 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b2; (* vsli.64 d24, d18, #0x32 *)
  0xf3ee95b2; (* vsli.64 d25, d18, #0x2e *)
  0xf262d1b2; (* vorr d29, d18, d18 *)
  0xf3d7a5b2; (* vsli.64 d26, d18, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf353d1b4; (* vbsl d29, d19, d20 *)
  0xf3e480b6; (* vshr.u64 d24, d22, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a5; (* vadd.i64 d27, d29, d21 *)
  0xf3de90b6; (* vshr.u64 d25, d22, #0x22 *)
  0xf3e485b6; (* vsli.64 d24, d22, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b6; (* vshr.u64 d26, d22, #0x27 *)
  0xf27cc88a; (* vadd.i64 d28, d28, d10 *)
  0xf3de95b6; (* vsli.64 d25, d22, #0x1e *)
  0xf346e1b7; (* veor d30, d22, d23 *)
  0xf3d9a5b6; (* vsli.64 d26, d22, #0x19 *)
  0xf34851b9; (* veor d21, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf350e1b7; (* vbsl d30, d16, d23 *)
  0xf34551ba; (* veor d21, d21, d26 *)
  0xf27118ab; (* vadd.i64 d17, d17, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b1; (* vshr.u64 d24, d17, #0xe *)
  0xf3ee90b1; (* vshr.u64 d25, d17, #0x12 *)
  0xf27558ae; (* vadd.i64 d21, d21, d30 *)
  0xf3d7a0b1; (* vshr.u64 d26, d17, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b1; (* vsli.64 d24, d17, #0x32 *)
  0xf3ee95b1; (* vsli.64 d25, d17, #0x2e *)
  0xf261d1b1; (* vorr d29, d17, d17 *)
  0xf3d7a5b1; (* vsli.64 d26, d17, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf352d1b3; (* vbsl d29, d18, d19 *)
  0xf3e480b5; (* vshr.u64 d24, d21, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a4; (* vadd.i64 d27, d29, d20 *)
  0xf3de90b5; (* vshr.u64 d25, d21, #0x22 *)
  0xf3e485b5; (* vsli.64 d24, d21, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b5; (* vshr.u64 d26, d21, #0x27 *)
  0xf27cc88b; (* vadd.i64 d28, d28, d11 *)
  0xf3de95b5; (* vsli.64 d25, d21, #0x1e *)
  0xf345e1b6; (* veor d30, d21, d22 *)
  0xf3d9a5b5; (* vsli.64 d26, d21, #0x19 *)
  0xf34841b9; (* veor d20, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf357e1b6; (* vbsl d30, d23, d22 *)
  0xf34441ba; (* veor d20, d20, d26 *)
  0xf27008ab; (* vadd.i64 d16, d16, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3ed80da; (* vshr.u64 q12, q5, #0x13 *)
  0xf3c3a0da; (* vshr.u64 q13, q5, #0x3d *)
  0xf27448ae; (* vadd.i64 d20, d20, d30 *)
  0xf3fae0da; (* vshr.u64 q15, q5, #0x6 *)
  0xf3ed85da; (* vsli.64 q12, q5, #0x2d *)
  0xf2fcc84e; (* vext.64 q14, q6, q7, #0x1 *)
  0xf3c3a5da; (* vsli.64 q13, q5, #0x3 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3ff80fc; (* vshr.u64 q12, q14, #0x1 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3f8a0fc; (* vshr.u64 q13, q14, #0x8 *)
  0xf23cc86e; (* vadd.i64 q6, q6, q15 *)
  0xf3f9e0fc; (* vshr.u64 q15, q14, #0x7 *)
  0xf3ff85fc; (* vsli.64 q12, q14, #0x3f *)
  0xf3f8a5fc; (* vsli.64 q13, q14, #0x38 *)
  0xf2f4c846; (* vext.64 q14, q2, q3, #0x1 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3f280b0; (* vshr.u64 d24, d16, #0xe *)
  0xf23cc86c; (* vadd.i64 q6, q6, q14 *)
  0xf3ee90b0; (* vshr.u64 d25, d16, #0x12 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3d7a0b0; (* vshr.u64 d26, d16, #0x29 *)
  0xf23cc86e; (* vadd.i64 q6, q6, q15 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b0; (* vsli.64 d24, d16, #0x32 *)
  0xf3ee95b0; (* vsli.64 d25, d16, #0x2e *)
  0xf260d1b0; (* vorr d29, d16, d16 *)
  0xf3d7a5b0; (* vsli.64 d26, d16, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf351d1b2; (* vbsl d29, d17, d18 *)
  0xf3e480b4; (* vshr.u64 d24, d20, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a3; (* vadd.i64 d27, d29, d19 *)
  0xf3de90b4; (* vshr.u64 d25, d20, #0x22 *)
  0xf3e485b4; (* vsli.64 d24, d20, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b4; (* vshr.u64 d26, d20, #0x27 *)
  0xf27cc88c; (* vadd.i64 d28, d28, d12 *)
  0xf3de95b4; (* vsli.64 d25, d20, #0x1e *)
  0xf344e1b5; (* veor d30, d20, d21 *)
  0xf3d9a5b4; (* vsli.64 d26, d20, #0x19 *)
  0xf34831b9; (* veor d19, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf356e1b5; (* vbsl d30, d22, d21 *)
  0xf34331ba; (* veor d19, d19, d26 *)
  0xf27778ab; (* vadd.i64 d23, d23, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b7; (* vshr.u64 d24, d23, #0xe *)
  0xf3ee90b7; (* vshr.u64 d25, d23, #0x12 *)
  0xf27338ae; (* vadd.i64 d19, d19, d30 *)
  0xf3d7a0b7; (* vshr.u64 d26, d23, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b7; (* vsli.64 d24, d23, #0x32 *)
  0xf3ee95b7; (* vsli.64 d25, d23, #0x2e *)
  0xf267d1b7; (* vorr d29, d23, d23 *)
  0xf3d7a5b7; (* vsli.64 d26, d23, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf350d1b1; (* vbsl d29, d16, d17 *)
  0xf3e480b3; (* vshr.u64 d24, d19, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a2; (* vadd.i64 d27, d29, d18 *)
  0xf3de90b3; (* vshr.u64 d25, d19, #0x22 *)
  0xf3e485b3; (* vsli.64 d24, d19, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b3; (* vshr.u64 d26, d19, #0x27 *)
  0xf27cc88d; (* vadd.i64 d28, d28, d13 *)
  0xf3de95b3; (* vsli.64 d25, d19, #0x1e *)
  0xf343e1b4; (* veor d30, d19, d20 *)
  0xf3d9a5b3; (* vsli.64 d26, d19, #0x19 *)
  0xf34821b9; (* veor d18, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf355e1b4; (* vbsl d30, d21, d20 *)
  0xf34221ba; (* veor d18, d18, d26 *)
  0xf27668ab; (* vadd.i64 d22, d22, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3ed80dc; (* vshr.u64 q12, q6, #0x13 *)
  0xf3c3a0dc; (* vshr.u64 q13, q6, #0x3d *)
  0xf27228ae; (* vadd.i64 d18, d18, d30 *)
  0xf3fae0dc; (* vshr.u64 q15, q6, #0x6 *)
  0xf3ed85dc; (* vsli.64 q12, q6, #0x2d *)
  0xf2fec840; (* vext.64 q14, q7, q0, #0x1 *)
  0xf3c3a5dc; (* vsli.64 q13, q6, #0x3 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3ff80fc; (* vshr.u64 q12, q14, #0x1 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3f8a0fc; (* vshr.u64 q13, q14, #0x8 *)
  0xf23ee86e; (* vadd.i64 q7, q7, q15 *)
  0xf3f9e0fc; (* vshr.u64 q15, q14, #0x7 *)
  0xf3ff85fc; (* vsli.64 q12, q14, #0x3f *)
  0xf3f8a5fc; (* vsli.64 q13, q14, #0x38 *)
  0xf2f6c848; (* vext.64 q14, q3, q4, #0x1 *)
  0xf34ee1f8; (* veor q15, q15, q12 *)
  0xf3f280b6; (* vshr.u64 d24, d22, #0xe *)
  0xf23ee86c; (* vadd.i64 q7, q7, q14 *)
  0xf3ee90b6; (* vshr.u64 d25, d22, #0x12 *)
  0xf34ee1fa; (* veor q15, q15, q13 *)
  0xf3d7a0b6; (* vshr.u64 d26, d22, #0x29 *)
  0xf23ee86e; (* vadd.i64 q7, q7, q15 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b6; (* vsli.64 d24, d22, #0x32 *)
  0xf3ee95b6; (* vsli.64 d25, d22, #0x2e *)
  0xf266d1b6; (* vorr d29, d22, d22 *)
  0xf3d7a5b6; (* vsli.64 d26, d22, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf357d1b0; (* vbsl d29, d23, d16 *)
  0xf3e480b2; (* vshr.u64 d24, d18, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a1; (* vadd.i64 d27, d29, d17 *)
  0xf3de90b2; (* vshr.u64 d25, d18, #0x22 *)
  0xf3e485b2; (* vsli.64 d24, d18, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b2; (* vshr.u64 d26, d18, #0x27 *)
  0xf27cc88e; (* vadd.i64 d28, d28, d14 *)
  0xf3de95b2; (* vsli.64 d25, d18, #0x1e *)
  0xf342e1b3; (* veor d30, d18, d19 *)
  0xf3d9a5b2; (* vsli.64 d26, d18, #0x19 *)
  0xf34811b9; (* veor d17, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf354e1b3; (* vbsl d30, d20, d19 *)
  0xf34111ba; (* veor d17, d17, d26 *)
  0xf27558ab; (* vadd.i64 d21, d21, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0xf3f280b5; (* vshr.u64 d24, d21, #0xe *)
  0xf3ee90b5; (* vshr.u64 d25, d21, #0x12 *)
  0xf27118ae; (* vadd.i64 d17, d17, d30 *)
  0xf3d7a0b5; (* vshr.u64 d26, d21, #0x29 *)
  0xf463c7dd; (* vld1.64 {d28}, [r3:64]! *)
  0xf3f285b5; (* vsli.64 d24, d21, #0x32 *)
  0xf3ee95b5; (* vsli.64 d25, d21, #0x2e *)
  0xf265d1b5; (* vorr d29, d21, d21 *)
  0xf3d7a5b5; (* vsli.64 d26, d21, #0x17 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xf356d1b7; (* vbsl d29, d22, d23 *)
  0xf3e480b1; (* vshr.u64 d24, d17, #0x1c *)
  0xf34aa1b9; (* veor d26, d26, d25 *)
  0xf27db8a0; (* vadd.i64 d27, d29, d16 *)
  0xf3de90b1; (* vshr.u64 d25, d17, #0x22 *)
  0xf3e485b1; (* vsli.64 d24, d17, #0x24 *)
  0xf27bb8aa; (* vadd.i64 d27, d27, d26 *)
  0xf3d9a0b1; (* vshr.u64 d26, d17, #0x27 *)
  0xf27cc88f; (* vadd.i64 d28, d28, d15 *)
  0xf3de95b1; (* vsli.64 d25, d17, #0x1e *)
  0xf341e1b2; (* veor d30, d17, d18 *)
  0xf3d9a5b1; (* vsli.64 d26, d17, #0x19 *)
  0xf34801b9; (* veor d16, d24, d25 *)
  0xf27bb8ac; (* vadd.i64 d27, d27, d28 *)
  0xf353e1b2; (* vbsl d30, d19, d18 *)
  0xf34001ba; (* veor d16, d16, d26 *)
  0xf27448ab; (* vadd.i64 d20, d20, d27 *)
  0xf27ee8ab; (* vadd.i64 d30, d30, d27 *)
  0x1afffda5; (* bne 0xed4 *)
  0xf27008ae; (* vadd.i64 d16, d16, d30 *)
  0xecd08b10; (* vldmia r0, {d24, d25, d26, d27, d28, d29, d30, d31} *)
  0xf27008e8; (* vadd.i64 q8, q8, q12 *)
  0xf27228ea; (* vadd.i64 q9, q9, q13 *)
  0xf27448ec; (* vadd.i64 q10, q10, q14 *)
  0xf27668ee; (* vadd.i64 q11, q11, q15 *)
  0xecc00b10; (* vstmia r0, {d16, d17, d18, d19, d20, d21, d22, d23} *)
  0xe1310002; (* teq r1, r2 *)
  0xe2433d0a; (* sub r3, r3, #640 *)
  0x1afffbbb; (* bne 0x754 *)
  0xecbd8b10; (* vpop {d8, d9, d10, d11, d12, d13, d14, d15} *)
  0xe12fff1e  (* bx lr *)
];;

let SHA512_ARMV4_EXEC = AARCH32_MK_EXEC_RULE sha512_armv4_mc;;

(* admin/prove writes sha512_block_data_order_neon's offset from K512 in
   rind's build to armv7/sha512_armv4.offset, and this fails unless it is
   0x740, the entry the theorems take, so the symbol rind calls is the code
   they are about. *)
let () =
  let offset =
    int_of_string (String.trim (Bytes.to_string
                                 (load_file "armv7/sha512_armv4.offset"))) in
  if offset <> 0x740 then
    failwith ("sha512_armv4: sha512_block_data_order_neon is at " ^
              string_of_int offset ^ ", not 0x740");;

(* ------------------------------------------------------------------------- *)
(* Reading K512 from the code.                                               *)
(* ------------------------------------------------------------------------- *)

let SHA512_READ_BYTELIST_EQ_BYTES = prove
 (`!(x:int32) l k (s:aarch32state).
        read (memory :> bytelist(x,k)) s = l <=>
        LENGTH l = k /\
        read (memory :> bytes(x,k)) s = num_of_bytelist l`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist; through; read] THEN
  MESON_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; BYTELIST_OF_NUM_OF_BYTELIST;
            READ_BYTES_BOUND_ALT; LENGTH_BYTELIST_OF_NUM]);;

let SHA512_LOADED_BYTES64 = prove
 (`!(s:aarch32state) (a:int32) b0 b1 b2 b3 b4 b5 b6 b7.
     bytes_loaded s a [b0;b1;b2;b3;b4;b5;b6;b7]
     ==> read (memory :> bytes64 a) s =
         word(num_of_bytelist [b0;b1;b2;b3;b4;b5;b6;b7])`,
  REWRITE_TAC[bytes_loaded; SHA512_READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[bytes64; asword; READ_COMPONENT_COMPOSE; through; read] THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN SIMP_TAC[]);;

(* SHA512_ARMV4_READ64 off: the doubleword the code holds at pc + off,
   `aligned_bytes_loaded s (word pc) sha512_armv4_mc ==>
    read (memory :> bytes64 (word (pc + off))) s = word v`. *)
let SHA512_ARMV4_READ64 =
  let mc_th = sha512_armv4_mc in
  fun off ->
    let th = SPECL [`s:aarch32state`; `word pc:int32`; `sha512_armv4_mc`;
                    mk_small_numeral off; `8`]
               aligned_bytes_loaded_sub_list in
    let th = CONV_RULE (LAND_CONV (RAND_CONV DIVIDES_CONV) THENC
               RAND_CONV (RAND_CONV (REWRITE_CONV[mc_th] THENC SUB_LIST_CONV) THENC
                          REWR_CONV aligned_bytes_loaded)) th in
    let th = MATCH_MP SHA512_LOADED_BYTES64 (CONJUNCT2 (UNDISCH (REWRITE_RULE[] th))) in
    let th = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV[num_of_bytelist] THENC
                                              DEPTH_CONV WORD_NUM_RED_CONV THENC
                                              NUM_REDUCE_CONV))) th in
    let th = REWRITE_RULE[GSYM WORD_ADD; ADD_CLAUSES] th in
    GEN_ALL (DISCH_ALL th);;

(* K512's 80 constants, as VLD1.64 reads them. *)
let SHA512_K_LOADS =
  let kel t = mk_comb(mk_comb(`EL:num->int64 list->int64`, mk_small_numeral t),
                      `sha512_constants`) in
  let addr t = if t = 0 then `word pc:int32` else
    mk_comb(mk_comb(`word_add:int32->int32->int32`, `word pc:int32`),
            mk_comb(`word:num->int32`, mk_small_numeral (8 * t))) in
  let fact t =
    mk_eq(vsubst [addr t,`a:int32`] `read (memory :> bytes64 a) (s:aarch32state)`, kel t) in
  prove
   (mk_imp(`aligned_bytes_loaded s (word pc) sha512_armv4_mc`,
           list_mk_conj(map fact (0--79))),
    DISCH_TAC THEN
    MAP_EVERY (fun t -> MP_TAC(SPECL [`pc:num`; `s:aarch32state`]
                                 (SHA512_ARMV4_READ64 (8 * t)))) (0--79) THEN
    ASM_REWRITE_TAC[WORD_ADD] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[sha512_constants] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
    CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The code's forms of FIPS 180-4's functions, rounds, and schedule.         *)
(* ------------------------------------------------------------------------- *)

(* VSHR then VSLI of the same lane is a rotation. *)
let SHA512_ROR_SLI =
  map (fun n ->
    let m = 64 - n in
    let tm = subst [mk_small_numeral m,`m:num`; mk_small_numeral n,`n:num`;
                    mk_numeral(power_num (num 2) (num m) -/ num 1),`k:num`]
      `!x:int64. word_or (word_shl x m) (word_and (word_ushr x n) (word k)) =
                 word_ror x n` in
    prove(tm, CONV_TAC WORD_BLAST))
  [14; 18; 41; 28; 34; 39; 19; 61; 1; 8];;

(* The code's forms of FIPS 180-4's functions. *)
let SHA512_NEON_FUNCTIONS = prove
 (`(!e:int64. word_xor (word_ror e 41) (word_xor (word_ror e 18) (word_ror e 14)) =
              sha512_hash_sigma_1 e) /\
   (!a:int64. word_xor (word_xor (word_ror a 28) (word_ror a 34)) (word_ror a 39) =
              sha512_hash_sigma_0 a) /\
   (!e f g:int64. word_or (word_and f e) (word_and g (word_not e)) =
                  sha512_choose e f g) /\
   (!a b c:int64. word_or (word_and c (word_xor a b)) (word_and b (word_not (word_xor a b))) =
                  sha512_maj a b c) /\
   (!x:int64. word_xor (word_xor (word_ushr x 6) (word_ror x 19)) (word_ror x 61) =
              sha512_msg_sigma_1 x) /\
   (!x:int64. word_xor (word_xor (word_ushr x 7) (word_ror x 1)) (word_ror x 8) =
              sha512_msg_sigma_0 x) /\
   (!x y:int64. word_add y (word_sub x y) = x)`,
  REWRITE_TAC[sha512_hash_sigma_0; sha512_hash_sigma_1; sha512_choose; sha512_maj;
              sha512_msg_sigma_0; sha512_msg_sigma_1] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_BLAST) THEN CONV_TAC WORD_RULE);;

let SHA512_REV_BYTEREVERSE = prove
 (`!x:int64. word_reversefields 8 (word_bytereverse x) = x`,
  GEN_TAC THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_REVERSEFIELDS; DIMINDEX_64] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* VBSL of a ^ b is Maj, which the choose form reaches first. *)
let SHA512_CHOOSE_MAJ = prove
 (`!a b c:int64. sha512_choose (word_xor a b) c b = sha512_maj a b c`,
  REWRITE_TAC[sha512_choose; sha512_maj] THEN CONV_TAC WORD_BLAST);;

(* Each state word but a and e is an earlier round's a or e. *)
let SHA512_ROUND_SHIFT = prove
 (`!w hh t.
     EL 1 (sha512_compress_rounds w hh (t + 1)) = EL 0 (sha512_compress_rounds w hh t) /\
     EL 2 (sha512_compress_rounds w hh (t + 1)) = EL 1 (sha512_compress_rounds w hh t) /\
     EL 3 (sha512_compress_rounds w hh (t + 1)) = EL 2 (sha512_compress_rounds w hh t) /\
     EL 5 (sha512_compress_rounds w hh (t + 1)) = EL 4 (sha512_compress_rounds w hh t) /\
     EL 6 (sha512_compress_rounds w hh (t + 1)) = EL 5 (sha512_compress_rounds w hh t) /\
     EL 7 (sha512_compress_rounds w hh (t + 1)) = EL 6 (sha512_compress_rounds w hh t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT2 sha512_compress_rounds; sha512_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* One round in the code's form: e's new value, and the sum the code adds
   to Sigma0 of a for a's in the next round. *)
let SHA512_NEON_ROUND = prove
 (`!w hh t.
     let S = sha512_compress_rounds w hh t
     and S' = sha512_compress_rounds w hh (t + 1) in
     let T1 = word_add (word_add (word_add (sha512_choose (EL 4 S) (EL 5 S) (EL 6 S))
                                           (EL 7 S))
                                 (sha512_hash_sigma_1 (EL 4 S)))
                       (word_add (EL t sha512_constants) (sha512_msg_schedule w t)) in
     word_add (EL 3 S) T1 = EL 4 S' /\
     word_add (sha512_maj (EL 0 S) (EL 1 S) (EL 2 S)) T1 =
     word_sub (EL 0 S') (sha512_hash_sigma_0 (EL 0 S))`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONJUNCT2 sha512_compress_rounds; sha512_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC WORD_RULE);;

(* The schedule's words from 16 on, as the code sums them. *)
let SHA512_NEON_SCHEDULE = prove
 (`!w t. word_add (word_add (word_add (sha512_msg_schedule w t)
                                      (sha512_msg_sigma_1 (sha512_msg_schedule w (t + 14))))
                            (sha512_msg_schedule w (t + 9)))
                  (sha512_msg_sigma_0 (sha512_msg_schedule w (t + 1))) =
         sha512_msg_schedule w (t + 16)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [sha512_msg_schedule] THEN
  REWRITE_TAC[ARITH_RULE `~(t + 16 < 16) /\ (t + 16) - 2 = t + 14 /\ (t + 16) - 7 = t + 9 /\
                          (t + 16) - 15 = t + 1 /\ (t + 16) - 16 = t`] THEN
  CONV_TAC WORD_RULE);;

(* The feed-forward of one word. *)
let SHA512_BLOCK_EL = prove
 (`!w hh j. j < 8
            ==> EL j (sha512_block w hh) =
                word_add (EL j (sha512_compress_rounds w hh 80)) (EL j hh)`,
  REWRITE_TAC[sha512_block] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  GEN_TAC THEN GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* The rewrites, for the block w from the state hh: each state word to the
   earliest round's a or e it is, which keeps every term in that form; each
   round's e and its sum toward a, and each schedule word, to the spec's;
   and the feed-forward to the next state's words. *)
let sha512_shift_rules =
  let gen = SPECL [`w:int64 list`; `hh:int64 list`] SHA512_ROUND_SHIFT in
  flat (map (fun t -> CONJUNCTS(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
                                  (SPEC (mk_small_numeral t) gen))) (0--79));;

let sha512_round_folds =
  let gen = SPECL [`w:int64 list`; `hh:int64 list`] SHA512_NEON_ROUND in
  flat (map (fun t ->
    CONJUNCTS(REWRITE_RULE sha512_shift_rules
      (CONV_RULE(TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV NUM_ADD_CONV)
         (SPEC (mk_small_numeral t) gen)))) (0--79));;

let sha512_schedule_folds =
  map (fun t -> CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
                  (SPECL [`w:int64 list`; mk_small_numeral t] SHA512_NEON_SCHEDULE)) (0--63);;

let sha512_schedule_first =
  map (fun t ->
    CONV_RULE(RAND_CONV(RATOR_CONV(LAND_CONV NUM_LT_CONV) THENC REWRITE_CONV[]))
      (REWR_CONV sha512_msg_schedule
        (mk_comb(`sha512_msg_schedule w`, mk_small_numeral t))))
  (0--15);;

let sha512_feed_forward =
  map (fun j -> GSYM(REWRITE_RULE sha512_shift_rules
                  (CONV_RULE(LAND_CONV NUM_LT_CONV THENC REWRITE_CONV[])
                    (SPECL [`w:int64 list`; `hh:int64 list`; mk_small_numeral j] SHA512_BLOCK_EL))))
      (0--7);;

(* ------------------------------------------------------------------------- *)
(* Stepping, with each Q register kept as a join of the spec's words.        *)
(* ------------------------------------------------------------------------- *)

(* Bitwise operations on a Q register act on its two lanes. *)
let SHA512_JOIN_BITWISE = prove
 (`(!(a:int64) (b:int64) (c:int64) (d:int64).
      word_xor (word_join a b:int128) (word_join c d) =
      word_join (word_xor a c) (word_xor b d)) /\
   (!(a:int64) (b:int64) (c:int64) (d:int64).
      word_and (word_join a b:int128) (word_join c d) =
      word_join (word_and a c) (word_and b d)) /\
   (!(a:int64) (b:int64) (c:int64) (d:int64).
      word_or (word_join a b:int128) (word_join c d) =
      word_join (word_or a c) (word_or b d)) /\
   (!(a:int64) (b:int64). word_not (word_join a b:int128) = word_join (word_not a) (word_not b))`,
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* The rewrites that keep each Q register a join of the spec's words. *)
let SHA512_NEON_RULES =
  SHA512_ROR_SLI @ CONJUNCTS SHA512_NEON_FUNCTIONS @ sha512_shift_rules @
  sha512_round_folds @ sha512_schedule_folds @ sha512_feed_forward @
  CONJUNCTS SHA512_JOIN_BITWISE @
  [WORD_OR_REFL; SHA512_REV_BYTEREVERSE; SHA512_CHOOSE_MAJ];;

let SHA512_NEON_VALUE_CONV =
  TOP_DEPTH_CONV (WORD_SIMPLE_SUBWORD_CONV ORELSEC GEN_REWRITE_CONV I SHA512_NEON_RULES);;

(* Stepping normalizes only the Q registers' values: memory and the core
   registers hold addresses and the words as loaded. *)
let sha512_is_q_fact th =
  try (match lhs(concl th) with
         Comb(Comb(Const("read",_),Const(n,_)),_) ->
           String.length n >= 2 && String.sub n 0 1 = "Q"
       | _ -> false)
  with Failure _ -> false;;

let SHA512_NEON_NORM_TAC =
  RULE_ASSUM_TAC(fun th -> if sha512_is_q_fact th then
    CONV_RULE(RAND_CONV SHA512_NEON_VALUE_CONV) th else th);;

let SHA512_NEON_STEPS_TAC execth ns =
  MAP_EVERY (fun n -> AARCH32_STEPS_TAC execth [n] THEN SHA512_NEON_NORM_TAC) ns;;

(* ------------------------------------------------------------------------- *)
(* The message in memory.                                                    *)
(* ------------------------------------------------------------------------- *)

(* The message as one region of memory, which stepping keeps. *)
let sha512_neon_input = new_definition
 `sha512_neon_input (D:num) (n:num) (m:num->int64 list) <=>
    !i j. i < n /\ j < 16
          ==> word(D DIV 2 EXP (64 * (16 * i + j))):int64 =
              word_bytereverse (EL j (m i))`;;

(* A doubleword inside the region is its digits from there on. *)
let SHA512_NEON_DATA_WORD = prove
 (`!(s:aarch32state) (data:int32) K D k.
     read (memory :> bytes(data,K)) s = D /\ k + 8 <= K
     ==> read (memory :> bytes64 (word_add data (word k))) s =
         word(D DIV 2 EXP (8 * k))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytes64; asword; through; read] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 = 8 * 8`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(* base + k, as stepping writes addresses: base itself for 0. *)
let sha512_at base k =
  if k = 0 then base else
  mk_comb(mk_comb(`word_add:int32->int32->int32`, base),
          mk_comb(`word:num->int32`, mk_small_numeral k));;

(* Block i's sixteen doublewords, as VLD1.64 reads them. *)
let SHA512_NEON_BLOCK_DATA =
  let base = `word_add data (word (128 * i)):int32` in
  let fact j =
    mk_eq(vsubst [sha512_at base (8 * j),`a:int32`]
                 `read (memory :> bytes64 a) (s:aarch32state)`,
          vsubst [mk_small_numeral j,`j:num`]
                 `word_bytereverse (EL j ((m:num->int64 list) i))`) in
  prove
   (mk_imp(`read (memory :> bytes(data,128 * n)) (s:aarch32state) = D /\
            sha512_neon_input D n m /\ i < n`,
           list_mk_conj(map fact (0--15))),
    REWRITE_TAC[sha512_neon_input] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!j. j < 16 ==> read (memory :> bytes64 (word_add data (word (128 * i + 8 * j)))) s =
                     word_bytereverse (EL j ((m:num->int64 list) i))`
     (fun th -> MP_TAC(end_itlist CONJ
        (map (fun j -> REWRITE_RULE[ADD_CLAUSES] (CONV_RULE NUM_REDUCE_CONV
                         (SPEC (mk_small_numeral j) th))) (0--15)))) THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(SPECL [`s:aarch32state`; `data:int32`; `128 * n`; `D:num`;
                    `128 * i + 8 * j`] SHA512_NEON_DATA_WORD) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `8 * (128 * i + 8 * j) = 64 * (16 * i + j)`];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One block.                                                                *)
(* ------------------------------------------------------------------------- *)

(* The state's words in memory, and in Q8-Q11 two at a time, as text for
   the goals below. *)
let sha512_state_facts_s st h =
  String.concat " /\\ " (map (fun k ->
    let a = if k = 0 then st else
      Printf.sprintf "word_add %s (word %d)" st (8 * k) in
    Printf.sprintf "read (memory :> bytes64 (%s)) s = EL %d (%s)" a k h) (0--7));;

let sha512_q_facts_s h =
  String.concat " /\\ " (map (fun k ->
    Printf.sprintf "read Q%d s = word_join (EL %d (%s)) (EL %d (%s))"
      (8 + k) (2 * k + 1) h (2 * k) h) (0--3));;

(* TEQ's flag at the block's end: whether block i was the last. *)
let SHA512_NEON_ZF = prove
 (`!data i n.
     i < n /\ 128 * n < 2 EXP 32
     ==> (val (word_xor (word_add (word_add data (word (128 * i))) (word 128))
                        (word_add data (word (128 * n))):int32) = 0 <=>
          i + 1 = n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN
  REWRITE_TAC[MESON[WORD_RULE `word_sub (word_add (d:int32) a) d = a`]
               `word_add (d:int32) a = word_add d b <=> a = b`] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_32; CONG] THEN
  SUBGOAL_THEN `128 * i + 128 < 2 EXP 32` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

(* The state is the rounds' start. *)
let SHA512_HH_ROUNDS0 = prove
 (`!w hh k. EL k hh = EL k (sha512_compress_rounds w hh 0)`,
  REWRITE_TAC[sha512_compress_rounds]);;

(* One block, from the loop's head to its branch: the state, in memory and in
   Q8-Q11, compresses block i. *)
let SHA512_NEON_BLOCK_GOAL =
  let h0 = "sha512_hash_blocks m hh i" and h1 = "sha512_hash_blocks m hh (i + 1)" in
  parse_term (Printf.sprintf
 "!pc state data n D m hh i.
   i < n /\\ 128 * n < 2 EXP 32 /\\ aligned 8 (word pc:int32) /\\
   aarch32_nowrap (word pc:int32) 0x186c /\\ aarch32_nowrap data (128 * n) /\\
   aarch32_nowrap state 64 /\\ aligned 4 state /\\
   nonoverlapping (word pc,0x186c) (state,64) /\\
   nonoverlapping (data,128 * n) (state,64) /\\
   sha512_neon_input D n m
   ==> ensures aarch32
    (\\s. aligned_bytes_loaded s (word pc) sha512_armv4_mc /\\
         read PC s = word (pc + 0x754) /\\
         read R0 s = state /\\ read R1 s = word_add data (word (128 * i)) /\\
         read R2 s = word_add data (word (128 * n)) /\\ read R3 s = word pc /\\
         read (memory :> bytes(data,128 * n)) s = D /\\ %s /\\ %s)
    (\\s. aligned_bytes_loaded s (word pc) sha512_armv4_mc /\\
         read PC s = word (pc + 0x1860) /\\
         (read R0 s = state /\\ read R1 s = word_add data (word (128 * (i + 1))) /\\
          read R2 s = word_add data (word (128 * n)) /\\ read R3 s = word pc /\\
          read (memory :> bytes(data,128 * n)) s = D /\\ %s /\\ %s) /\\
         (read ZF s <=> i + 1 = n))
    (MAYCHANGE [PC; R1; R3; R12] ,,
     MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(state,64)] ,,
     MAYCHANGE [events])"
  (sha512_state_facts_s "state" h0) (sha512_q_facts_s h0)
  (sha512_state_facts_s "state" h1) (sha512_q_facts_s h1));;

(* Names the other Q registers' values, since a write to half of a register
   with none drops it; reads block i's words, as the schedule's first, and
   K512; and states Q8-Q11 as the rounds' start. *)
let SHA512_NEON_BLOCK_SETUP_TAC =
  REWRITE_TAC[SOME_FLAGS; fst SHA512_ARMV4_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[CONJUNCT2 sha512_hash_blocks] THEN
  SUBGOAL_THEN `aarch32_nowrap (word_add data (word (128 * i)):int32) 128`
  ASSUME_TAC THENL
   [MATCH_MP_TAC AARCH32_NOWRAP_OFFSET THEN EXISTS_TAC `128 * n` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add data (word (128 * (i + 1))):int32 =
                word_add (word_add data (word (128 * i))) (word 128)`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  MAP_EVERY (fun (v,c) -> GHOST_INTRO_TAC v c)
   [`q0:int128`,`read Q0`; `q1:int128`,`read Q1`; `q2:int128`,`read Q2`;
    `q3:int128`,`read Q3`; `q4:int128`,`read Q4`; `q5:int128`,`read Q5`;
    `q6:int128`,`read Q6`; `q7:int128`,`read Q7`; `q12:int128`,`read Q12`;
    `q13:int128`,`read Q13`; `q14:int128`,`read Q14`; `q15:int128`,`read Q15`] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(INST [`s0:aarch32state`,`s:aarch32state`] SHA512_NEON_BLOCK_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `blk = word_add data (word (128 * i)):int32` THEN
  ABBREV_TAC `h = sha512_hash_blocks m hh i` THEN
  ABBREV_TAC `w = (m:num->int64 list) i` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE(map GSYM sha512_schedule_first)) THEN
  MP_TAC(INST [`s0:aarch32state`,`s:aarch32state`] SHA512_K_LOADS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th -> if sha512_is_q_fact th then
    ONCE_REWRITE_RULE[SPEC `w:int64 list` SHA512_HH_ROUNDS0] th else th);;


(* The block's 2,897 instructions, the last 64 rounds' four passes of their
   loop unrolled. *)
let SHA512_NEON_BLOCK = prove
 (SHA512_NEON_BLOCK_GOAL,
  SHA512_NEON_BLOCK_SETUP_TAC THEN
  SHA512_NEON_STEPS_TAC SHA512_ARMV4_EXEC (1--2897) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[] THEN
  EXPAND_TAC "blk" THEN ASM_SIMP_TAC[SHA512_NEON_ZF]);;

(* ------------------------------------------------------------------------- *)
(* The blocks, and the routine.                                              *)
(* ------------------------------------------------------------------------- *)

(* From the state's load to the loop's exit, over the message as one region,
   which stepping keeps. *)
let sha512_init_list = "[h0; h1; h2; h3; h4; h5; h6; h7]";;

let sha512_plain_state_facts =
  "read (memory :> bytes64 state) s = h0 /\\ " ^
  String.concat " /\\ " (map (fun k ->
    Printf.sprintf "read (memory :> bytes64 (word_add state (word %d))) s = h%d" (8 * k) k) (1--7));;

let SHA512_NEON_CORE_GOAL =
  let hn = "sha512_hash_blocks m " ^ sha512_init_list ^ " n" in
  parse_term (Printf.sprintf
 "!state data n D m h0 h1 h2 h3 h4 h5 h6 h7 pc.
   0 < n /\\ 128 * n < 2 EXP 32 /\\ aligned 8 (word pc:int32) /\\
   aarch32_nowrap (word pc:int32) 0x186c /\\ aarch32_nowrap data (128 * n) /\\
   aarch32_nowrap state 64 /\\ aligned 4 state /\\
   nonoverlapping (word pc,0x186c) (state,64) /\\
   nonoverlapping (data,128 * n) (state,64) /\\
   sha512_neon_input D n m
   ==> ensures aarch32
    (\\s. aligned_bytes_loaded s (word pc) sha512_armv4_mc /\\
         read PC s = word (pc + 0x750) /\\
         read R0 s = state /\\ read R1 s = data /\\
         read R2 s = word_add data (word (128 * n)) /\\ read R3 s = word pc /\\
         read (memory :> bytes(data,128 * n)) s = D /\\ %s)
    (\\s. read PC s = word (pc + 0x1864) /\\ %s)
    (MAYCHANGE [PC; R1; R3; R12] ,,
     MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
     MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(state,64)] ,,
     MAYCHANGE [events])"
  sha512_plain_state_facts (sha512_state_facts_s "state" hn));;

(* At the loop's head after i blocks, and at its branch with the flag. *)
let SHA512_NEON_INV =
  let hi = "sha512_hash_blocks m " ^ sha512_init_list ^ " i" in
  parse_term (Printf.sprintf
 "\\i s. (read R0 s = state /\\ read R1 s = word_add data (word (128 * i)) /\\
         read R2 s = word_add data (word (128 * n)) /\\ read R3 s = word pc /\\
         read (memory :> bytes(data,128 * n)) s = D /\\ %s /\\ %s) /\\
        (read ZF s <=> i = n)"
  (sha512_state_facts_s "state" hi) (sha512_q_facts_s hi));;

let SHA512_NEON_CORE_TAC block_th =
  REWRITE_TAC[SOME_FLAGS; fst SHA512_ARMV4_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_WHILE_PUP_TAC `n:num` `pc + 0x754` `pc + 0x1860` SHA512_NEON_INV THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* There is a block. *)
    ASM_ARITH_TAC;

    (* Into the loop: the state into Q8-Q11. *)
    ENSURES_INIT_TAC "s0" THEN
    AARCH32_STEPS_TAC SHA512_ARMV4_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 sha512_hash_blocks] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[];

    (* A block. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] block_th) THEN
    ASM_REWRITE_TAC[];

    (* Back to the head while blocks remain. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `read ZF (s0:aarch32state) <=> (i:num) = n` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    AARCH32_STEPS_TAC SHA512_ARMV4_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (* Out of the loop. *)
    ENSURES_INIT_TAC "s0" THEN
    AARCH32_STEPS_TAC SHA512_ARMV4_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let SHA512_NEON_CORE = prove
 (SHA512_NEON_CORE_GOAL, SHA512_NEON_CORE_TAC SHA512_NEON_BLOCK);;

(* The prologue's end of the message, data + (n << 7). *)
let SHA512_NEON_SHL7 = prove
 (`!n. word_shl (word n:int32) 7 = word (128 * n)`,
  GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; DIMINDEX_32; WORD_EQ; CONG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM]);;

(* From the routine's entry to its return, over the message as one region:
   the prologue saves d8-d15, which the AAPCS keeps, below the stack
   pointer, and the epilogue restores them. *)
let SHA512_NEON_SUBROUTINE_D_GOAL =
  let hn = "sha512_hash_blocks m " ^ sha512_init_list ^ " n" in
  parse_term (Printf.sprintf
 "!state data n D m h0 h1 h2 h3 h4 h5 h6 h7 pc stackpointer returnaddress.
   0 < n /\\ 128 * n < 2 EXP 32 /\\ aligned 8 (word pc:int32) /\\
   aarch32_nowrap (word pc:int32) 0x186c /\\ aarch32_nowrap data (128 * n) /\\
   aarch32_nowrap state 64 /\\ aligned 4 state /\\
   nonoverlapping (word pc,0x186c) (state,64) /\\
   nonoverlapping (data,128 * n) (state,64) /\\
   sha512_neon_input D n m /\\
   aarch32_bx_target returnaddress /\\ aligned 4 stackpointer /\\
   aarch32_nowrap (word_sub stackpointer (word 64)) 64 /\\
   nonoverlapping (word_sub stackpointer (word 64),64) (word pc,0x186c) /\\
   nonoverlapping (word_sub stackpointer (word 64),64) (state,64) /\\
   nonoverlapping (word_sub stackpointer (word 64),64) (data,128 * n)
   ==> ensures aarch32
    (\\s. aligned_bytes_loaded s (word pc) sha512_armv4_mc /\\
         read PC s = word (pc + 0x740) /\\
         read SP s = stackpointer /\\ read LR s = returnaddress /\\
         C_ARGUMENTS [state; data; word n] s /\\
         read (memory :> bytes(data,128 * n)) s = D /\\ %s)
    (\\s. read PC s = returnaddress /\\ %s)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(state,64);
                memory :> bytes(word_sub stackpointer (word 64),64)])"
  sha512_plain_state_facts (sha512_state_facts_s "state" hn));;

let SHA512_NEON_SUBROUTINE_D = prove
 (SHA512_NEON_SUBROUTINE_D_GOAL,
  REWRITE_TAC[fst SHA512_ARMV4_EXEC] THEN
  AARCH32_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(4,2)
    ~qreglist:`[Q4; Q5; Q6; Q7]`
    ~core_precondition_tac:(REWRITE_TAC[SHA512_NEON_SHL7])
    SHA512_ARMV4_EXEC
    (REWRITE_RULE[fst SHA512_ARMV4_EXEC] SHA512_NEON_CORE)
    `[]:((aarch32state,int32)component)list` 64);;

(* The routine, over its blocks' words as memory holds them. *)
let SHA512_BLOCK_DATA_ORDER_NEON_GOAL =
  let hn = "sha512_hash_blocks m " ^ sha512_init_list ^ " n" in
  parse_term (Printf.sprintf
 "!state data n h0 h1 h2 h3 h4 h5 h6 h7 m pc stackpointer returnaddress.
   0 < n /\\ 128 * n < 2 EXP 32 /\\ aligned 8 (word pc:int32) /\\
   aarch32_nowrap (word pc:int32) 0x186c /\\ aarch32_nowrap data (128 * n) /\\
   aarch32_nowrap state 64 /\\ aligned 4 state /\\
   nonoverlapping (word pc,0x186c) (state,64) /\\
   nonoverlapping (data,128 * n) (state,64) /\\
   aarch32_bx_target returnaddress /\\ aligned 4 stackpointer /\\
   aarch32_nowrap (word_sub stackpointer (word 64)) 64 /\\
   nonoverlapping (word_sub stackpointer (word 64),64) (word pc,0x186c) /\\
   nonoverlapping (word_sub stackpointer (word 64),64) (state,64) /\\
   nonoverlapping (word_sub stackpointer (word 64),64) (data,128 * n)
   ==> ensures aarch32
    (\\s. aligned_bytes_loaded s (word pc) sha512_armv4_mc /\\
         read PC s = word (pc + 0x740) /\\
         read SP s = stackpointer /\\ read LR s = returnaddress /\\
         C_ARGUMENTS [state; data; word n] s /\\ %s /\\
         (!i j. i < n /\\ j < 16
                ==> read (memory :> bytes64
                           (word_add data (word (128 * i + 8 * j)))) s =
                    word_bytereverse (EL j (m i))))
    (\\s. read PC s = returnaddress /\\
         let h' = %s in %s)
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(state,64);
                memory :> bytes(word_sub stackpointer (word 64),64)])"
  sha512_plain_state_facts hn (sha512_state_facts_s "state" "h'"));;

(* The region's words are the blocks' byte-swapped message words. *)
let SHA512_NEON_INPUT = prove
 (`!(s:aarch32state) data n m.
     (!i j. i < n /\ j < 16
            ==> read (memory :> bytes64 (word_add data (word (128 * i + 8 * j)))) s =
                word_bytereverse (EL j (m i)))
     ==> sha512_neon_input (read (memory :> bytes(data,128 * n)) s) n m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sha512_neon_input] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`s:aarch32state`; `data:int32`; `128 * n`;
                `read (memory :> bytes(data,128 * n)) s`; `128 * i + 8 * j`]
               SHA512_NEON_DATA_WORD) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * (128 * i + 8 * j) = 64 * (16 * i + j)`]);;

(* The routine's theorem from the region's, with the region's value at entry. *)
let SHA512_NEON_FROM_REGION_TAC dth =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ensures] THEN X_GEN_TAC `s:aarch32state` THEN STRIP_TAC THEN
  MP_TAC(SPEC `read (memory :> bytes(data,128 * n)) (s:aarch32state)`
           (ISPECL [`state:int32`; `data:int32`; `n:num`] dth)) THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num->int64 list`; `h0:int64`; `h1:int64`; `h2:int64`;
                             `h3:int64`; `h4:int64`; `h5:int64`; `h6:int64`; `h7:int64`;
                             `pc:num`; `stackpointer:int32`; `returnaddress:int32`]) THEN
  ASM_SIMP_TAC[SHA512_NEON_INPUT] THEN
  REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:aarch32state`) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];;

let SHA512_BLOCK_DATA_ORDER_NEON_SUBROUTINE_CORRECT = prove
 (SHA512_BLOCK_DATA_ORDER_NEON_GOAL,
  SHA512_NEON_FROM_REGION_TAC SHA512_NEON_SUBROUTINE_D);;
