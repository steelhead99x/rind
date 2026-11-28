(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* aws-lc's sha256-armv4, as rind's build emits it.                          *)
(* ========================================================================= *)

(* The A32 code rind's low::arm::sha_armv4 assembles from aws-lc's
   sha256-armv4: the table K256, its terminator, and the routines
   sha256_block_data_order_nohw, sha256_block_data_order_neon, and
   sha256_block_data_order_hw, which reach K256 through the address the
   code gives it, an ADR or a literal word before the routine. So the code
   these theorems are about is the whole of it, from K256 at pc. Each
   theorem holds for a caller in A32 or T32, so it covers every armv7
   target.

   SHA256_BLOCK_DATA_ORDER_HW_SUBROUTINE_CORRECT: the crypto extension's
   routine, which rind runs where the CPU has it, stores to the state
   s2n-bignum's FIPS 180-4 spec, sha256_hash_blocks, of its blocks from the
   state, for one block or more, as rind calls it. *)

needs "aarch32/proofs/base.ml";;
needs "x86/proofs/utils/sha256_spec.ml";;

(* admin/prove writes the code's bytes, from K256 through the end of
   sha256_block_data_order_hw, as rind's release build for
   armv7-unknown-linux-gnueabihf emits them, to armv7/sha256_armv4.bin, and
   the definition fails unless they are these: K256 and its terminator at
   0, sha256_block_data_order_nohw at 0x104, sha256_block_data_order_neon at
   0xf10, and sha256_block_data_order_hw at 0x1b20, after the literal it
   loads K256's offset from. The source spells the crypto extension's
   instructions as .byte, which this names as they disassemble. *)
let sha256_armv4_mc = define_assert_word_list "sha256_armv4_mc"
  (term_of_bytes (load_file "armv7/sha256_armv4.bin"))
[
  0x428a2f98; (* data *)
  0x71374491; (* data *)
  0xb5c0fbcf; (* data *)
  0xe9b5dba5; (* data *)
  0x3956c25b; (* data *)
  0x59f111f1; (* data *)
  0x923f82a4; (* data *)
  0xab1c5ed5; (* data *)
  0xd807aa98; (* data *)
  0x12835b01; (* data *)
  0x243185be; (* data *)
  0x550c7dc3; (* data *)
  0x72be5d74; (* data *)
  0x80deb1fe; (* data *)
  0x9bdc06a7; (* data *)
  0xc19bf174; (* data *)
  0xe49b69c1; (* data *)
  0xefbe4786; (* data *)
  0x0fc19dc6; (* data *)
  0x240ca1cc; (* data *)
  0x2de92c6f; (* data *)
  0x4a7484aa; (* data *)
  0x5cb0a9dc; (* data *)
  0x76f988da; (* data *)
  0x983e5152; (* data *)
  0xa831c66d; (* data *)
  0xb00327c8; (* data *)
  0xbf597fc7; (* data *)
  0xc6e00bf3; (* data *)
  0xd5a79147; (* data *)
  0x06ca6351; (* data *)
  0x14292967; (* data *)
  0x27b70a85; (* data *)
  0x2e1b2138; (* data *)
  0x4d2c6dfc; (* data *)
  0x53380d13; (* data *)
  0x650a7354; (* data *)
  0x766a0abb; (* data *)
  0x81c2c92e; (* data *)
  0x92722c85; (* data *)
  0xa2bfe8a1; (* data *)
  0xa81a664b; (* data *)
  0xc24b8b70; (* data *)
  0xc76c51a3; (* data *)
  0xd192e819; (* data *)
  0xd6990624; (* data *)
  0xf40e3585; (* data *)
  0x106aa070; (* data *)
  0x19a4c116; (* data *)
  0x1e376c08; (* data *)
  0x2748774c; (* data *)
  0x34b0bcb5; (* data *)
  0x391c0cb3; (* data *)
  0x4ed8aa4a; (* data *)
  0x5b9cca4f; (* data *)
  0x682e6ff3; (* data *)
  0x748f82ee; (* data *)
  0x78a5636f; (* data *)
  0x84c87814; (* data *)
  0x8cc70208; (* data *)
  0x90befffa; (* data *)
  0xa4506ceb; (* data *)
  0xbef9a3f7; (* data *)
  0xc67178f2; (* data *)
  0x00000000; (* data *)
  0xe0812302; (* add r2, r1, r2, lsl #6 *)
  0xe92d4ff7; (* push {r0, r1, r2, r4, r5, r6, r7, r8, r9, r10, r11, lr} *)
  0xe8900ff0; (* ldm r0, {r4, r5, r6, r7, r8, r9, r10, r11} *)
  0xe24fef46; (* sub lr, pc, #280 *)
  0xe24dd040; (* sub sp, sp, #64 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe0253006; (* eor r3, r5, r6 *)
  0xe02cc00c; (* eor r12, r12, r12 *)
  0xe02802e8; (* eor r0, r8, r8, ror #5 *)
  0xe084400c; (* add r4, r4, r12 *)
  0xe02009e8; (* eor r0, r0, r8, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe58d2000; (* str r2, [sp] *)
  0xe029200a; (* eor r2, r9, r10 *)
  0xe08bb360; (* add r11, r11, r0, ror #6 *)
  0xe0022008; (* and r2, r2, r8 *)
  0xe08bb00c; (* add r11, r11, r12 *)
  0xe022200a; (* eor r2, r2, r10 *)
  0xe02405e4; (* eor r0, r4, r4, ror #11 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe024c005; (* eor r12, r4, r5 *)
  0xe0200a64; (* eor r0, r0, r4, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe087700b; (* add r7, r7, r11 *)
  0xe0233005; (* eor r3, r3, r5 *)
  0xe08bb160; (* add r11, r11, r0, ror #2 *)
  0xe02702e7; (* eor r0, r7, r7, ror #5 *)
  0xe08bb003; (* add r11, r11, r3 *)
  0xe02009e7; (* eor r0, r0, r7, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe58d2004; (* str r2, [sp, #0x4] *)
  0xe0282009; (* eor r2, r8, r9 *)
  0xe08aa360; (* add r10, r10, r0, ror #6 *)
  0xe0022007; (* and r2, r2, r7 *)
  0xe08aa003; (* add r10, r10, r3 *)
  0xe0222009; (* eor r2, r2, r9 *)
  0xe02b05eb; (* eor r0, r11, r11, ror #11 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe02b3004; (* eor r3, r11, r4 *)
  0xe0200a6b; (* eor r0, r0, r11, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe086600a; (* add r6, r6, r10 *)
  0xe02cc004; (* eor r12, r12, r4 *)
  0xe08aa160; (* add r10, r10, r0, ror #2 *)
  0xe02602e6; (* eor r0, r6, r6, ror #5 *)
  0xe08aa00c; (* add r10, r10, r12 *)
  0xe02009e6; (* eor r0, r0, r6, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe58d2008; (* str r2, [sp, #0x8] *)
  0xe0272008; (* eor r2, r7, r8 *)
  0xe0899360; (* add r9, r9, r0, ror #6 *)
  0xe0022006; (* and r2, r2, r6 *)
  0xe089900c; (* add r9, r9, r12 *)
  0xe0222008; (* eor r2, r2, r8 *)
  0xe02a05ea; (* eor r0, r10, r10, ror #11 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe02ac00b; (* eor r12, r10, r11 *)
  0xe0200a6a; (* eor r0, r0, r10, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0855009; (* add r5, r5, r9 *)
  0xe023300b; (* eor r3, r3, r11 *)
  0xe0899160; (* add r9, r9, r0, ror #2 *)
  0xe02502e5; (* eor r0, r5, r5, ror #5 *)
  0xe0899003; (* add r9, r9, r3 *)
  0xe02009e5; (* eor r0, r0, r5, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe58d200c; (* str r2, [sp, #0xc] *)
  0xe0262007; (* eor r2, r6, r7 *)
  0xe0888360; (* add r8, r8, r0, ror #6 *)
  0xe0022005; (* and r2, r2, r5 *)
  0xe0888003; (* add r8, r8, r3 *)
  0xe0222007; (* eor r2, r2, r7 *)
  0xe02905e9; (* eor r0, r9, r9, ror #11 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe029300a; (* eor r3, r9, r10 *)
  0xe0200a69; (* eor r0, r0, r9, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0844008; (* add r4, r4, r8 *)
  0xe02cc00a; (* eor r12, r12, r10 *)
  0xe0888160; (* add r8, r8, r0, ror #2 *)
  0xe02402e4; (* eor r0, r4, r4, ror #5 *)
  0xe088800c; (* add r8, r8, r12 *)
  0xe02009e4; (* eor r0, r0, r4, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe58d2010; (* str r2, [sp, #0x10] *)
  0xe0252006; (* eor r2, r5, r6 *)
  0xe0877360; (* add r7, r7, r0, ror #6 *)
  0xe0022004; (* and r2, r2, r4 *)
  0xe087700c; (* add r7, r7, r12 *)
  0xe0222006; (* eor r2, r2, r6 *)
  0xe02805e8; (* eor r0, r8, r8, ror #11 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe028c009; (* eor r12, r8, r9 *)
  0xe0200a68; (* eor r0, r0, r8, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe08bb007; (* add r11, r11, r7 *)
  0xe0233009; (* eor r3, r3, r9 *)
  0xe0877160; (* add r7, r7, r0, ror #2 *)
  0xe02b02eb; (* eor r0, r11, r11, ror #5 *)
  0xe0877003; (* add r7, r7, r3 *)
  0xe02009eb; (* eor r0, r0, r11, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe58d2014; (* str r2, [sp, #0x14] *)
  0xe0242005; (* eor r2, r4, r5 *)
  0xe0866360; (* add r6, r6, r0, ror #6 *)
  0xe002200b; (* and r2, r2, r11 *)
  0xe0866003; (* add r6, r6, r3 *)
  0xe0222005; (* eor r2, r2, r5 *)
  0xe02705e7; (* eor r0, r7, r7, ror #11 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe0273008; (* eor r3, r7, r8 *)
  0xe0200a67; (* eor r0, r0, r7, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe08aa006; (* add r10, r10, r6 *)
  0xe02cc008; (* eor r12, r12, r8 *)
  0xe0866160; (* add r6, r6, r0, ror #2 *)
  0xe02a02ea; (* eor r0, r10, r10, ror #5 *)
  0xe086600c; (* add r6, r6, r12 *)
  0xe02009ea; (* eor r0, r0, r10, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe58d2018; (* str r2, [sp, #0x18] *)
  0xe02b2004; (* eor r2, r11, r4 *)
  0xe0855360; (* add r5, r5, r0, ror #6 *)
  0xe002200a; (* and r2, r2, r10 *)
  0xe085500c; (* add r5, r5, r12 *)
  0xe0222004; (* eor r2, r2, r4 *)
  0xe02605e6; (* eor r0, r6, r6, ror #11 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe026c007; (* eor r12, r6, r7 *)
  0xe0200a66; (* eor r0, r0, r6, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0899005; (* add r9, r9, r5 *)
  0xe0233007; (* eor r3, r3, r7 *)
  0xe0855160; (* add r5, r5, r0, ror #2 *)
  0xe02902e9; (* eor r0, r9, r9, ror #5 *)
  0xe0855003; (* add r5, r5, r3 *)
  0xe02009e9; (* eor r0, r0, r9, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe58d201c; (* str r2, [sp, #0x1c] *)
  0xe02a200b; (* eor r2, r10, r11 *)
  0xe0844360; (* add r4, r4, r0, ror #6 *)
  0xe0022009; (* and r2, r2, r9 *)
  0xe0844003; (* add r4, r4, r3 *)
  0xe022200b; (* eor r2, r2, r11 *)
  0xe02505e5; (* eor r0, r5, r5, ror #11 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe0253006; (* eor r3, r5, r6 *)
  0xe0200a65; (* eor r0, r0, r5, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0888004; (* add r8, r8, r4 *)
  0xe02cc006; (* eor r12, r12, r6 *)
  0xe0844160; (* add r4, r4, r0, ror #2 *)
  0xe02802e8; (* eor r0, r8, r8, ror #5 *)
  0xe084400c; (* add r4, r4, r12 *)
  0xe02009e8; (* eor r0, r0, r8, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe58d2020; (* str r2, [sp, #0x20] *)
  0xe029200a; (* eor r2, r9, r10 *)
  0xe08bb360; (* add r11, r11, r0, ror #6 *)
  0xe0022008; (* and r2, r2, r8 *)
  0xe08bb00c; (* add r11, r11, r12 *)
  0xe022200a; (* eor r2, r2, r10 *)
  0xe02405e4; (* eor r0, r4, r4, ror #11 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe024c005; (* eor r12, r4, r5 *)
  0xe0200a64; (* eor r0, r0, r4, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe087700b; (* add r7, r7, r11 *)
  0xe0233005; (* eor r3, r3, r5 *)
  0xe08bb160; (* add r11, r11, r0, ror #2 *)
  0xe02702e7; (* eor r0, r7, r7, ror #5 *)
  0xe08bb003; (* add r11, r11, r3 *)
  0xe02009e7; (* eor r0, r0, r7, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe58d2024; (* str r2, [sp, #0x24] *)
  0xe0282009; (* eor r2, r8, r9 *)
  0xe08aa360; (* add r10, r10, r0, ror #6 *)
  0xe0022007; (* and r2, r2, r7 *)
  0xe08aa003; (* add r10, r10, r3 *)
  0xe0222009; (* eor r2, r2, r9 *)
  0xe02b05eb; (* eor r0, r11, r11, ror #11 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe02b3004; (* eor r3, r11, r4 *)
  0xe0200a6b; (* eor r0, r0, r11, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe086600a; (* add r6, r6, r10 *)
  0xe02cc004; (* eor r12, r12, r4 *)
  0xe08aa160; (* add r10, r10, r0, ror #2 *)
  0xe02602e6; (* eor r0, r6, r6, ror #5 *)
  0xe08aa00c; (* add r10, r10, r12 *)
  0xe02009e6; (* eor r0, r0, r6, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe58d2028; (* str r2, [sp, #0x28] *)
  0xe0272008; (* eor r2, r7, r8 *)
  0xe0899360; (* add r9, r9, r0, ror #6 *)
  0xe0022006; (* and r2, r2, r6 *)
  0xe089900c; (* add r9, r9, r12 *)
  0xe0222008; (* eor r2, r2, r8 *)
  0xe02a05ea; (* eor r0, r10, r10, ror #11 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe02ac00b; (* eor r12, r10, r11 *)
  0xe0200a6a; (* eor r0, r0, r10, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0855009; (* add r5, r5, r9 *)
  0xe023300b; (* eor r3, r3, r11 *)
  0xe0899160; (* add r9, r9, r0, ror #2 *)
  0xe02502e5; (* eor r0, r5, r5, ror #5 *)
  0xe0899003; (* add r9, r9, r3 *)
  0xe02009e5; (* eor r0, r0, r5, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe58d202c; (* str r2, [sp, #0x2c] *)
  0xe0262007; (* eor r2, r6, r7 *)
  0xe0888360; (* add r8, r8, r0, ror #6 *)
  0xe0022005; (* and r2, r2, r5 *)
  0xe0888003; (* add r8, r8, r3 *)
  0xe0222007; (* eor r2, r2, r7 *)
  0xe02905e9; (* eor r0, r9, r9, ror #11 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe029300a; (* eor r3, r9, r10 *)
  0xe0200a69; (* eor r0, r0, r9, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0844008; (* add r4, r4, r8 *)
  0xe02cc00a; (* eor r12, r12, r10 *)
  0xe0888160; (* add r8, r8, r0, ror #2 *)
  0xe02402e4; (* eor r0, r4, r4, ror #5 *)
  0xe088800c; (* add r8, r8, r12 *)
  0xe02009e4; (* eor r0, r0, r4, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe58d2030; (* str r2, [sp, #0x30] *)
  0xe0252006; (* eor r2, r5, r6 *)
  0xe0877360; (* add r7, r7, r0, ror #6 *)
  0xe0022004; (* and r2, r2, r4 *)
  0xe087700c; (* add r7, r7, r12 *)
  0xe0222006; (* eor r2, r2, r6 *)
  0xe02805e8; (* eor r0, r8, r8, ror #11 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe028c009; (* eor r12, r8, r9 *)
  0xe0200a68; (* eor r0, r0, r8, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe08bb007; (* add r11, r11, r7 *)
  0xe0233009; (* eor r3, r3, r9 *)
  0xe0877160; (* add r7, r7, r0, ror #2 *)
  0xe02b02eb; (* eor r0, r11, r11, ror #5 *)
  0xe0877003; (* add r7, r7, r3 *)
  0xe02009eb; (* eor r0, r0, r11, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe58d2034; (* str r2, [sp, #0x34] *)
  0xe0242005; (* eor r2, r4, r5 *)
  0xe0866360; (* add r6, r6, r0, ror #6 *)
  0xe002200b; (* and r2, r2, r11 *)
  0xe0866003; (* add r6, r6, r3 *)
  0xe0222005; (* eor r2, r2, r5 *)
  0xe02705e7; (* eor r0, r7, r7, ror #11 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe0273008; (* eor r3, r7, r8 *)
  0xe0200a67; (* eor r0, r0, r7, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe08aa006; (* add r10, r10, r6 *)
  0xe02cc008; (* eor r12, r12, r8 *)
  0xe0866160; (* add r6, r6, r0, ror #2 *)
  0xe02a02ea; (* eor r0, r10, r10, ror #5 *)
  0xe086600c; (* add r6, r6, r12 *)
  0xe02009ea; (* eor r0, r0, r10, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe58d2038; (* str r2, [sp, #0x38] *)
  0xe02b2004; (* eor r2, r11, r4 *)
  0xe0855360; (* add r5, r5, r0, ror #6 *)
  0xe002200a; (* and r2, r2, r10 *)
  0xe085500c; (* add r5, r5, r12 *)
  0xe0222004; (* eor r2, r2, r4 *)
  0xe02605e6; (* eor r0, r6, r6, ror #11 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe4912004; (* ldr r2, [r1], #4 *)
  0xe026c007; (* eor r12, r6, r7 *)
  0xe0200a66; (* eor r0, r0, r6, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0899005; (* add r9, r9, r5 *)
  0xe0233007; (* eor r3, r3, r7 *)
  0xe0855160; (* add r5, r5, r0, ror #2 *)
  0xe58d1044; (* str r1, [sp, #0x44] *)
  0xe02902e9; (* eor r0, r9, r9, ror #5 *)
  0xe0855003; (* add r5, r5, r3 *)
  0xe02009e9; (* eor r0, r0, r9, ror #19 *)
  0xe6bf2f32; (* rev r2, r2 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe58d203c; (* str r2, [sp, #0x3c] *)
  0xe02a200b; (* eor r2, r10, r11 *)
  0xe0844360; (* add r4, r4, r0, ror #6 *)
  0xe0022009; (* and r2, r2, r9 *)
  0xe0844003; (* add r4, r4, r3 *)
  0xe022200b; (* eor r2, r2, r11 *)
  0xe02505e5; (* eor r0, r5, r5, ror #11 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe59d2004; (* ldr r2, [sp, #0x4] *)
  0xe0253006; (* eor r3, r5, r6 *)
  0xe59d1038; (* ldr r1, [sp, #0x38] *)
  0xe0200a65; (* eor r0, r0, r5, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0888004; (* add r8, r8, r4 *)
  0xe02cc006; (* eor r12, r12, r6 *)
  0xe0844160; (* add r4, r4, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe084400c; (* add r4, r4, r12 *)
  0xe1a0c8e1; (* ror r12, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02cc9e1; (* eor r12, r12, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2000; (* ldr r2, [sp] *)
  0xe02cc521; (* eor r12, r12, r1, lsr #10 *)
  0xe59d1024; (* ldr r1, [sp, #0x24] *)
  0xe08cc000; (* add r12, r12, r0 *)
  0xe02802e8; (* eor r0, r8, r8, ror #5 *)
  0xe082200c; (* add r2, r2, r12 *)
  0xe02009e8; (* eor r0, r0, r8, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe58d2000; (* str r2, [sp] *)
  0xe029200a; (* eor r2, r9, r10 *)
  0xe08bb360; (* add r11, r11, r0, ror #6 *)
  0xe0022008; (* and r2, r2, r8 *)
  0xe08bb00c; (* add r11, r11, r12 *)
  0xe022200a; (* eor r2, r2, r10 *)
  0xe02405e4; (* eor r0, r4, r4, ror #11 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe59d2008; (* ldr r2, [sp, #0x8] *)
  0xe024c005; (* eor r12, r4, r5 *)
  0xe59d103c; (* ldr r1, [sp, #0x3c] *)
  0xe0200a64; (* eor r0, r0, r4, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe087700b; (* add r7, r7, r11 *)
  0xe0233005; (* eor r3, r3, r5 *)
  0xe08bb160; (* add r11, r11, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe08bb003; (* add r11, r11, r3 *)
  0xe1a038e1; (* ror r3, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02339e1; (* eor r3, r3, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2004; (* ldr r2, [sp, #0x4] *)
  0xe0233521; (* eor r3, r3, r1, lsr #10 *)
  0xe59d1028; (* ldr r1, [sp, #0x28] *)
  0xe0833000; (* add r3, r3, r0 *)
  0xe02702e7; (* eor r0, r7, r7, ror #5 *)
  0xe0822003; (* add r2, r2, r3 *)
  0xe02009e7; (* eor r0, r0, r7, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe58d2004; (* str r2, [sp, #0x4] *)
  0xe0282009; (* eor r2, r8, r9 *)
  0xe08aa360; (* add r10, r10, r0, ror #6 *)
  0xe0022007; (* and r2, r2, r7 *)
  0xe08aa003; (* add r10, r10, r3 *)
  0xe0222009; (* eor r2, r2, r9 *)
  0xe02b05eb; (* eor r0, r11, r11, ror #11 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe59d200c; (* ldr r2, [sp, #0xc] *)
  0xe02b3004; (* eor r3, r11, r4 *)
  0xe59d1000; (* ldr r1, [sp] *)
  0xe0200a6b; (* eor r0, r0, r11, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe086600a; (* add r6, r6, r10 *)
  0xe02cc004; (* eor r12, r12, r4 *)
  0xe08aa160; (* add r10, r10, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe08aa00c; (* add r10, r10, r12 *)
  0xe1a0c8e1; (* ror r12, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02cc9e1; (* eor r12, r12, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2008; (* ldr r2, [sp, #0x8] *)
  0xe02cc521; (* eor r12, r12, r1, lsr #10 *)
  0xe59d102c; (* ldr r1, [sp, #0x2c] *)
  0xe08cc000; (* add r12, r12, r0 *)
  0xe02602e6; (* eor r0, r6, r6, ror #5 *)
  0xe082200c; (* add r2, r2, r12 *)
  0xe02009e6; (* eor r0, r0, r6, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe58d2008; (* str r2, [sp, #0x8] *)
  0xe0272008; (* eor r2, r7, r8 *)
  0xe0899360; (* add r9, r9, r0, ror #6 *)
  0xe0022006; (* and r2, r2, r6 *)
  0xe089900c; (* add r9, r9, r12 *)
  0xe0222008; (* eor r2, r2, r8 *)
  0xe02a05ea; (* eor r0, r10, r10, ror #11 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe59d2010; (* ldr r2, [sp, #0x10] *)
  0xe02ac00b; (* eor r12, r10, r11 *)
  0xe59d1004; (* ldr r1, [sp, #0x4] *)
  0xe0200a6a; (* eor r0, r0, r10, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0855009; (* add r5, r5, r9 *)
  0xe023300b; (* eor r3, r3, r11 *)
  0xe0899160; (* add r9, r9, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe0899003; (* add r9, r9, r3 *)
  0xe1a038e1; (* ror r3, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02339e1; (* eor r3, r3, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d200c; (* ldr r2, [sp, #0xc] *)
  0xe0233521; (* eor r3, r3, r1, lsr #10 *)
  0xe59d1030; (* ldr r1, [sp, #0x30] *)
  0xe0833000; (* add r3, r3, r0 *)
  0xe02502e5; (* eor r0, r5, r5, ror #5 *)
  0xe0822003; (* add r2, r2, r3 *)
  0xe02009e5; (* eor r0, r0, r5, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe58d200c; (* str r2, [sp, #0xc] *)
  0xe0262007; (* eor r2, r6, r7 *)
  0xe0888360; (* add r8, r8, r0, ror #6 *)
  0xe0022005; (* and r2, r2, r5 *)
  0xe0888003; (* add r8, r8, r3 *)
  0xe0222007; (* eor r2, r2, r7 *)
  0xe02905e9; (* eor r0, r9, r9, ror #11 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe59d2014; (* ldr r2, [sp, #0x14] *)
  0xe029300a; (* eor r3, r9, r10 *)
  0xe59d1008; (* ldr r1, [sp, #0x8] *)
  0xe0200a69; (* eor r0, r0, r9, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0844008; (* add r4, r4, r8 *)
  0xe02cc00a; (* eor r12, r12, r10 *)
  0xe0888160; (* add r8, r8, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe088800c; (* add r8, r8, r12 *)
  0xe1a0c8e1; (* ror r12, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02cc9e1; (* eor r12, r12, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2010; (* ldr r2, [sp, #0x10] *)
  0xe02cc521; (* eor r12, r12, r1, lsr #10 *)
  0xe59d1034; (* ldr r1, [sp, #0x34] *)
  0xe08cc000; (* add r12, r12, r0 *)
  0xe02402e4; (* eor r0, r4, r4, ror #5 *)
  0xe082200c; (* add r2, r2, r12 *)
  0xe02009e4; (* eor r0, r0, r4, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe58d2010; (* str r2, [sp, #0x10] *)
  0xe0252006; (* eor r2, r5, r6 *)
  0xe0877360; (* add r7, r7, r0, ror #6 *)
  0xe0022004; (* and r2, r2, r4 *)
  0xe087700c; (* add r7, r7, r12 *)
  0xe0222006; (* eor r2, r2, r6 *)
  0xe02805e8; (* eor r0, r8, r8, ror #11 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe59d2018; (* ldr r2, [sp, #0x18] *)
  0xe028c009; (* eor r12, r8, r9 *)
  0xe59d100c; (* ldr r1, [sp, #0xc] *)
  0xe0200a68; (* eor r0, r0, r8, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe08bb007; (* add r11, r11, r7 *)
  0xe0233009; (* eor r3, r3, r9 *)
  0xe0877160; (* add r7, r7, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe0877003; (* add r7, r7, r3 *)
  0xe1a038e1; (* ror r3, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02339e1; (* eor r3, r3, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2014; (* ldr r2, [sp, #0x14] *)
  0xe0233521; (* eor r3, r3, r1, lsr #10 *)
  0xe59d1038; (* ldr r1, [sp, #0x38] *)
  0xe0833000; (* add r3, r3, r0 *)
  0xe02b02eb; (* eor r0, r11, r11, ror #5 *)
  0xe0822003; (* add r2, r2, r3 *)
  0xe02009eb; (* eor r0, r0, r11, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe58d2014; (* str r2, [sp, #0x14] *)
  0xe0242005; (* eor r2, r4, r5 *)
  0xe0866360; (* add r6, r6, r0, ror #6 *)
  0xe002200b; (* and r2, r2, r11 *)
  0xe0866003; (* add r6, r6, r3 *)
  0xe0222005; (* eor r2, r2, r5 *)
  0xe02705e7; (* eor r0, r7, r7, ror #11 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe59d201c; (* ldr r2, [sp, #0x1c] *)
  0xe0273008; (* eor r3, r7, r8 *)
  0xe59d1010; (* ldr r1, [sp, #0x10] *)
  0xe0200a67; (* eor r0, r0, r7, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe08aa006; (* add r10, r10, r6 *)
  0xe02cc008; (* eor r12, r12, r8 *)
  0xe0866160; (* add r6, r6, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe086600c; (* add r6, r6, r12 *)
  0xe1a0c8e1; (* ror r12, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02cc9e1; (* eor r12, r12, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2018; (* ldr r2, [sp, #0x18] *)
  0xe02cc521; (* eor r12, r12, r1, lsr #10 *)
  0xe59d103c; (* ldr r1, [sp, #0x3c] *)
  0xe08cc000; (* add r12, r12, r0 *)
  0xe02a02ea; (* eor r0, r10, r10, ror #5 *)
  0xe082200c; (* add r2, r2, r12 *)
  0xe02009ea; (* eor r0, r0, r10, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe58d2018; (* str r2, [sp, #0x18] *)
  0xe02b2004; (* eor r2, r11, r4 *)
  0xe0855360; (* add r5, r5, r0, ror #6 *)
  0xe002200a; (* and r2, r2, r10 *)
  0xe085500c; (* add r5, r5, r12 *)
  0xe0222004; (* eor r2, r2, r4 *)
  0xe02605e6; (* eor r0, r6, r6, ror #11 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe59d2020; (* ldr r2, [sp, #0x20] *)
  0xe026c007; (* eor r12, r6, r7 *)
  0xe59d1014; (* ldr r1, [sp, #0x14] *)
  0xe0200a66; (* eor r0, r0, r6, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0899005; (* add r9, r9, r5 *)
  0xe0233007; (* eor r3, r3, r7 *)
  0xe0855160; (* add r5, r5, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe0855003; (* add r5, r5, r3 *)
  0xe1a038e1; (* ror r3, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02339e1; (* eor r3, r3, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d201c; (* ldr r2, [sp, #0x1c] *)
  0xe0233521; (* eor r3, r3, r1, lsr #10 *)
  0xe59d1000; (* ldr r1, [sp] *)
  0xe0833000; (* add r3, r3, r0 *)
  0xe02902e9; (* eor r0, r9, r9, ror #5 *)
  0xe0822003; (* add r2, r2, r3 *)
  0xe02009e9; (* eor r0, r0, r9, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe58d201c; (* str r2, [sp, #0x1c] *)
  0xe02a200b; (* eor r2, r10, r11 *)
  0xe0844360; (* add r4, r4, r0, ror #6 *)
  0xe0022009; (* and r2, r2, r9 *)
  0xe0844003; (* add r4, r4, r3 *)
  0xe022200b; (* eor r2, r2, r11 *)
  0xe02505e5; (* eor r0, r5, r5, ror #11 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe59d2024; (* ldr r2, [sp, #0x24] *)
  0xe0253006; (* eor r3, r5, r6 *)
  0xe59d1018; (* ldr r1, [sp, #0x18] *)
  0xe0200a65; (* eor r0, r0, r5, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0888004; (* add r8, r8, r4 *)
  0xe02cc006; (* eor r12, r12, r6 *)
  0xe0844160; (* add r4, r4, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe084400c; (* add r4, r4, r12 *)
  0xe1a0c8e1; (* ror r12, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02cc9e1; (* eor r12, r12, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2020; (* ldr r2, [sp, #0x20] *)
  0xe02cc521; (* eor r12, r12, r1, lsr #10 *)
  0xe59d1004; (* ldr r1, [sp, #0x4] *)
  0xe08cc000; (* add r12, r12, r0 *)
  0xe02802e8; (* eor r0, r8, r8, ror #5 *)
  0xe082200c; (* add r2, r2, r12 *)
  0xe02009e8; (* eor r0, r0, r8, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe58d2020; (* str r2, [sp, #0x20] *)
  0xe029200a; (* eor r2, r9, r10 *)
  0xe08bb360; (* add r11, r11, r0, ror #6 *)
  0xe0022008; (* and r2, r2, r8 *)
  0xe08bb00c; (* add r11, r11, r12 *)
  0xe022200a; (* eor r2, r2, r10 *)
  0xe02405e4; (* eor r0, r4, r4, ror #11 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe59d2028; (* ldr r2, [sp, #0x28] *)
  0xe024c005; (* eor r12, r4, r5 *)
  0xe59d101c; (* ldr r1, [sp, #0x1c] *)
  0xe0200a64; (* eor r0, r0, r4, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe087700b; (* add r7, r7, r11 *)
  0xe0233005; (* eor r3, r3, r5 *)
  0xe08bb160; (* add r11, r11, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe08bb003; (* add r11, r11, r3 *)
  0xe1a038e1; (* ror r3, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02339e1; (* eor r3, r3, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2024; (* ldr r2, [sp, #0x24] *)
  0xe0233521; (* eor r3, r3, r1, lsr #10 *)
  0xe59d1008; (* ldr r1, [sp, #0x8] *)
  0xe0833000; (* add r3, r3, r0 *)
  0xe02702e7; (* eor r0, r7, r7, ror #5 *)
  0xe0822003; (* add r2, r2, r3 *)
  0xe02009e7; (* eor r0, r0, r7, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe58d2024; (* str r2, [sp, #0x24] *)
  0xe0282009; (* eor r2, r8, r9 *)
  0xe08aa360; (* add r10, r10, r0, ror #6 *)
  0xe0022007; (* and r2, r2, r7 *)
  0xe08aa003; (* add r10, r10, r3 *)
  0xe0222009; (* eor r2, r2, r9 *)
  0xe02b05eb; (* eor r0, r11, r11, ror #11 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe59d202c; (* ldr r2, [sp, #0x2c] *)
  0xe02b3004; (* eor r3, r11, r4 *)
  0xe59d1020; (* ldr r1, [sp, #0x20] *)
  0xe0200a6b; (* eor r0, r0, r11, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe086600a; (* add r6, r6, r10 *)
  0xe02cc004; (* eor r12, r12, r4 *)
  0xe08aa160; (* add r10, r10, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe08aa00c; (* add r10, r10, r12 *)
  0xe1a0c8e1; (* ror r12, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02cc9e1; (* eor r12, r12, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2028; (* ldr r2, [sp, #0x28] *)
  0xe02cc521; (* eor r12, r12, r1, lsr #10 *)
  0xe59d100c; (* ldr r1, [sp, #0xc] *)
  0xe08cc000; (* add r12, r12, r0 *)
  0xe02602e6; (* eor r0, r6, r6, ror #5 *)
  0xe082200c; (* add r2, r2, r12 *)
  0xe02009e6; (* eor r0, r0, r6, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe58d2028; (* str r2, [sp, #0x28] *)
  0xe0272008; (* eor r2, r7, r8 *)
  0xe0899360; (* add r9, r9, r0, ror #6 *)
  0xe0022006; (* and r2, r2, r6 *)
  0xe089900c; (* add r9, r9, r12 *)
  0xe0222008; (* eor r2, r2, r8 *)
  0xe02a05ea; (* eor r0, r10, r10, ror #11 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe59d2030; (* ldr r2, [sp, #0x30] *)
  0xe02ac00b; (* eor r12, r10, r11 *)
  0xe59d1024; (* ldr r1, [sp, #0x24] *)
  0xe0200a6a; (* eor r0, r0, r10, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0855009; (* add r5, r5, r9 *)
  0xe023300b; (* eor r3, r3, r11 *)
  0xe0899160; (* add r9, r9, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe0899003; (* add r9, r9, r3 *)
  0xe1a038e1; (* ror r3, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02339e1; (* eor r3, r3, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d202c; (* ldr r2, [sp, #0x2c] *)
  0xe0233521; (* eor r3, r3, r1, lsr #10 *)
  0xe59d1010; (* ldr r1, [sp, #0x10] *)
  0xe0833000; (* add r3, r3, r0 *)
  0xe02502e5; (* eor r0, r5, r5, ror #5 *)
  0xe0822003; (* add r2, r2, r3 *)
  0xe02009e5; (* eor r0, r0, r5, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe58d202c; (* str r2, [sp, #0x2c] *)
  0xe0262007; (* eor r2, r6, r7 *)
  0xe0888360; (* add r8, r8, r0, ror #6 *)
  0xe0022005; (* and r2, r2, r5 *)
  0xe0888003; (* add r8, r8, r3 *)
  0xe0222007; (* eor r2, r2, r7 *)
  0xe02905e9; (* eor r0, r9, r9, ror #11 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe59d2034; (* ldr r2, [sp, #0x34] *)
  0xe029300a; (* eor r3, r9, r10 *)
  0xe59d1028; (* ldr r1, [sp, #0x28] *)
  0xe0200a69; (* eor r0, r0, r9, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0844008; (* add r4, r4, r8 *)
  0xe02cc00a; (* eor r12, r12, r10 *)
  0xe0888160; (* add r8, r8, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe088800c; (* add r8, r8, r12 *)
  0xe1a0c8e1; (* ror r12, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02cc9e1; (* eor r12, r12, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2030; (* ldr r2, [sp, #0x30] *)
  0xe02cc521; (* eor r12, r12, r1, lsr #10 *)
  0xe59d1014; (* ldr r1, [sp, #0x14] *)
  0xe08cc000; (* add r12, r12, r0 *)
  0xe02402e4; (* eor r0, r4, r4, ror #5 *)
  0xe082200c; (* add r2, r2, r12 *)
  0xe02009e4; (* eor r0, r0, r4, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe58d2030; (* str r2, [sp, #0x30] *)
  0xe0252006; (* eor r2, r5, r6 *)
  0xe0877360; (* add r7, r7, r0, ror #6 *)
  0xe0022004; (* and r2, r2, r4 *)
  0xe087700c; (* add r7, r7, r12 *)
  0xe0222006; (* eor r2, r2, r6 *)
  0xe02805e8; (* eor r0, r8, r8, ror #11 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe59d2038; (* ldr r2, [sp, #0x38] *)
  0xe028c009; (* eor r12, r8, r9 *)
  0xe59d102c; (* ldr r1, [sp, #0x2c] *)
  0xe0200a68; (* eor r0, r0, r8, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe08bb007; (* add r11, r11, r7 *)
  0xe0233009; (* eor r3, r3, r9 *)
  0xe0877160; (* add r7, r7, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe0877003; (* add r7, r7, r3 *)
  0xe1a038e1; (* ror r3, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02339e1; (* eor r3, r3, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2034; (* ldr r2, [sp, #0x34] *)
  0xe0233521; (* eor r3, r3, r1, lsr #10 *)
  0xe59d1018; (* ldr r1, [sp, #0x18] *)
  0xe0833000; (* add r3, r3, r0 *)
  0xe02b02eb; (* eor r0, r11, r11, ror #5 *)
  0xe0822003; (* add r2, r2, r3 *)
  0xe02009eb; (* eor r0, r0, r11, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe58d2034; (* str r2, [sp, #0x34] *)
  0xe0242005; (* eor r2, r4, r5 *)
  0xe0866360; (* add r6, r6, r0, ror #6 *)
  0xe002200b; (* and r2, r2, r11 *)
  0xe0866003; (* add r6, r6, r3 *)
  0xe0222005; (* eor r2, r2, r5 *)
  0xe02705e7; (* eor r0, r7, r7, ror #11 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe59d203c; (* ldr r2, [sp, #0x3c] *)
  0xe0273008; (* eor r3, r7, r8 *)
  0xe59d1030; (* ldr r1, [sp, #0x30] *)
  0xe0200a67; (* eor r0, r0, r7, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe08aa006; (* add r10, r10, r6 *)
  0xe02cc008; (* eor r12, r12, r8 *)
  0xe0866160; (* add r6, r6, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe086600c; (* add r6, r6, r12 *)
  0xe1a0c8e1; (* ror r12, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02cc9e1; (* eor r12, r12, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d2038; (* ldr r2, [sp, #0x38] *)
  0xe02cc521; (* eor r12, r12, r1, lsr #10 *)
  0xe59d101c; (* ldr r1, [sp, #0x1c] *)
  0xe08cc000; (* add r12, r12, r0 *)
  0xe02a02ea; (* eor r0, r10, r10, ror #5 *)
  0xe082200c; (* add r2, r2, r12 *)
  0xe02009ea; (* eor r0, r0, r10, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49ec004; (* ldr r12, [lr], #4 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe58d2038; (* str r2, [sp, #0x38] *)
  0xe02b2004; (* eor r2, r11, r4 *)
  0xe0855360; (* add r5, r5, r0, ror #6 *)
  0xe002200a; (* and r2, r2, r10 *)
  0xe085500c; (* add r5, r5, r12 *)
  0xe0222004; (* eor r2, r2, r4 *)
  0xe02605e6; (* eor r0, r6, r6, ror #11 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe59d2000; (* ldr r2, [sp] *)
  0xe026c007; (* eor r12, r6, r7 *)
  0xe59d1034; (* ldr r1, [sp, #0x34] *)
  0xe0200a66; (* eor r0, r0, r6, ror #20 *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0899005; (* add r9, r9, r5 *)
  0xe0233007; (* eor r3, r3, r7 *)
  0xe0855160; (* add r5, r5, r0, ror #2 *)
  0xe1a003e2; (* ror r0, r2, #7 *)
  0xe0855003; (* add r5, r5, r3 *)
  0xe1a038e1; (* ror r3, r1, #17 *)
  0xe0200962; (* eor r0, r0, r2, ror #18 *)
  0xe02339e1; (* eor r3, r3, r1, ror #19 *)
  0xe02001a2; (* eor r0, r0, r2, lsr #3 *)
  0xe59d203c; (* ldr r2, [sp, #0x3c] *)
  0xe0233521; (* eor r3, r3, r1, lsr #10 *)
  0xe59d1020; (* ldr r1, [sp, #0x20] *)
  0xe0833000; (* add r3, r3, r0 *)
  0xe02902e9; (* eor r0, r9, r9, ror #5 *)
  0xe0822003; (* add r2, r2, r3 *)
  0xe02009e9; (* eor r0, r0, r9, ror #19 *)
  0xe0822001; (* add r2, r2, r1 *)
  0xe49e3004; (* ldr r3, [lr], #4 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe58d203c; (* str r2, [sp, #0x3c] *)
  0xe02a200b; (* eor r2, r10, r11 *)
  0xe0844360; (* add r4, r4, r0, ror #6 *)
  0xe0022009; (* and r2, r2, r9 *)
  0xe0844003; (* add r4, r4, r3 *)
  0xe022200b; (* eor r2, r2, r11 *)
  0xe02505e5; (* eor r0, r5, r5, ror #11 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe20330ff; (* and r3, r3, #255 *)
  0xe35300f2; (* cmp r3, #242 *)
  0xe59d2004; (* ldr r2, [sp, #0x4] *)
  0xe0253006; (* eor r3, r5, r6 *)
  0xe59d1038; (* ldr r1, [sp, #0x38] *)
  0xe0200a65; (* eor r0, r0, r5, ror #20 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0888004; (* add r8, r8, r4 *)
  0xe02cc006; (* eor r12, r12, r6 *)
  0xe0844160; (* add r4, r4, r0, ror #2 *)
  0x059d3040; (* ldreq r3, [sp, #0x40] *)
  0x1afffdfb; (* bne 0x270c *)
  0xe084400c; (* add r4, r4, r12 *)
  0xe5930000; (* ldr r0, [r3] *)
  0xe5932004; (* ldr r2, [r3, #0x4] *)
  0xe593c008; (* ldr r12, [r3, #0x8] *)
  0xe0844000; (* add r4, r4, r0 *)
  0xe593000c; (* ldr r0, [r3, #0xc] *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe5932010; (* ldr r2, [r3, #0x10] *)
  0xe086600c; (* add r6, r6, r12 *)
  0xe593c014; (* ldr r12, [r3, #0x14] *)
  0xe0877000; (* add r7, r7, r0 *)
  0xe5930018; (* ldr r0, [r3, #0x18] *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe593201c; (* ldr r2, [r3, #0x1c] *)
  0xe089900c; (* add r9, r9, r12 *)
  0xe59d1044; (* ldr r1, [sp, #0x44] *)
  0xe59dc048; (* ldr r12, [sp, #0x48] *)
  0xe08aa000; (* add r10, r10, r0 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe8830ff0; (* stm r3, {r4, r5, r6, r7, r8, r9, r10, r11} *)
  0xe151000c; (* cmp r1, r12 *)
  0xe24eec01; (* sub lr, lr, #256 *)
  0x1afffc8f; (* bne 0x21b8 *)
  0xe28dd04c; (* add sp, sp, #76 *)
  0xe8bd8ff0; (* pop {r4, r5, r6, r7, r8, r9, r10, r11, pc} *)
  0xfffff0dc; (* data *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0x00000000; (* data *)
  0x00000000; (* data *)
  0x00000000; (* data *)
  0x00000000; (* data *)
  0xe92d5ff0; (* push {r4, r5, r6, r7, r8, r9, r10, r11, r12, lr} *)
  0xe24db050; (* sub r11, sp, #80 *)
  0xe51fe040; (* ldr lr, [pc, #-0x40] *)
  0xe08fe00e; (* add lr, pc, lr *)
  0xe3cbb00f; (* bic r11, r11, #15 *)
  0xe1a0c00d; (* mov r12, sp *)
  0xe1a0d00b; (* mov sp, r11 *)
  0xe0812302; (* add r2, r1, r2, lsl #6 *)
  0xf4210a0d; (* vld1.8 {d0, d1}, [r1]! *)
  0xf4212a0d; (* vld1.8 {d2, d3}, [r1]! *)
  0xf4214a0d; (* vld1.8 {d4, d5}, [r1]! *)
  0xf4216a0d; (* vld1.8 {d6, d7}, [r1]! *)
  0xf46e0aad; (* vld1.32 {d16, d17}, [lr:128]! *)
  0xf46e2aad; (* vld1.32 {d18, d19}, [lr:128]! *)
  0xf46e4aad; (* vld1.32 {d20, d21}, [lr:128]! *)
  0xf46e6aad; (* vld1.32 {d22, d23}, [lr:128]! *)
  0xf3b000c0; (* vrev32.8 q0, q0 *)
  0xe58d0040; (* str r0, [sp, #0x40] *)
  0xf3b020c2; (* vrev32.8 q1, q1 *)
  0xe58d1044; (* str r1, [sp, #0x44] *)
  0xe1a0100d; (* mov r1, sp *)
  0xf3b040c4; (* vrev32.8 q2, q2 *)
  0xe58d2048; (* str r2, [sp, #0x48] *)
  0xf3b060c6; (* vrev32.8 q3, q3 *)
  0xe58dc04c; (* str r12, [sp, #0x4c] *)
  0xf26008c0; (* vadd.i32 q8, q8, q0 *)
  0xf26228c2; (* vadd.i32 q9, q9, q1 *)
  0xf4410aad; (* vst1.32 {d16, d17}, [r1:128]! *)
  0xf26448c4; (* vadd.i32 q10, q10, q2 *)
  0xf4412aad; (* vst1.32 {d18, d19}, [r1:128]! *)
  0xf26668c6; (* vadd.i32 q11, q11, q3 *)
  0xf4414aad; (* vst1.32 {d20, d21}, [r1:128]! *)
  0xf4416aad; (* vst1.32 {d22, d23}, [r1:128]! *)
  0xe8900ff0; (* ldm r0, {r4, r5, r6, r7, r8, r9, r10, r11} *)
  0xe2411040; (* sub r1, r1, #64 *)
  0xe59d2000; (* ldr r2, [sp] *)
  0xe02cc00c; (* eor r12, r12, r12 *)
  0xe0253006; (* eor r3, r5, r6 *)
  0xea000000; (* b 0x3050 *)
  0xe320f000; (* nop *)
  0xf2f00442; (* vext.32 q8, q0, q1, #0x1 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe029200a; (* eor r2, r9, r10 *)
  0xe02802e8; (* eor r0, r8, r8, ror #5 *)
  0xf2f42446; (* vext.32 q9, q2, q3, #0x1 *)
  0xe084400c; (* add r4, r4, r12 *)
  0xe0022008; (* and r2, r2, r8 *)
  0xe020c9e8; (* eor r12, r0, r8, ror #19 *)
  0xf3f94070; (* vshr.u32 q10, q8, #0x7 *)
  0xe02405e4; (* eor r0, r4, r4, ror #11 *)
  0xe022200a; (* eor r2, r2, r10 *)
  0xf2200862; (* vadd.i32 q0, q0, q9 *)
  0xe08bb36c; (* add r11, r11, r12, ror #6 *)
  0xe024c005; (* eor r12, r4, r5 *)
  0xf3fd2070; (* vshr.u32 q9, q8, #0x3 *)
  0xe0200a64; (* eor r0, r0, r4, ror #20 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xf3f94570; (* vsli.32 q10, q8, #0x19 *)
  0xe59d2004; (* ldr r2, [sp, #0x4] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xf3ee6070; (* vshr.u32 q11, q8, #0x12 *)
  0xe087700b; (* add r7, r7, r11 *)
  0xe08bb160; (* add r11, r11, r0, ror #2 *)
  0xe0233005; (* eor r3, r3, r5 *)
  0xf34221f4; (* veor q9, q9, q10 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xf3ee6570; (* vsli.32 q11, q8, #0xe *)
  0xe0282009; (* eor r2, r8, r9 *)
  0xe02702e7; (* eor r0, r7, r7, ror #5 *)
  0xf3ef8017; (* vshr.u32 d24, d7, #0x11 *)
  0xe08bb003; (* add r11, r11, r3 *)
  0xe0022007; (* and r2, r2, r7 *)
  0xf34221f6; (* veor q9, q9, q11 *)
  0xe02039e7; (* eor r3, r0, r7, ror #19 *)
  0xe02b05eb; (* eor r0, r11, r11, ror #11 *)
  0xf3ef8517; (* vsli.32 d24, d7, #0xf *)
  0xe0222009; (* eor r2, r2, r9 *)
  0xe08aa363; (* add r10, r10, r3, ror #6 *)
  0xf3f69017; (* vshr.u32 d25, d7, #0xa *)
  0xe02b3004; (* eor r3, r11, r4 *)
  0xe0200a6b; (* eor r0, r0, r11, ror #20 *)
  0xf2200862; (* vadd.i32 q0, q0, q9 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe59d2008; (* ldr r2, [sp, #0x8] *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe086600a; (* add r6, r6, r10 *)
  0xf3ed8017; (* vshr.u32 d24, d7, #0x13 *)
  0xe08aa160; (* add r10, r10, r0, ror #2 *)
  0xe02cc004; (* eor r12, r12, r4 *)
  0xf3ed8517; (* vsli.32 d24, d7, #0xd *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe0272008; (* eor r2, r7, r8 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe02602e6; (* eor r0, r6, r6, ror #5 *)
  0xe08aa00c; (* add r10, r10, r12 *)
  0xf2200829; (* vadd.i32 d0, d0, d25 *)
  0xe0022006; (* and r2, r2, r6 *)
  0xe020c9e6; (* eor r12, r0, r6, ror #19 *)
  0xf3ef8010; (* vshr.u32 d24, d0, #0x11 *)
  0xe02a05ea; (* eor r0, r10, r10, ror #11 *)
  0xe0222008; (* eor r2, r2, r8 *)
  0xf3ef8510; (* vsli.32 d24, d0, #0xf *)
  0xe089936c; (* add r9, r9, r12, ror #6 *)
  0xe02ac00b; (* eor r12, r10, r11 *)
  0xf3f69010; (* vshr.u32 d25, d0, #0xa *)
  0xe0200a6a; (* eor r0, r0, r10, ror #20 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe59d200c; (* ldr r2, [sp, #0xc] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xf3ed8010; (* vshr.u32 d24, d0, #0x13 *)
  0xe0855009; (* add r5, r5, r9 *)
  0xe0899160; (* add r9, r9, r0, ror #2 *)
  0xe023300b; (* eor r3, r3, r11 *)
  0xf46e0aad; (* vld1.32 {d16, d17}, [lr:128]! *)
  0xe0888002; (* add r8, r8, r2 *)
  0xf3ed8510; (* vsli.32 d24, d0, #0xd *)
  0xe0262007; (* eor r2, r6, r7 *)
  0xe02502e5; (* eor r0, r5, r5, ror #5 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe0899003; (* add r9, r9, r3 *)
  0xe0022005; (* and r2, r2, r5 *)
  0xf2211829; (* vadd.i32 d1, d1, d25 *)
  0xe02039e5; (* eor r3, r0, r5, ror #19 *)
  0xe02905e9; (* eor r0, r9, r9, ror #11 *)
  0xf26008c0; (* vadd.i32 q8, q8, q0 *)
  0xe0222007; (* eor r2, r2, r7 *)
  0xe0888363; (* add r8, r8, r3, ror #6 *)
  0xe029300a; (* eor r3, r9, r10 *)
  0xe0200a69; (* eor r0, r0, r9, ror #20 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe59d2010; (* ldr r2, [sp, #0x10] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0844008; (* add r4, r4, r8 *)
  0xf4410aad; (* vst1.32 {d16, d17}, [r1:128]! *)
  0xe0888160; (* add r8, r8, r0, ror #2 *)
  0xe02cc00a; (* eor r12, r12, r10 *)
  0xf2f20444; (* vext.32 q8, q1, q2, #0x1 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe0252006; (* eor r2, r5, r6 *)
  0xe02402e4; (* eor r0, r4, r4, ror #5 *)
  0xf2f62440; (* vext.32 q9, q3, q0, #0x1 *)
  0xe088800c; (* add r8, r8, r12 *)
  0xe0022004; (* and r2, r2, r4 *)
  0xe020c9e4; (* eor r12, r0, r4, ror #19 *)
  0xf3f94070; (* vshr.u32 q10, q8, #0x7 *)
  0xe02805e8; (* eor r0, r8, r8, ror #11 *)
  0xe0222006; (* eor r2, r2, r6 *)
  0xf2222862; (* vadd.i32 q1, q1, q9 *)
  0xe087736c; (* add r7, r7, r12, ror #6 *)
  0xe028c009; (* eor r12, r8, r9 *)
  0xf3fd2070; (* vshr.u32 q9, q8, #0x3 *)
  0xe0200a68; (* eor r0, r0, r8, ror #20 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xf3f94570; (* vsli.32 q10, q8, #0x19 *)
  0xe59d2014; (* ldr r2, [sp, #0x14] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xf3ee6070; (* vshr.u32 q11, q8, #0x12 *)
  0xe08bb007; (* add r11, r11, r7 *)
  0xe0877160; (* add r7, r7, r0, ror #2 *)
  0xe0233009; (* eor r3, r3, r9 *)
  0xf34221f4; (* veor q9, q9, q10 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xf3ee6570; (* vsli.32 q11, q8, #0xe *)
  0xe0242005; (* eor r2, r4, r5 *)
  0xe02b02eb; (* eor r0, r11, r11, ror #5 *)
  0xf3ef8011; (* vshr.u32 d24, d1, #0x11 *)
  0xe0877003; (* add r7, r7, r3 *)
  0xe002200b; (* and r2, r2, r11 *)
  0xf34221f6; (* veor q9, q9, q11 *)
  0xe02039eb; (* eor r3, r0, r11, ror #19 *)
  0xe02705e7; (* eor r0, r7, r7, ror #11 *)
  0xf3ef8511; (* vsli.32 d24, d1, #0xf *)
  0xe0222005; (* eor r2, r2, r5 *)
  0xe0866363; (* add r6, r6, r3, ror #6 *)
  0xf3f69011; (* vshr.u32 d25, d1, #0xa *)
  0xe0273008; (* eor r3, r7, r8 *)
  0xe0200a67; (* eor r0, r0, r7, ror #20 *)
  0xf2222862; (* vadd.i32 q1, q1, q9 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe59d2018; (* ldr r2, [sp, #0x18] *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe08aa006; (* add r10, r10, r6 *)
  0xf3ed8011; (* vshr.u32 d24, d1, #0x13 *)
  0xe0866160; (* add r6, r6, r0, ror #2 *)
  0xe02cc008; (* eor r12, r12, r8 *)
  0xf3ed8511; (* vsli.32 d24, d1, #0xd *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe02b2004; (* eor r2, r11, r4 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe02a02ea; (* eor r0, r10, r10, ror #5 *)
  0xe086600c; (* add r6, r6, r12 *)
  0xf2222829; (* vadd.i32 d2, d2, d25 *)
  0xe002200a; (* and r2, r2, r10 *)
  0xe020c9ea; (* eor r12, r0, r10, ror #19 *)
  0xf3ef8012; (* vshr.u32 d24, d2, #0x11 *)
  0xe02605e6; (* eor r0, r6, r6, ror #11 *)
  0xe0222004; (* eor r2, r2, r4 *)
  0xf3ef8512; (* vsli.32 d24, d2, #0xf *)
  0xe085536c; (* add r5, r5, r12, ror #6 *)
  0xe026c007; (* eor r12, r6, r7 *)
  0xf3f69012; (* vshr.u32 d25, d2, #0xa *)
  0xe0200a66; (* eor r0, r0, r6, ror #20 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe59d201c; (* ldr r2, [sp, #0x1c] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xf3ed8012; (* vshr.u32 d24, d2, #0x13 *)
  0xe0899005; (* add r9, r9, r5 *)
  0xe0855160; (* add r5, r5, r0, ror #2 *)
  0xe0233007; (* eor r3, r3, r7 *)
  0xf46e0aad; (* vld1.32 {d16, d17}, [lr:128]! *)
  0xe0844002; (* add r4, r4, r2 *)
  0xf3ed8512; (* vsli.32 d24, d2, #0xd *)
  0xe02a200b; (* eor r2, r10, r11 *)
  0xe02902e9; (* eor r0, r9, r9, ror #5 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe0855003; (* add r5, r5, r3 *)
  0xe0022009; (* and r2, r2, r9 *)
  0xf2233829; (* vadd.i32 d3, d3, d25 *)
  0xe02039e9; (* eor r3, r0, r9, ror #19 *)
  0xe02505e5; (* eor r0, r5, r5, ror #11 *)
  0xf26008c2; (* vadd.i32 q8, q8, q1 *)
  0xe022200b; (* eor r2, r2, r11 *)
  0xe0844363; (* add r4, r4, r3, ror #6 *)
  0xe0253006; (* eor r3, r5, r6 *)
  0xe0200a65; (* eor r0, r0, r5, ror #20 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe59d2020; (* ldr r2, [sp, #0x20] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0888004; (* add r8, r8, r4 *)
  0xf4410aad; (* vst1.32 {d16, d17}, [r1:128]! *)
  0xe0844160; (* add r4, r4, r0, ror #2 *)
  0xe02cc006; (* eor r12, r12, r6 *)
  0xf2f40446; (* vext.32 q8, q2, q3, #0x1 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe029200a; (* eor r2, r9, r10 *)
  0xe02802e8; (* eor r0, r8, r8, ror #5 *)
  0xf2f02442; (* vext.32 q9, q0, q1, #0x1 *)
  0xe084400c; (* add r4, r4, r12 *)
  0xe0022008; (* and r2, r2, r8 *)
  0xe020c9e8; (* eor r12, r0, r8, ror #19 *)
  0xf3f94070; (* vshr.u32 q10, q8, #0x7 *)
  0xe02405e4; (* eor r0, r4, r4, ror #11 *)
  0xe022200a; (* eor r2, r2, r10 *)
  0xf2244862; (* vadd.i32 q2, q2, q9 *)
  0xe08bb36c; (* add r11, r11, r12, ror #6 *)
  0xe024c005; (* eor r12, r4, r5 *)
  0xf3fd2070; (* vshr.u32 q9, q8, #0x3 *)
  0xe0200a64; (* eor r0, r0, r4, ror #20 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xf3f94570; (* vsli.32 q10, q8, #0x19 *)
  0xe59d2024; (* ldr r2, [sp, #0x24] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xf3ee6070; (* vshr.u32 q11, q8, #0x12 *)
  0xe087700b; (* add r7, r7, r11 *)
  0xe08bb160; (* add r11, r11, r0, ror #2 *)
  0xe0233005; (* eor r3, r3, r5 *)
  0xf34221f4; (* veor q9, q9, q10 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xf3ee6570; (* vsli.32 q11, q8, #0xe *)
  0xe0282009; (* eor r2, r8, r9 *)
  0xe02702e7; (* eor r0, r7, r7, ror #5 *)
  0xf3ef8013; (* vshr.u32 d24, d3, #0x11 *)
  0xe08bb003; (* add r11, r11, r3 *)
  0xe0022007; (* and r2, r2, r7 *)
  0xf34221f6; (* veor q9, q9, q11 *)
  0xe02039e7; (* eor r3, r0, r7, ror #19 *)
  0xe02b05eb; (* eor r0, r11, r11, ror #11 *)
  0xf3ef8513; (* vsli.32 d24, d3, #0xf *)
  0xe0222009; (* eor r2, r2, r9 *)
  0xe08aa363; (* add r10, r10, r3, ror #6 *)
  0xf3f69013; (* vshr.u32 d25, d3, #0xa *)
  0xe02b3004; (* eor r3, r11, r4 *)
  0xe0200a6b; (* eor r0, r0, r11, ror #20 *)
  0xf2244862; (* vadd.i32 q2, q2, q9 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe59d2028; (* ldr r2, [sp, #0x28] *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe086600a; (* add r6, r6, r10 *)
  0xf3ed8013; (* vshr.u32 d24, d3, #0x13 *)
  0xe08aa160; (* add r10, r10, r0, ror #2 *)
  0xe02cc004; (* eor r12, r12, r4 *)
  0xf3ed8513; (* vsli.32 d24, d3, #0xd *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe0272008; (* eor r2, r7, r8 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe02602e6; (* eor r0, r6, r6, ror #5 *)
  0xe08aa00c; (* add r10, r10, r12 *)
  0xf2244829; (* vadd.i32 d4, d4, d25 *)
  0xe0022006; (* and r2, r2, r6 *)
  0xe020c9e6; (* eor r12, r0, r6, ror #19 *)
  0xf3ef8014; (* vshr.u32 d24, d4, #0x11 *)
  0xe02a05ea; (* eor r0, r10, r10, ror #11 *)
  0xe0222008; (* eor r2, r2, r8 *)
  0xf3ef8514; (* vsli.32 d24, d4, #0xf *)
  0xe089936c; (* add r9, r9, r12, ror #6 *)
  0xe02ac00b; (* eor r12, r10, r11 *)
  0xf3f69014; (* vshr.u32 d25, d4, #0xa *)
  0xe0200a6a; (* eor r0, r0, r10, ror #20 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe59d202c; (* ldr r2, [sp, #0x2c] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xf3ed8014; (* vshr.u32 d24, d4, #0x13 *)
  0xe0855009; (* add r5, r5, r9 *)
  0xe0899160; (* add r9, r9, r0, ror #2 *)
  0xe023300b; (* eor r3, r3, r11 *)
  0xf46e0aad; (* vld1.32 {d16, d17}, [lr:128]! *)
  0xe0888002; (* add r8, r8, r2 *)
  0xf3ed8514; (* vsli.32 d24, d4, #0xd *)
  0xe0262007; (* eor r2, r6, r7 *)
  0xe02502e5; (* eor r0, r5, r5, ror #5 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe0899003; (* add r9, r9, r3 *)
  0xe0022005; (* and r2, r2, r5 *)
  0xf2255829; (* vadd.i32 d5, d5, d25 *)
  0xe02039e5; (* eor r3, r0, r5, ror #19 *)
  0xe02905e9; (* eor r0, r9, r9, ror #11 *)
  0xf26008c4; (* vadd.i32 q8, q8, q2 *)
  0xe0222007; (* eor r2, r2, r7 *)
  0xe0888363; (* add r8, r8, r3, ror #6 *)
  0xe029300a; (* eor r3, r9, r10 *)
  0xe0200a69; (* eor r0, r0, r9, ror #20 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe59d2030; (* ldr r2, [sp, #0x30] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0844008; (* add r4, r4, r8 *)
  0xf4410aad; (* vst1.32 {d16, d17}, [r1:128]! *)
  0xe0888160; (* add r8, r8, r0, ror #2 *)
  0xe02cc00a; (* eor r12, r12, r10 *)
  0xf2f60440; (* vext.32 q8, q3, q0, #0x1 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe0252006; (* eor r2, r5, r6 *)
  0xe02402e4; (* eor r0, r4, r4, ror #5 *)
  0xf2f22444; (* vext.32 q9, q1, q2, #0x1 *)
  0xe088800c; (* add r8, r8, r12 *)
  0xe0022004; (* and r2, r2, r4 *)
  0xe020c9e4; (* eor r12, r0, r4, ror #19 *)
  0xf3f94070; (* vshr.u32 q10, q8, #0x7 *)
  0xe02805e8; (* eor r0, r8, r8, ror #11 *)
  0xe0222006; (* eor r2, r2, r6 *)
  0xf2266862; (* vadd.i32 q3, q3, q9 *)
  0xe087736c; (* add r7, r7, r12, ror #6 *)
  0xe028c009; (* eor r12, r8, r9 *)
  0xf3fd2070; (* vshr.u32 q9, q8, #0x3 *)
  0xe0200a68; (* eor r0, r0, r8, ror #20 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xf3f94570; (* vsli.32 q10, q8, #0x19 *)
  0xe59d2034; (* ldr r2, [sp, #0x34] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xf3ee6070; (* vshr.u32 q11, q8, #0x12 *)
  0xe08bb007; (* add r11, r11, r7 *)
  0xe0877160; (* add r7, r7, r0, ror #2 *)
  0xe0233009; (* eor r3, r3, r9 *)
  0xf34221f4; (* veor q9, q9, q10 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xf3ee6570; (* vsli.32 q11, q8, #0xe *)
  0xe0242005; (* eor r2, r4, r5 *)
  0xe02b02eb; (* eor r0, r11, r11, ror #5 *)
  0xf3ef8015; (* vshr.u32 d24, d5, #0x11 *)
  0xe0877003; (* add r7, r7, r3 *)
  0xe002200b; (* and r2, r2, r11 *)
  0xf34221f6; (* veor q9, q9, q11 *)
  0xe02039eb; (* eor r3, r0, r11, ror #19 *)
  0xe02705e7; (* eor r0, r7, r7, ror #11 *)
  0xf3ef8515; (* vsli.32 d24, d5, #0xf *)
  0xe0222005; (* eor r2, r2, r5 *)
  0xe0866363; (* add r6, r6, r3, ror #6 *)
  0xf3f69015; (* vshr.u32 d25, d5, #0xa *)
  0xe0273008; (* eor r3, r7, r8 *)
  0xe0200a67; (* eor r0, r0, r7, ror #20 *)
  0xf2266862; (* vadd.i32 q3, q3, q9 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe59d2038; (* ldr r2, [sp, #0x38] *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe08aa006; (* add r10, r10, r6 *)
  0xf3ed8015; (* vshr.u32 d24, d5, #0x13 *)
  0xe0866160; (* add r6, r6, r0, ror #2 *)
  0xe02cc008; (* eor r12, r12, r8 *)
  0xf3ed8515; (* vsli.32 d24, d5, #0xd *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe02b2004; (* eor r2, r11, r4 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe02a02ea; (* eor r0, r10, r10, ror #5 *)
  0xe086600c; (* add r6, r6, r12 *)
  0xf2266829; (* vadd.i32 d6, d6, d25 *)
  0xe002200a; (* and r2, r2, r10 *)
  0xe020c9ea; (* eor r12, r0, r10, ror #19 *)
  0xf3ef8016; (* vshr.u32 d24, d6, #0x11 *)
  0xe02605e6; (* eor r0, r6, r6, ror #11 *)
  0xe0222004; (* eor r2, r2, r4 *)
  0xf3ef8516; (* vsli.32 d24, d6, #0xf *)
  0xe085536c; (* add r5, r5, r12, ror #6 *)
  0xe026c007; (* eor r12, r6, r7 *)
  0xf3f69016; (* vshr.u32 d25, d6, #0xa *)
  0xe0200a66; (* eor r0, r0, r6, ror #20 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe59d203c; (* ldr r2, [sp, #0x3c] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xf3ed8016; (* vshr.u32 d24, d6, #0x13 *)
  0xe0899005; (* add r9, r9, r5 *)
  0xe0855160; (* add r5, r5, r0, ror #2 *)
  0xe0233007; (* eor r3, r3, r7 *)
  0xf46e0aad; (* vld1.32 {d16, d17}, [lr:128]! *)
  0xe0844002; (* add r4, r4, r2 *)
  0xf3ed8516; (* vsli.32 d24, d6, #0xd *)
  0xe02a200b; (* eor r2, r10, r11 *)
  0xe02902e9; (* eor r0, r9, r9, ror #5 *)
  0xf34991b8; (* veor d25, d25, d24 *)
  0xe0855003; (* add r5, r5, r3 *)
  0xe0022009; (* and r2, r2, r9 *)
  0xf2277829; (* vadd.i32 d7, d7, d25 *)
  0xe02039e9; (* eor r3, r0, r9, ror #19 *)
  0xe02505e5; (* eor r0, r5, r5, ror #11 *)
  0xf26008c6; (* vadd.i32 q8, q8, q3 *)
  0xe022200b; (* eor r2, r2, r11 *)
  0xe0844363; (* add r4, r4, r3, ror #6 *)
  0xe0253006; (* eor r3, r5, r6 *)
  0xe0200a65; (* eor r0, r0, r5, ror #20 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe59e2000; (* ldr r2, [lr] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0888004; (* add r8, r8, r4 *)
  0xf4410aad; (* vst1.32 {d16, d17}, [r1:128]! *)
  0xe0844160; (* add r4, r4, r0, ror #2 *)
  0xe02cc006; (* eor r12, r12, r6 *)
  0xe3320000; (* teq r2, #0 *)
  0xe59d2000; (* ldr r2, [sp] *)
  0xe2411040; (* sub r1, r1, #64 *)
  0x1afffe73; (* bne 0x3050 *)
  0xe59d1044; (* ldr r1, [sp, #0x44] *)
  0xe59d0048; (* ldr r0, [sp, #0x48] *)
  0xe24eec01; (* sub lr, lr, #256 *)
  0xe1310000; (* teq r1, r0 *)
  0x02411040; (* subeq r1, r1, #64 *)
  0xf4210a0d; (* vld1.8 {d0, d1}, [r1]! *)
  0xf4212a0d; (* vld1.8 {d2, d3}, [r1]! *)
  0xf4214a0d; (* vld1.8 {d4, d5}, [r1]! *)
  0xf4216a0d; (* vld1.8 {d6, d7}, [r1]! *)
  0x158d1044; (* strne r1, [sp, #0x44] *)
  0xe1a0100d; (* mov r1, sp *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe029200a; (* eor r2, r9, r10 *)
  0xe02802e8; (* eor r0, r8, r8, ror #5 *)
  0xe084400c; (* add r4, r4, r12 *)
  0xf46e0aad; (* vld1.32 {d16, d17}, [lr:128]! *)
  0xe0022008; (* and r2, r2, r8 *)
  0xe020c9e8; (* eor r12, r0, r8, ror #19 *)
  0xe02405e4; (* eor r0, r4, r4, ror #11 *)
  0xe022200a; (* eor r2, r2, r10 *)
  0xf3b000c0; (* vrev32.8 q0, q0 *)
  0xe08bb36c; (* add r11, r11, r12, ror #6 *)
  0xe024c005; (* eor r12, r4, r5 *)
  0xe0200a64; (* eor r0, r0, r4, ror #20 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xf26008c0; (* vadd.i32 q8, q8, q0 *)
  0xe59d2004; (* ldr r2, [sp, #0x4] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe087700b; (* add r7, r7, r11 *)
  0xe08bb160; (* add r11, r11, r0, ror #2 *)
  0xe0233005; (* eor r3, r3, r5 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe0282009; (* eor r2, r8, r9 *)
  0xe02702e7; (* eor r0, r7, r7, ror #5 *)
  0xe08bb003; (* add r11, r11, r3 *)
  0xe0022007; (* and r2, r2, r7 *)
  0xe02039e7; (* eor r3, r0, r7, ror #19 *)
  0xe02b05eb; (* eor r0, r11, r11, ror #11 *)
  0xe0222009; (* eor r2, r2, r9 *)
  0xe08aa363; (* add r10, r10, r3, ror #6 *)
  0xe02b3004; (* eor r3, r11, r4 *)
  0xe0200a6b; (* eor r0, r0, r11, ror #20 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe59d2008; (* ldr r2, [sp, #0x8] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe086600a; (* add r6, r6, r10 *)
  0xe08aa160; (* add r10, r10, r0, ror #2 *)
  0xe02cc004; (* eor r12, r12, r4 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe0272008; (* eor r2, r7, r8 *)
  0xe02602e6; (* eor r0, r6, r6, ror #5 *)
  0xe08aa00c; (* add r10, r10, r12 *)
  0xe0022006; (* and r2, r2, r6 *)
  0xe020c9e6; (* eor r12, r0, r6, ror #19 *)
  0xe02a05ea; (* eor r0, r10, r10, ror #11 *)
  0xe0222008; (* eor r2, r2, r8 *)
  0xe089936c; (* add r9, r9, r12, ror #6 *)
  0xe02ac00b; (* eor r12, r10, r11 *)
  0xe0200a6a; (* eor r0, r0, r10, ror #20 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe59d200c; (* ldr r2, [sp, #0xc] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0855009; (* add r5, r5, r9 *)
  0xe0899160; (* add r9, r9, r0, ror #2 *)
  0xe023300b; (* eor r3, r3, r11 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe0262007; (* eor r2, r6, r7 *)
  0xe02502e5; (* eor r0, r5, r5, ror #5 *)
  0xe0899003; (* add r9, r9, r3 *)
  0xe0022005; (* and r2, r2, r5 *)
  0xe02039e5; (* eor r3, r0, r5, ror #19 *)
  0xe02905e9; (* eor r0, r9, r9, ror #11 *)
  0xe0222007; (* eor r2, r2, r7 *)
  0xe0888363; (* add r8, r8, r3, ror #6 *)
  0xe029300a; (* eor r3, r9, r10 *)
  0xe0200a69; (* eor r0, r0, r9, ror #20 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe59d2010; (* ldr r2, [sp, #0x10] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0844008; (* add r4, r4, r8 *)
  0xe0888160; (* add r8, r8, r0, ror #2 *)
  0xe02cc00a; (* eor r12, r12, r10 *)
  0xf4410aad; (* vst1.32 {d16, d17}, [r1:128]! *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe0252006; (* eor r2, r5, r6 *)
  0xe02402e4; (* eor r0, r4, r4, ror #5 *)
  0xe088800c; (* add r8, r8, r12 *)
  0xf46e0aad; (* vld1.32 {d16, d17}, [lr:128]! *)
  0xe0022004; (* and r2, r2, r4 *)
  0xe020c9e4; (* eor r12, r0, r4, ror #19 *)
  0xe02805e8; (* eor r0, r8, r8, ror #11 *)
  0xe0222006; (* eor r2, r2, r6 *)
  0xf3b020c2; (* vrev32.8 q1, q1 *)
  0xe087736c; (* add r7, r7, r12, ror #6 *)
  0xe028c009; (* eor r12, r8, r9 *)
  0xe0200a68; (* eor r0, r0, r8, ror #20 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xf26008c2; (* vadd.i32 q8, q8, q1 *)
  0xe59d2014; (* ldr r2, [sp, #0x14] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe08bb007; (* add r11, r11, r7 *)
  0xe0877160; (* add r7, r7, r0, ror #2 *)
  0xe0233009; (* eor r3, r3, r9 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe0242005; (* eor r2, r4, r5 *)
  0xe02b02eb; (* eor r0, r11, r11, ror #5 *)
  0xe0877003; (* add r7, r7, r3 *)
  0xe002200b; (* and r2, r2, r11 *)
  0xe02039eb; (* eor r3, r0, r11, ror #19 *)
  0xe02705e7; (* eor r0, r7, r7, ror #11 *)
  0xe0222005; (* eor r2, r2, r5 *)
  0xe0866363; (* add r6, r6, r3, ror #6 *)
  0xe0273008; (* eor r3, r7, r8 *)
  0xe0200a67; (* eor r0, r0, r7, ror #20 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe59d2018; (* ldr r2, [sp, #0x18] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe08aa006; (* add r10, r10, r6 *)
  0xe0866160; (* add r6, r6, r0, ror #2 *)
  0xe02cc008; (* eor r12, r12, r8 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe02b2004; (* eor r2, r11, r4 *)
  0xe02a02ea; (* eor r0, r10, r10, ror #5 *)
  0xe086600c; (* add r6, r6, r12 *)
  0xe002200a; (* and r2, r2, r10 *)
  0xe020c9ea; (* eor r12, r0, r10, ror #19 *)
  0xe02605e6; (* eor r0, r6, r6, ror #11 *)
  0xe0222004; (* eor r2, r2, r4 *)
  0xe085536c; (* add r5, r5, r12, ror #6 *)
  0xe026c007; (* eor r12, r6, r7 *)
  0xe0200a66; (* eor r0, r0, r6, ror #20 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe59d201c; (* ldr r2, [sp, #0x1c] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0899005; (* add r9, r9, r5 *)
  0xe0855160; (* add r5, r5, r0, ror #2 *)
  0xe0233007; (* eor r3, r3, r7 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe02a200b; (* eor r2, r10, r11 *)
  0xe02902e9; (* eor r0, r9, r9, ror #5 *)
  0xe0855003; (* add r5, r5, r3 *)
  0xe0022009; (* and r2, r2, r9 *)
  0xe02039e9; (* eor r3, r0, r9, ror #19 *)
  0xe02505e5; (* eor r0, r5, r5, ror #11 *)
  0xe022200b; (* eor r2, r2, r11 *)
  0xe0844363; (* add r4, r4, r3, ror #6 *)
  0xe0253006; (* eor r3, r5, r6 *)
  0xe0200a65; (* eor r0, r0, r5, ror #20 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe59d2020; (* ldr r2, [sp, #0x20] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0888004; (* add r8, r8, r4 *)
  0xe0844160; (* add r4, r4, r0, ror #2 *)
  0xe02cc006; (* eor r12, r12, r6 *)
  0xf4410aad; (* vst1.32 {d16, d17}, [r1:128]! *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xe029200a; (* eor r2, r9, r10 *)
  0xe02802e8; (* eor r0, r8, r8, ror #5 *)
  0xe084400c; (* add r4, r4, r12 *)
  0xf46e0aad; (* vld1.32 {d16, d17}, [lr:128]! *)
  0xe0022008; (* and r2, r2, r8 *)
  0xe020c9e8; (* eor r12, r0, r8, ror #19 *)
  0xe02405e4; (* eor r0, r4, r4, ror #11 *)
  0xe022200a; (* eor r2, r2, r10 *)
  0xf3b040c4; (* vrev32.8 q2, q2 *)
  0xe08bb36c; (* add r11, r11, r12, ror #6 *)
  0xe024c005; (* eor r12, r4, r5 *)
  0xe0200a64; (* eor r0, r0, r4, ror #20 *)
  0xe08bb002; (* add r11, r11, r2 *)
  0xf26008c4; (* vadd.i32 q8, q8, q2 *)
  0xe59d2024; (* ldr r2, [sp, #0x24] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe087700b; (* add r7, r7, r11 *)
  0xe08bb160; (* add r11, r11, r0, ror #2 *)
  0xe0233005; (* eor r3, r3, r5 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe0282009; (* eor r2, r8, r9 *)
  0xe02702e7; (* eor r0, r7, r7, ror #5 *)
  0xe08bb003; (* add r11, r11, r3 *)
  0xe0022007; (* and r2, r2, r7 *)
  0xe02039e7; (* eor r3, r0, r7, ror #19 *)
  0xe02b05eb; (* eor r0, r11, r11, ror #11 *)
  0xe0222009; (* eor r2, r2, r9 *)
  0xe08aa363; (* add r10, r10, r3, ror #6 *)
  0xe02b3004; (* eor r3, r11, r4 *)
  0xe0200a6b; (* eor r0, r0, r11, ror #20 *)
  0xe08aa002; (* add r10, r10, r2 *)
  0xe59d2028; (* ldr r2, [sp, #0x28] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe086600a; (* add r6, r6, r10 *)
  0xe08aa160; (* add r10, r10, r0, ror #2 *)
  0xe02cc004; (* eor r12, r12, r4 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe0272008; (* eor r2, r7, r8 *)
  0xe02602e6; (* eor r0, r6, r6, ror #5 *)
  0xe08aa00c; (* add r10, r10, r12 *)
  0xe0022006; (* and r2, r2, r6 *)
  0xe020c9e6; (* eor r12, r0, r6, ror #19 *)
  0xe02a05ea; (* eor r0, r10, r10, ror #11 *)
  0xe0222008; (* eor r2, r2, r8 *)
  0xe089936c; (* add r9, r9, r12, ror #6 *)
  0xe02ac00b; (* eor r12, r10, r11 *)
  0xe0200a6a; (* eor r0, r0, r10, ror #20 *)
  0xe0899002; (* add r9, r9, r2 *)
  0xe59d202c; (* ldr r2, [sp, #0x2c] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0855009; (* add r5, r5, r9 *)
  0xe0899160; (* add r9, r9, r0, ror #2 *)
  0xe023300b; (* eor r3, r3, r11 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe0262007; (* eor r2, r6, r7 *)
  0xe02502e5; (* eor r0, r5, r5, ror #5 *)
  0xe0899003; (* add r9, r9, r3 *)
  0xe0022005; (* and r2, r2, r5 *)
  0xe02039e5; (* eor r3, r0, r5, ror #19 *)
  0xe02905e9; (* eor r0, r9, r9, ror #11 *)
  0xe0222007; (* eor r2, r2, r7 *)
  0xe0888363; (* add r8, r8, r3, ror #6 *)
  0xe029300a; (* eor r3, r9, r10 *)
  0xe0200a69; (* eor r0, r0, r9, ror #20 *)
  0xe0888002; (* add r8, r8, r2 *)
  0xe59d2030; (* ldr r2, [sp, #0x30] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0844008; (* add r4, r4, r8 *)
  0xe0888160; (* add r8, r8, r0, ror #2 *)
  0xe02cc00a; (* eor r12, r12, r10 *)
  0xf4410aad; (* vst1.32 {d16, d17}, [r1:128]! *)
  0xe0877002; (* add r7, r7, r2 *)
  0xe0252006; (* eor r2, r5, r6 *)
  0xe02402e4; (* eor r0, r4, r4, ror #5 *)
  0xe088800c; (* add r8, r8, r12 *)
  0xf46e0aad; (* vld1.32 {d16, d17}, [lr:128]! *)
  0xe0022004; (* and r2, r2, r4 *)
  0xe020c9e4; (* eor r12, r0, r4, ror #19 *)
  0xe02805e8; (* eor r0, r8, r8, ror #11 *)
  0xe0222006; (* eor r2, r2, r6 *)
  0xf3b060c6; (* vrev32.8 q3, q3 *)
  0xe087736c; (* add r7, r7, r12, ror #6 *)
  0xe028c009; (* eor r12, r8, r9 *)
  0xe0200a68; (* eor r0, r0, r8, ror #20 *)
  0xe0877002; (* add r7, r7, r2 *)
  0xf26008c6; (* vadd.i32 q8, q8, q3 *)
  0xe59d2034; (* ldr r2, [sp, #0x34] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe08bb007; (* add r11, r11, r7 *)
  0xe0877160; (* add r7, r7, r0, ror #2 *)
  0xe0233009; (* eor r3, r3, r9 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe0242005; (* eor r2, r4, r5 *)
  0xe02b02eb; (* eor r0, r11, r11, ror #5 *)
  0xe0877003; (* add r7, r7, r3 *)
  0xe002200b; (* and r2, r2, r11 *)
  0xe02039eb; (* eor r3, r0, r11, ror #19 *)
  0xe02705e7; (* eor r0, r7, r7, ror #11 *)
  0xe0222005; (* eor r2, r2, r5 *)
  0xe0866363; (* add r6, r6, r3, ror #6 *)
  0xe0273008; (* eor r3, r7, r8 *)
  0xe0200a67; (* eor r0, r0, r7, ror #20 *)
  0xe0866002; (* add r6, r6, r2 *)
  0xe59d2038; (* ldr r2, [sp, #0x38] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe08aa006; (* add r10, r10, r6 *)
  0xe0866160; (* add r6, r6, r0, ror #2 *)
  0xe02cc008; (* eor r12, r12, r8 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe02b2004; (* eor r2, r11, r4 *)
  0xe02a02ea; (* eor r0, r10, r10, ror #5 *)
  0xe086600c; (* add r6, r6, r12 *)
  0xe002200a; (* and r2, r2, r10 *)
  0xe020c9ea; (* eor r12, r0, r10, ror #19 *)
  0xe02605e6; (* eor r0, r6, r6, ror #11 *)
  0xe0222004; (* eor r2, r2, r4 *)
  0xe085536c; (* add r5, r5, r12, ror #6 *)
  0xe026c007; (* eor r12, r6, r7 *)
  0xe0200a66; (* eor r0, r0, r6, ror #20 *)
  0xe0855002; (* add r5, r5, r2 *)
  0xe59d203c; (* ldr r2, [sp, #0x3c] *)
  0xe003300c; (* and r3, r3, r12 *)
  0xe0899005; (* add r9, r9, r5 *)
  0xe0855160; (* add r5, r5, r0, ror #2 *)
  0xe0233007; (* eor r3, r3, r7 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe02a200b; (* eor r2, r10, r11 *)
  0xe02902e9; (* eor r0, r9, r9, ror #5 *)
  0xe0855003; (* add r5, r5, r3 *)
  0xe0022009; (* and r2, r2, r9 *)
  0xe02039e9; (* eor r3, r0, r9, ror #19 *)
  0xe02505e5; (* eor r0, r5, r5, ror #11 *)
  0xe022200b; (* eor r2, r2, r11 *)
  0xe0844363; (* add r4, r4, r3, ror #6 *)
  0xe0253006; (* eor r3, r5, r6 *)
  0xe0200a65; (* eor r0, r0, r5, ror #20 *)
  0xe0844002; (* add r4, r4, r2 *)
  0xe59d2040; (* ldr r2, [sp, #0x40] *)
  0xe00cc003; (* and r12, r12, r3 *)
  0xe0888004; (* add r8, r8, r4 *)
  0xe0844160; (* add r4, r4, r0, ror #2 *)
  0xe02cc006; (* eor r12, r12, r6 *)
  0xf4410aad; (* vst1.32 {d16, d17}, [r1:128]! *)
  0xe5920000; (* ldr r0, [r2] *)
  0xe084400c; (* add r4, r4, r12 *)
  0xe592c004; (* ldr r12, [r2, #0x4] *)
  0xe5923008; (* ldr r3, [r2, #0x8] *)
  0xe592100c; (* ldr r1, [r2, #0xc] *)
  0xe0844000; (* add r4, r4, r0 *)
  0xe5920010; (* ldr r0, [r2, #0x10] *)
  0xe085500c; (* add r5, r5, r12 *)
  0xe592c014; (* ldr r12, [r2, #0x14] *)
  0xe0866003; (* add r6, r6, r3 *)
  0xe5923018; (* ldr r3, [r2, #0x18] *)
  0xe0877001; (* add r7, r7, r1 *)
  0xe592101c; (* ldr r1, [r2, #0x1c] *)
  0xe0888000; (* add r8, r8, r0 *)
  0xe4824004; (* str r4, [r2], #4 *)
  0xe089900c; (* add r9, r9, r12 *)
  0xe4825004; (* str r5, [r2], #4 *)
  0xe08aa003; (* add r10, r10, r3 *)
  0xe4826004; (* str r6, [r2], #4 *)
  0xe08bb001; (* add r11, r11, r1 *)
  0xe4827004; (* str r7, [r2], #4 *)
  0xe8820f00; (* stm r2, {r8, r9, r10, r11} *)
  0x11a0100d; (* movne r1, sp *)
  0x159d2000; (* ldrne r2, [sp] *)
  0x102cc00c; (* eorne r12, r12, r12 *)
  0x059dd04c; (* ldreq sp, [sp, #0x4c] *)
  0x10253006; (* eorne r3, r5, r6 *)
  0x1afffd2c; (* bne 0x3050 *)
  0xe8bd9ff0; (* pop {r4, r5, r6, r7, r8, r9, r10, r11, r12, pc} *)
  0xffffe4d4; (* data *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe51f3028; (* ldr r3, [pc, #-0x28] *)
  0xe08f3003; (* add r3, pc, r3 *)
  0xf420028f; (* vld1.32 {d0, d1, d2, d3}, [r0] *)
  0xe0812302; (* add r2, r1, r2, lsl #6 *)
  0xea000002; (* b 0x3be0 *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xe320f000; (* nop *)
  0xf461020d; (* vld1.8 {d16, d17, d18, d19}, [r1]! *)
  0xf461420d; (* vld1.8 {d20, d21, d22, d23}, [r1]! *)
  0xf4638a8d; (* vld1.32 {d24, d25}, [r3]! *)
  0xf3f000e0; (* vrev32.8 q8, q8 *)
  0xf3f020e2; (* vrev32.8 q9, q9 *)
  0xf3f040e4; (* vrev32.8 q10, q10 *)
  0xf3f060e6; (* vrev32.8 q11, q11 *)
  0xf260c150; (* vorr q14, q0, q0 *)
  0xf262e152; (* vorr q15, q1, q1 *)
  0xe1310002; (* teq r1, r2 *)
  0xf463aa8d; (* vld1.32 {d26, d27}, [r3]! *)
  0xf26888e0; (* vadd.i32 q12, q12, q8 *)
  0xf3fa03e2; (* sha256su0.32 q8, q9 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c68; (* sha256h.32 q0, q1, q12 *)
  0xf3142c68; (* sha256h2.32 q1, q2, q12 *)
  0xf3640ce6; (* sha256su1.32 q8, q10, q11 *)
  0xf4638a8d; (* vld1.32 {d24, d25}, [r3]! *)
  0xf26aa8e2; (* vadd.i32 q13, q13, q9 *)
  0xf3fa23e4; (* sha256su0.32 q9, q10 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c6a; (* sha256h.32 q0, q1, q13 *)
  0xf3142c6a; (* sha256h2.32 q1, q2, q13 *)
  0xf3662ce0; (* sha256su1.32 q9, q11, q8 *)
  0xf463aa8d; (* vld1.32 {d26, d27}, [r3]! *)
  0xf26888e4; (* vadd.i32 q12, q12, q10 *)
  0xf3fa43e6; (* sha256su0.32 q10, q11 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c68; (* sha256h.32 q0, q1, q12 *)
  0xf3142c68; (* sha256h2.32 q1, q2, q12 *)
  0xf3604ce2; (* sha256su1.32 q10, q8, q9 *)
  0xf4638a8d; (* vld1.32 {d24, d25}, [r3]! *)
  0xf26aa8e6; (* vadd.i32 q13, q13, q11 *)
  0xf3fa63e0; (* sha256su0.32 q11, q8 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c6a; (* sha256h.32 q0, q1, q13 *)
  0xf3142c6a; (* sha256h2.32 q1, q2, q13 *)
  0xf3626ce4; (* sha256su1.32 q11, q9, q10 *)
  0xf463aa8d; (* vld1.32 {d26, d27}, [r3]! *)
  0xf26888e0; (* vadd.i32 q12, q12, q8 *)
  0xf3fa03e2; (* sha256su0.32 q8, q9 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c68; (* sha256h.32 q0, q1, q12 *)
  0xf3142c68; (* sha256h2.32 q1, q2, q12 *)
  0xf3640ce6; (* sha256su1.32 q8, q10, q11 *)
  0xf4638a8d; (* vld1.32 {d24, d25}, [r3]! *)
  0xf26aa8e2; (* vadd.i32 q13, q13, q9 *)
  0xf3fa23e4; (* sha256su0.32 q9, q10 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c6a; (* sha256h.32 q0, q1, q13 *)
  0xf3142c6a; (* sha256h2.32 q1, q2, q13 *)
  0xf3662ce0; (* sha256su1.32 q9, q11, q8 *)
  0xf463aa8d; (* vld1.32 {d26, d27}, [r3]! *)
  0xf26888e4; (* vadd.i32 q12, q12, q10 *)
  0xf3fa43e6; (* sha256su0.32 q10, q11 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c68; (* sha256h.32 q0, q1, q12 *)
  0xf3142c68; (* sha256h2.32 q1, q2, q12 *)
  0xf3604ce2; (* sha256su1.32 q10, q8, q9 *)
  0xf4638a8d; (* vld1.32 {d24, d25}, [r3]! *)
  0xf26aa8e6; (* vadd.i32 q13, q13, q11 *)
  0xf3fa63e0; (* sha256su0.32 q11, q8 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c6a; (* sha256h.32 q0, q1, q13 *)
  0xf3142c6a; (* sha256h2.32 q1, q2, q13 *)
  0xf3626ce4; (* sha256su1.32 q11, q9, q10 *)
  0xf463aa8d; (* vld1.32 {d26, d27}, [r3]! *)
  0xf26888e0; (* vadd.i32 q12, q12, q8 *)
  0xf3fa03e2; (* sha256su0.32 q8, q9 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c68; (* sha256h.32 q0, q1, q12 *)
  0xf3142c68; (* sha256h2.32 q1, q2, q12 *)
  0xf3640ce6; (* sha256su1.32 q8, q10, q11 *)
  0xf4638a8d; (* vld1.32 {d24, d25}, [r3]! *)
  0xf26aa8e2; (* vadd.i32 q13, q13, q9 *)
  0xf3fa23e4; (* sha256su0.32 q9, q10 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c6a; (* sha256h.32 q0, q1, q13 *)
  0xf3142c6a; (* sha256h2.32 q1, q2, q13 *)
  0xf3662ce0; (* sha256su1.32 q9, q11, q8 *)
  0xf463aa8d; (* vld1.32 {d26, d27}, [r3]! *)
  0xf26888e4; (* vadd.i32 q12, q12, q10 *)
  0xf3fa43e6; (* sha256su0.32 q10, q11 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c68; (* sha256h.32 q0, q1, q12 *)
  0xf3142c68; (* sha256h2.32 q1, q2, q12 *)
  0xf3604ce2; (* sha256su1.32 q10, q8, q9 *)
  0xf4638a8d; (* vld1.32 {d24, d25}, [r3]! *)
  0xf26aa8e6; (* vadd.i32 q13, q13, q11 *)
  0xf3fa63e0; (* sha256su0.32 q11, q8 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c6a; (* sha256h.32 q0, q1, q13 *)
  0xf3142c6a; (* sha256h2.32 q1, q2, q13 *)
  0xf3626ce4; (* sha256su1.32 q11, q9, q10 *)
  0xf463aa8d; (* vld1.32 {d26, d27}, [r3]! *)
  0xf26888e0; (* vadd.i32 q12, q12, q8 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c68; (* sha256h.32 q0, q1, q12 *)
  0xf3142c68; (* sha256h2.32 q1, q2, q12 *)
  0xf4638a8d; (* vld1.32 {d24, d25}, [r3]! *)
  0xf26aa8e2; (* vadd.i32 q13, q13, q9 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c6a; (* sha256h.32 q0, q1, q13 *)
  0xf3142c6a; (* sha256h2.32 q1, q2, q13 *)
  0xf463aa8f; (* vld1.32 {d26, d27}, [r3] *)
  0xf26888e4; (* vadd.i32 q12, q12, q10 *)
  0xe24330f0; (* sub r3, r3, #240 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c68; (* sha256h.32 q0, q1, q12 *)
  0xf3142c68; (* sha256h2.32 q1, q2, q12 *)
  0xf26aa8e6; (* vadd.i32 q13, q13, q11 *)
  0xf2204150; (* vorr q2, q0, q0 *)
  0xf3020c6a; (* sha256h.32 q0, q1, q13 *)
  0xf3142c6a; (* sha256h2.32 q1, q2, q13 *)
  0xf220086c; (* vadd.i32 q0, q0, q14 *)
  0xf222286e; (* vadd.i32 q1, q1, q15 *)
  0x1affff8a; (* bne 0x3be0 *)
  0xf400028f; (* vst1.32 {d0, d1, d2, d3}, [r0] *)
  0xe12fff1e  (* bx lr *)
];;

let SHA256_ARMV4_EXEC = AARCH32_MK_EXEC_RULE sha256_armv4_mc;;

(* admin/prove writes sha256_block_data_order_hw's offset from K256 in rind's
   build to armv7/sha256_armv4.offset, and this fails unless it is 0x1b20,
   the entry the theorems take, so the symbol rind calls is the code they
   are about. *)
let () =
  let offset =
    int_of_string (String.trim (Bytes.to_string
                                 (load_file "armv7/sha256_armv4.offset"))) in
  if offset <> 0x1b20 then
    failwith ("sha256_armv4: sha256_block_data_order_hw is at " ^
              string_of_int offset ^ ", not 0x1b20");;

(* ------------------------------------------------------------------------- *)
(* Reading the code's own words: the literal and K256.                       *)
(* ------------------------------------------------------------------------- *)

let SHA256_READ_BYTELIST_EQ_BYTES = prove
 (`!(x:int32) l k (s:aarch32state).
        read (memory :> bytelist(x,k)) s = l <=>
        LENGTH l = k /\
        read (memory :> bytes(x,k)) s = num_of_bytelist l`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist; through; read] THEN
  MESON_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; BYTELIST_OF_NUM_OF_BYTELIST;
            READ_BYTES_BOUND_ALT; LENGTH_BYTELIST_OF_NUM]);;

let SHA256_LOADED_BYTES32 = prove
 (`!(s:aarch32state) (a:int32) b0 b1 b2 b3.
     bytes_loaded s a [b0;b1;b2;b3]
     ==> read (memory :> bytes32 a) s = word(num_of_bytelist [b0;b1;b2;b3])`,
  REWRITE_TAC[bytes_loaded; SHA256_READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[bytes32; asword; READ_COMPONENT_COMPOSE; through; read] THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN SIMP_TAC[]);;

let SHA256_LOADED_BYTES64 = prove
 (`!(s:aarch32state) (a:int32) b0 b1 b2 b3 b4 b5 b6 b7.
     bytes_loaded s a [b0;b1;b2;b3;b4;b5;b6;b7]
     ==> read (memory :> bytes64 a) s =
         word(num_of_bytelist [b0;b1;b2;b3;b4;b5;b6;b7])`,
  REWRITE_TAC[bytes_loaded; SHA256_READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[bytes64; asword; READ_COMPONENT_COMPOSE; through; read] THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN SIMP_TAC[]);;

(* SHA256_ARMV4_READ_RULE n off: the n-bit word the code holds at pc + off,
   `aligned_bytes_loaded s (word pc) sha256_armv4_mc ==>
    read (memory :> bytesn (word (pc + off))) s = word v`. *)
let SHA256_ARMV4_READ_RULE =
  let mc_th = sha256_armv4_mc in
  fun n off ->
    let th = SPECL [`s:aarch32state`; `word pc:int32`; `sha256_armv4_mc`;
                    mk_small_numeral off; mk_small_numeral (n / 8)]
               aligned_bytes_loaded_sub_list in
    let th = CONV_RULE (LAND_CONV (RAND_CONV DIVIDES_CONV) THENC
               RAND_CONV (RAND_CONV (REWRITE_CONV[mc_th] THENC SUB_LIST_CONV) THENC
                          REWR_CONV aligned_bytes_loaded)) th in
    let th = MATCH_MP (if n = 32 then SHA256_LOADED_BYTES32 else SHA256_LOADED_BYTES64)
                      (CONJUNCT2 (UNDISCH (REWRITE_RULE[] th))) in
    let th = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV[num_of_bytelist] THENC
                                              DEPTH_CONV WORD_NUM_RED_CONV THENC
                                              NUM_REDUCE_CONV))) th in
    let th = REWRITE_RULE[GSYM WORD_ADD; ADD_CLAUSES] th in
    GEN_ALL (DISCH_ALL th);;

(* ------------------------------------------------------------------------- *)
(* The crypto extension's SHA-256 steps as FIPS 180-4's rounds and schedule. *)
(* ------------------------------------------------------------------------- *)

(* Four words as a Q register holds them, the first in its lowest lane. *)
let sha256_quad = new_definition
 `sha256_quad (a:int32) (b:int32) (c:int32) (d:int32) : int128 =
    word_join (word_join d c:int64) (word_join b a:int64)`;;

(* A state's halves as SHA256H and SHA256H2 take them. *)
let sha256_abcd = new_definition
 `sha256_abcd (l:int32 list) = sha256_quad (EL 0 l) (EL 1 l) (EL 2 l) (EL 3 l)`;;

let sha256_efgh = new_definition
 `sha256_efgh (l:int32 list) = sha256_quad (EL 4 l) (EL 5 l) (EL 6 l) (EL 7 l)`;;

let SHA256_QUAD_SUBWORDS = prove
 (`!a b c d:int32.
     word_subword (sha256_quad a b c d) (0,32) = a /\
     word_subword (sha256_quad a b c d) (32,32) = b /\
     word_subword (sha256_quad a b c d) (64,32) = c /\
     word_subword (sha256_quad a b c d) (96,32) = d /\
     word_subword (sha256_quad a b c d) (0,64):int64 = word_join b a /\
     word_subword (sha256_quad a b c d) (64,64):int64 = word_join d c`,
  REWRITE_TAC[sha256_quad] THEN CONV_TAC WORD_BLAST);;

(* Proves a goal that joins the same 32-bit sums on both sides in different
   shapes: each sum becomes a variable, the largest first, and WORD_BLAST
   matches up the lanes. *)
let SHA256_LANES_TAC =
  let is_sum t =
    match t with
      Comb(Comb(Const("word_add",_),_),_) -> type_of t = `:int32`
    | _ -> false
  and size t = String.length(string_of_term t) in
  REPEAT GEN_TAC THEN
  W(fun (_,w) ->
     let ts = setify(find_terms is_sum w) in
     let rec go ts =
       match ts with
         [] -> ALL_TAC
       | t::rest ->
           W(fun (_,w) -> if free_in t w then SPEC_TAC(t,genvar(type_of t))
                          else ALL_TAC) THEN go rest in
     go (rev (sort (fun t u -> size t <= size u) ts))) THEN
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST;;

(* One step of SHA256hash on quads, its round constant and schedule word in
   lane i of the third operand: a FIPS 180-4 round, ABCD on top. *)
let SHA256HASH_LOOP_ROUND = prove
 (`!a b c d e f g h k0 w0 k1 w1 k2 w2 k3 w3.
     let wq = sha256_quad (word_add k0 w0) (word_add k1 w1)
                          (word_add k2 w2) (word_add k3 w3) in
     let l = [a;b;c;d;e;f;g;h] in
     sha256hash_loop 0 (sha256_quad a b c d) (sha256_quad e f g h) wq =
       word_join (sha256_abcd (sha256_round l k0 w0))
                 (sha256_efgh (sha256_round l k0 w0)) /\
     sha256hash_loop 1 (sha256_quad a b c d) (sha256_quad e f g h) wq =
       word_join (sha256_abcd (sha256_round l k1 w1))
                 (sha256_efgh (sha256_round l k1 w1)) /\
     sha256hash_loop 2 (sha256_quad a b c d) (sha256_quad e f g h) wq =
       word_join (sha256_abcd (sha256_round l k2 w2))
                 (sha256_efgh (sha256_round l k2 w2)) /\
     sha256hash_loop 3 (sha256_quad a b c d) (sha256_quad e f g h) wq =
       word_join (sha256_abcd (sha256_round l k3 w3))
                 (sha256_efgh (sha256_round l k3 w3))`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha256hash_loop; elem; sha256_round; sha256_abcd; sha256_efgh] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[SHA256_QUAD_SUBWORDS] THEN REWRITE_TAC[sha256_quad] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD_AC] THEN REPEAT CONJ_TAC THEN SHA256_LANES_TAC);;

(* A round reads only the state's first eight words. *)
let SHA256_ROUND_EL = prove
 (`!l k w. sha256_round l k w =
           sha256_round [EL 0 l; EL 1 l; EL 2 l; EL 3 l;
                         EL 4 l; EL 5 l; EL 6 l; EL 7 l] k w`,
  REWRITE_TAC[sha256_round] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* SHA256H and SHA256H2 on a state's halves are four rounds, each round's
   constant and schedule word summed in a lane of the third operand. *)
let SHA256H_ROUNDS = prove
 (`!l k0 w0 k1 w1 k2 w2 k3 w3.
     let wq = sha256_quad (word_add k0 w0) (word_add k1 w1)
                          (word_add k2 w2) (word_add k3 w3) in
     let l' = sha256_round (sha256_round (sha256_round
                (sha256_round l k0 w0) k1 w1) k2 w2) k3 w3 in
     sha256h (sha256_abcd l) (sha256_efgh l) wq = sha256_abcd l' /\
     sha256h2 (sha256_efgh l) (sha256_abcd l) wq = sha256_efgh l'`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[sha256h; sha256h2; sha256hash] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o TOP_DEPTH_CONV)
    [sha256_abcd; sha256_efgh] THEN
  REPEAT(CHANGED_TAC
   (REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256HASH_LOOP_ROUND] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o TOP_DEPTH_CONV)
      [sha256_abcd; sha256_efgh])) THEN
  REWRITE_TAC[GSYM SHA256_ROUND_EL] THEN REWRITE_TAC[sha256_abcd; sha256_efgh]);;

(* So each SHA256H and SHA256H2 pair is the spec's rounds n to n + 3. *)
let SHA256H_STEP = prove
 (`!m h n.
     let wq = sha256_quad
       (word_add (EL n sha256_constants) (sha256_msg_schedule m n))
       (word_add (EL (n + 1) sha256_constants) (sha256_msg_schedule m (n + 1)))
       (word_add (EL (n + 2) sha256_constants) (sha256_msg_schedule m (n + 2)))
       (word_add (EL (n + 3) sha256_constants) (sha256_msg_schedule m (n + 3))) in
     sha256h (sha256_abcd (sha256_compress_rounds m h n))
             (sha256_efgh (sha256_compress_rounds m h n)) wq =
       sha256_abcd (sha256_compress_rounds m h (n + 4)) /\
     sha256h2 (sha256_efgh (sha256_compress_rounds m h n))
              (sha256_abcd (sha256_compress_rounds m h n)) wq =
       sha256_efgh (sha256_compress_rounds m h (n + 4))`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_RULE `n + 4 = (n + 3) + 1`; ARITH_RULE `n + 3 = (n + 2) + 1`;
              ARITH_RULE `n + 2 = (n + 1) + 1`; sha256_compress_rounds] THEN
  REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256H_ROUNDS]);;

(* SHA256SU0 and SHA256SU1 on quads of schedule words: the first sums each
   word with sigma0 of the next, and the second completes the next four
   words, its top two from its bottom two. *)
let SHA256SU0_QUAD = prove
 (`!w0 w1 w2 w3 w4 w5 w6 w7:int32.
     sha256su0 (sha256_quad w0 w1 w2 w3) (sha256_quad w4 w5 w6 w7) =
     sha256_quad (word_add (sha_msg_sigma_0 w1) w0)
                 (word_add (sha_msg_sigma_0 w2) w1)
                 (word_add (sha_msg_sigma_0 w3) w2)
                 (word_add (sha_msg_sigma_0 w4) w3)`,
  REWRITE_TAC[sha256su0; sha256su0_loop; elem] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[sha256_quad] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM sha_msg_sigma_0] THEN SHA256_LANES_TAC);;

(* Lanes as SHA256SU1 joins them, and quads equal lane by lane. *)
let SHA256_JOIN_QUAD = prove
 (`!a b c d:int32.
     (word_join:int32->96 word->int128) d
       ((word_join:int32->int64->96 word) c (word_join b a)) =
     sha256_quad a b c d`,
  REWRITE_TAC[sha256_quad] THEN CONV_TAC WORD_BLAST);;

let SHA256_QUAD_EQ = prove
 (`!a b c d a' b' c' d'.
     sha256_quad a b c d = sha256_quad a' b' c' d' <=>
     a = a' /\ b = b' /\ c = c' /\ d = d'`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun p ->
    MP_TAC(AP_TERM (subst [p,`p:num#num`] `\q:int128. word_subword q p:int32`) th))
    [`0,32`; `32,32`; `64,32`; `96,32`]) THEN
  REWRITE_TAC[SHA256_QUAD_SUBWORDS] THEN SIMP_TAC[]);;

let SHA256SU1_QUAD = prove
 (`!p0 p1 p2 p3 w8 w9 w10 w11 w12 w13 w14 w15:int32.
     sha256su1 (sha256_quad p0 p1 p2 p3) (sha256_quad w8 w9 w10 w11)
               (sha256_quad w12 w13 w14 w15) =
     let r0 = word_add (sha_msg_sigma_1 w14) (word_add p0 w9)
     and r1 = word_add (sha_msg_sigma_1 w15) (word_add p1 w10) in
     sha256_quad r0 r1 (word_add (sha_msg_sigma_1 r0) (word_add p2 w11))
                       (word_add (sha_msg_sigma_1 r1) (word_add p3 w12))`,
  REPEAT GEN_TAC THEN CONV_TAC(RAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
  REWRITE_TAC[sha256su1; sha256su1_loop0; sha256su1_loop1; elem] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [sha256_quad] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SHA256_JOIN_QUAD; SHA256_QUAD_EQ] THEN
  REWRITE_TAC[GSYM sha_msg_sigma_1] THEN REWRITE_TAC[WORD_ADD_AC]);;

(* Each schedule word as SHA256SU0 and SHA256SU1 sum it. *)
let SHA256_MSG_SCHEDULE_SU = prove
 (`!m t. sha256_msg_schedule m (t + 16) =
         word_add (sha_msg_sigma_1 (sha256_msg_schedule m (t + 14)))
          (word_add (word_add (sha_msg_sigma_0 (sha256_msg_schedule m (t + 1)))
                              (sha256_msg_schedule m t))
                    (sha256_msg_schedule m (t + 9)))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [sha256_msg_schedule] THEN
  REWRITE_TAC[ARITH_RULE `~(t + 16 < 16) /\ (t + 16) - 2 = t + 14 /\
                          (t + 16) - 7 = t + 9 /\ (t + 16) - 15 = t + 1 /\
                          (t + 16) - 16 = t`] THEN
  REWRITE_TAC[WORD_ADD_AC]);;

(* ------------------------------------------------------------------------- *)
(* The loop's inputs: the block, K256, and the state.                        *)
(* ------------------------------------------------------------------------- *)

(* K256's address, as `add r3, pc, r3` adds the literal, -6956, to the pc it
   reads. *)
let SHA256_HW_K256_ADDR = prove
 (`!pc. word_add (word (pc + 6956)) (word 4294960340):int32 = word pc`,
  GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_32; CONG] THEN
  REWRITE_TAC[ARITH_RULE `(pc + 6956) + 4294960340 = 1 * 2 EXP 32 + pc`;
              MOD_MULT_ADD]);;

(* The memory M holds from data n blocks, m 0 to m (n - 1), each word
   big-endian. *)
let sha256_hw_blocks_in = new_definition
 `sha256_hw_blocks_in (data:int32) (n:num) (m:num->int32 list) (M:int32->byte) <=>
    !i j. i < n /\ j < 16
          ==> read (bytes32 (word_add data (word (64 * i + 4 * j)))) M =
              word_bytereverse (EL j (m i))`;;

(* Block i's eight doublewords, as VLD1 reads them. *)
let SHA256_HW_BLOCK_LOADS =
  let blk = `word_add data (word (64 * i)):int32` in
  let br j = mk_comb(`word_bytereverse:int32->int32`,
               mk_comb(mk_comb(`EL:num->int32 list->int32`, mk_small_numeral j),
                       `(m:num->int32 list) i`)) in
  let addr k = if k = 0 then blk else
    mk_comb(mk_comb(`word_add:int32->int32->int32`, blk),
            mk_comb(`word:num->int32`, mk_small_numeral (8 * k))) in
  let fact k =
    mk_eq(vsubst [addr k,`a:int32`] `read (memory :> bytes64 a) (s:aarch32state)`,
          mk_comb(mk_comb(`word_join:int32->int32->int64`, br (2*k+1)), br (2*k))) in
  prove
   (mk_imp(`sha256_hw_blocks_in data n m (read memory (s:aarch32state)) /\ i < n`,
           list_mk_conj(map fact (0--7))),
    REWRITE_TAC[sha256_hw_blocks_in] THEN STRIP_TAC THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT))] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC(map (fun j ->
      REWRITE_RULE[ADD_CLAUSES] (CONV_RULE(DEPTH_CONV NUM_RED_CONV)
        (MP (SPECL [`i:num`; mk_small_numeral j] th)
            (CONJ (ASSUME `i:num < n`) (EQT_ELIM(NUM_LT_CONV
               (mk_binop `(<):num->num->bool` (mk_small_numeral j) `16`)))))))
      (0--15))));;

(* K256's 64 words, as VLD1.32 reads them, two at a time. *)
let SHA256_HW_K_LOADS =
  let kel t = mk_comb(mk_comb(`EL:num->int32 list->int32`, mk_small_numeral t),
                      `sha256_constants`) in
  let addr k = if k = 0 then `word pc:int32` else
    mk_comb(mk_comb(`word_add:int32->int32->int32`, `word pc:int32`),
            mk_comb(`word:num->int32`, mk_small_numeral (8 * k))) in
  let fact k =
    mk_eq(vsubst [addr k,`a:int32`] `read (memory :> bytes64 a) (s:aarch32state)`,
          mk_comb(mk_comb(`word_join:int32->int32->int64`, kel (2*k+1)),
                  kel (2*k))) in
  prove
   (mk_imp(`aligned_bytes_loaded s (word pc) sha256_armv4_mc`,
           list_mk_conj(map fact (0--31))),
    DISCH_TAC THEN
    MAP_EVERY (fun k -> MP_TAC(SPECL [`pc:num`; `s:aarch32state`]
                                 (SHA256_ARMV4_READ_RULE 64 (8 * k)))) (0--31) THEN
    ASM_REWRITE_TAC[WORD_ADD] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[sha256_constants] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
    CONV_TAC WORD_REDUCE_CONV);;

(* The state's eight words as VLD1.32 reads them, two at a time. *)
let SHA256_HW_STATE_LOADS = prove
 (`!(a:int32) s h0 h1 h2 h3 h4 h5 h6 h7.
     read (memory :> bytes32 a) s = h0 /\
     read (memory :> bytes32 (word_add a (word 4))) s = h1 /\
     read (memory :> bytes32 (word_add a (word 8))) s = h2 /\
     read (memory :> bytes32 (word_add a (word 12))) s = h3 /\
     read (memory :> bytes32 (word_add a (word 16))) s = h4 /\
     read (memory :> bytes32 (word_add a (word 20))) s = h5 /\
     read (memory :> bytes32 (word_add a (word 24))) s = h6 /\
     read (memory :> bytes32 (word_add a (word 28))) s = h7
     ==> read (memory :> bytes64 a) s = word_join h1 h0 /\
         read (memory :> bytes64 (word_add a (word 8))) s = word_join h3 h2 /\
         read (memory :> bytes64 (word_add a (word 16))) s = word_join h5 h4 /\
         read (memory :> bytes64 (word_add a (word 24))) s = word_join h7 h6`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT))] THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]);;

(* And as VST1.32's doublewords leave them. *)
let SHA256_HW_STATE_STORED = prove
 (`!(a:int32) s x.
     read (memory :> bytes64 a) s = x
     ==> read (memory :> bytes32 a) s = word_subword x (0,32) /\
         read (memory :> bytes32 (word_add a (word 4))) s = word_subword x (32,32)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT))] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Stepping, with each Q register kept as a sha256_quad of the spec.         *)
(* ------------------------------------------------------------------------- *)

(* VREV32.8 of a big-endian word gives it back. *)
let SHA256_REV_BYTEREVERSE = prove
 (`!x:int32. word_reversefields 8 (word_bytereverse x) = x`,
  GEN_TAC THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_REVERSEFIELDS; DIMINDEX_32] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* The block's words, the schedule's first sixteen, of the message w. *)
let SHA256_MSG_SCHEDULE_FIRST = map (fun t ->
    CONV_RULE(RAND_CONV(RATOR_CONV(LAND_CONV NUM_LT_CONV) THENC REWRITE_CONV[]))
      (REWR_CONV sha256_msg_schedule
        (mk_comb(`sha256_msg_schedule w`, mk_small_numeral t))))
  (0--15);;

(* Folds each schedule word, and each four rounds, back into the spec's
   terms, for the message w and the state h the loop body names. *)
let SHA256_HW_FOLD_THS =
  map (fun t -> GSYM(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
         (SPECL [`w:int32 list`; mk_small_numeral t] SHA256_MSG_SCHEDULE_SU)))
      (0--47) @
  flat (map (fun i ->
    let th = CONV_RULE(TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV NUM_ADD_CONV)
      (SPECL [`w:int32 list`; `h:int32 list`; mk_small_numeral(4*i)]
             SHA256H_STEP) in
    CONJUNCTS(if i = 0 then REWRITE_RULE[CONJUNCT1 sha256_compress_rounds] th
              else th))
  (0--15));;

(* The value a step writes to a Q register: its lanes reduced to words
   through the instruction lemmas, then folded back into a sha256_quad of
   the spec's terms. *)
let SHA256_HW_VALUE_CONV =
  TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
  REWRITE_CONV[SHA256_QUAD_SUBWORDS; SHA256SU0_QUAD;
               CONV_RULE(TOP_DEPTH_CONV let_CONV) SHA256SU1_QUAD;
               WORD_OR_REFL] THENC
  REWRITE_CONV[sha256_quad] THENC TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
  REWRITE_CONV([SHA256_REV_BYTEREVERSE; GSYM sha256_quad; SHA256_JOIN_QUAD] @
               SHA256_HW_FOLD_THS);;

let sha256_is_q_fact th =
  try (match lhs(concl th) with
         Comb(Comb(Const("read",_),Const(n,_)),_) ->
           String.length n >= 2 && String.sub n 0 1 = "Q"
       | _ -> false)
  with Failure _ -> false;;

let SHA256_HW_NORM_TAC =
  RULE_ASSUM_TAC(fun th -> if sha256_is_q_fact th then
    CONV_RULE(RAND_CONV SHA256_HW_VALUE_CONV) th else th);;

let SHA256_HW_STEPS_TAC execth ns =
  MAP_EVERY (fun n -> AARCH32_STEPS_TAC execth [n] THEN SHA256_HW_NORM_TAC) ns;;

(* TEQ's flag at the loop's end: whether block i was the last. *)
let SHA256_HW_ZF = prove
 (`!data i n.
     i < n /\ 64 * n < 2 EXP 32
     ==> (val (word_xor (word_add (word_add data (word (64 * i))) (word 64))
                        (word_add data (word (64 * n))):int32) = 0 <=>
          i + 1 = n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN
  REWRITE_TAC[MESON[WORD_RULE `word_sub (word_add (d:int32) a) d = a`]
               `word_add (d:int32) a = word_add d b <=> a = b`] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_32; CONG] THEN
  SUBGOAL_THEN `64 * i + 64 < 2 EXP 32` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

(* One block, from the loop's head to its branch, in the routine's frame. *)
let SHA256_HW_BLOCK_CORRECT = prove
 (`!pc state data n m hh i.
   i < n /\ 64 * n < 2 EXP 32 /\
   aarch32_nowrap (word pc) 0x1d1c /\ aarch32_nowrap data (64 * n)
   ==> ensures aarch32
     (\s. aligned_bytes_loaded s (word pc) sha256_armv4_mc /\
          read PC s = word (pc + 0x1b40) /\
          read R0 s = state /\ read R1 s = word_add data (word (64 * i)) /\
          read R2 s = word_add data (word (64 * n)) /\ read R3 s = word pc /\
          sha256_hw_blocks_in data n m (read memory s) /\
          read Q0 s = sha256_abcd (sha256_hash_blocks m hh i) /\
          read Q1 s = sha256_efgh (sha256_hash_blocks m hh i))
     (\s. aligned_bytes_loaded s (word pc) sha256_armv4_mc /\
          read PC s = word (pc + 0x1d10) /\
          (read R0 s = state /\
           read R1 s = word_add data (word (64 * (i + 1))) /\
           read R2 s = word_add data (word (64 * n)) /\ read R3 s = word pc /\
           sha256_hw_blocks_in data n m (read memory s) /\
           read Q0 s = sha256_abcd (sha256_hash_blocks m hh (i + 1)) /\
           read Q1 s = sha256_efgh (sha256_hash_blocks m hh (i + 1))) /\
          (read ZF s <=> i + 1 = n))
     (MAYCHANGE [PC; R1; R2; R3] ,,
      MAYCHANGE [Q0; Q1; Q2; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(state,32)] ,,
      MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS; fst SHA256_ARMV4_EXEC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[CONJUNCT2 sha256_hash_blocks] THEN
  SUBGOAL_THEN `aarch32_nowrap (word_add data (word (64 * i)):int32) 64`
  ASSUME_TAC THENL
   [MATCH_MP_TAC AARCH32_NOWRAP_OFFSET THEN EXISTS_TAC `64 * n` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add data (word (64 * (i + 1))):int32 =
                word_add (word_add data (word (64 * i))) (word 64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  ABBREV_TAC `blk = word_add data (word (64 * i)):int32` THEN
  ABBREV_TAC `h = sha256_hash_blocks m hh i` THEN
  ABBREV_TAC `w = (m:num->int32 list) i` THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(INST [`s0:aarch32state`,`s:aarch32state`] SHA256_HW_K_LOADS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`s0:aarch32state`,`s:aarch32state`] SHA256_HW_BLOCK_LOADS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC(map GSYM SHA256_MSG_SCHEDULE_FIRST) THEN
  STRIP_TAC THEN
  SHA256_HW_STEPS_TAC SHA256_ARMV4_EXEC (1--116) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "blk" THEN ASM_SIMP_TAC[SHA256_HW_ZF] THEN
  REWRITE_TAC[sha256_abcd; sha256_efgh; SHA256_QUAD_SUBWORDS; sha256_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

(* K256's offset, the literal before the routine, and its shift of the
   block count. *)
let SHA256_HW_LITERAL = SHA256_ARMV4_READ_RULE 32 6912;;

let SHA256_HW_SHL6 = prove
 (`!n. word_shl (word n:int32) 6 = word (64 * n)`,
  GEN_TAC THEN REWRITE_TAC[word_shl; VAL_WORD; DIMINDEX_32; WORD_EQ; CONG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The routine.                                                              *)
(* ------------------------------------------------------------------------- *)

(* From the routine's entry to its `bx lr`. *)
let SHA256_BLOCK_DATA_ORDER_HW_CORRECT = prove
 (`!state data n h0 h1 h2 h3 h4 h5 h6 h7 m pc.
     0 < n /\ 64 * n < 2 EXP 32 /\
     aarch32_nowrap (word pc) 0x1d1c /\ aarch32_nowrap state 32 /\
     aarch32_nowrap data (64 * n) /\
     nonoverlapping (word pc,0x1d1c) (state,32)
     ==> ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) sha256_armv4_mc /\
               read PC s = word (pc + 0x1b20) /\
               C_ARGUMENTS [state; data; word n] s /\
               read (memory :> bytes32 state) s = h0 /\
               read (memory :> bytes32 (word_add state (word 4))) s = h1 /\
               read (memory :> bytes32 (word_add state (word 8))) s = h2 /\
               read (memory :> bytes32 (word_add state (word 12))) s = h3 /\
               read (memory :> bytes32 (word_add state (word 16))) s = h4 /\
               read (memory :> bytes32 (word_add state (word 20))) s = h5 /\
               read (memory :> bytes32 (word_add state (word 24))) s = h6 /\
               read (memory :> bytes32 (word_add state (word 28))) s = h7 /\
               (!i j. i < n /\ j < 16
                      ==> read (memory :> bytes32
                                 (word_add data (word (64 * i + 4 * j)))) s =
                          word_bytereverse (EL j (m i))))
          (\s. read PC s = word (pc + 0x1d18) /\
               let h' = sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] n in
               read (memory :> bytes32 state) s = EL 0 h' /\
               read (memory :> bytes32 (word_add state (word 4))) s = EL 1 h' /\
               read (memory :> bytes32 (word_add state (word 8))) s = EL 2 h' /\
               read (memory :> bytes32 (word_add state (word 12))) s = EL 3 h' /\
               read (memory :> bytes32 (word_add state (word 16))) s = EL 4 h' /\
               read (memory :> bytes32 (word_add state (word 20))) s = EL 5 h' /\
               read (memory :> bytes32 (word_add state (word 24))) s = EL 6 h' /\
               read (memory :> bytes32 (word_add state (word 28))) s = EL 7 h')
          (MAYCHANGE [PC; R1; R2; R3] ,,
           MAYCHANGE [Q0; Q1; Q2; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(state,32)] ,,
           MAYCHANGE [events])`,
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; fst SHA256_ARMV4_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. (!i j. i < n /\ j < 16
               ==> read (memory :> bytes32
                          (word_add data (word (64 * i + 4 * j)))) s =
                   word_bytereverse (EL j (m i))) <=>
        sha256_hw_blocks_in data n m (read memory s)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[sha256_hw_blocks_in; READ_COMPONENT_COMPOSE]; ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `n:num` `pc + 0x1b40` `pc + 0x1d10`
   `\i s. (read R0 s = state /\ read R1 s = word_add data (word (64 * i)) /\
           read R2 s = word_add data (word (64 * n)) /\ read R3 s = word pc /\
           sha256_hw_blocks_in data n m (read memory s) /\
           read Q0 s =
             sha256_abcd (sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i) /\
           read Q1 s =
             sha256_efgh (sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] i)) /\
          (read ZF s <=> i = n)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* There is a block. *)
    ASM_ARITH_TAC;

    (* Into the loop: the state, and K256's address. *)
    ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`state:int32`; `s0:aarch32state`; `h0:int32`; `h1:int32`;
                  `h2:int32`; `h3:int32`; `h4:int32`; `h5:int32`; `h6:int32`;
                  `h7:int32`] SHA256_HW_STATE_LOADS) THEN
    MP_TAC(SPECL [`pc:num`; `s0:aarch32state`] SHA256_HW_LITERAL) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    AARCH32_STEPS_TAC SHA256_ARMV4_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SHA256_HW_SHL6; SHA256_HW_K256_ADDR] THEN
    REWRITE_TAC[CONJUNCT1 sha256_hash_blocks; sha256_abcd; sha256_efgh;
                sha256_quad] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];

    (* A block. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS] SHA256_HW_BLOCK_CORRECT) THEN
    ASM_REWRITE_TAC[];

    (* Back to the head while blocks remain. *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `read ZF (s0:aarch32state) <=> (i:num) = n` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    AARCH32_STEPS_TAC SHA256_ARMV4_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (* Out: the state's store, a doubleword at a time. *)
    ENSURES_INIT_TAC "s0" THEN
    AARCH32_STEPS_TAC SHA256_ARMV4_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SHA256_HW_STATE_STORED o
      check (can (term_match [] `read (memory :> bytes64 a) s = x`) o concl))) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV) o
                   REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[sha256_abcd; sha256_efgh; SHA256_QUAD_SUBWORDS]]);;

let SHA256_BLOCK_DATA_ORDER_HW_SUBROUTINE_CORRECT = prove
 (`!state data n h0 h1 h2 h3 h4 h5 h6 h7 m pc returnaddress.
     0 < n /\ 64 * n < 2 EXP 32 /\
     aarch32_nowrap (word pc) 0x1d1c /\ aarch32_nowrap state 32 /\
     aarch32_nowrap data (64 * n) /\
     nonoverlapping (word pc,0x1d1c) (state,32) /\
     aarch32_bx_target returnaddress
     ==> ensures aarch32
          (\s. aligned_bytes_loaded s (word pc) sha256_armv4_mc /\
               read PC s = word (pc + 0x1b20) /\
               read LR s = returnaddress /\
               C_ARGUMENTS [state; data; word n] s /\
               read (memory :> bytes32 state) s = h0 /\
               read (memory :> bytes32 (word_add state (word 4))) s = h1 /\
               read (memory :> bytes32 (word_add state (word 8))) s = h2 /\
               read (memory :> bytes32 (word_add state (word 12))) s = h3 /\
               read (memory :> bytes32 (word_add state (word 16))) s = h4 /\
               read (memory :> bytes32 (word_add state (word 20))) s = h5 /\
               read (memory :> bytes32 (word_add state (word 24))) s = h6 /\
               read (memory :> bytes32 (word_add state (word 28))) s = h7 /\
               (!i j. i < n /\ j < 16
                      ==> read (memory :> bytes32
                                 (word_add data (word (64 * i + 4 * j)))) s =
                          word_bytereverse (EL j (m i))))
          (\s. read PC s = returnaddress /\
               let h' = sha256_hash_blocks m [h0;h1;h2;h3;h4;h5;h6;h7] n in
               read (memory :> bytes32 state) s = EL 0 h' /\
               read (memory :> bytes32 (word_add state (word 4))) s = EL 1 h' /\
               read (memory :> bytes32 (word_add state (word 8))) s = EL 2 h' /\
               read (memory :> bytes32 (word_add state (word 12))) s = EL 3 h' /\
               read (memory :> bytes32 (word_add state (word 16))) s = EL 4 h' /\
               read (memory :> bytes32 (word_add state (word 20))) s = EL 5 h' /\
               read (memory :> bytes32 (word_add state (word 24))) s = EL 6 h' /\
               read (memory :> bytes32 (word_add state (word 28))) s = EL 7 h')
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(state,32)])`,
  REWRITE_TAC[fst SHA256_ARMV4_EXEC] THEN
  AARCH32_ADD_RETURN_NOSTACK_TAC SHA256_ARMV4_EXEC
    (REWRITE_RULE[fst SHA256_ARMV4_EXEC] SHA256_BLOCK_DATA_ORDER_HW_CORRECT));;
