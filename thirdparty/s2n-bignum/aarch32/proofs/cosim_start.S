/*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/* The machine side of the AArch32 cosimulation executor, which runs as a
 * static Linux program, on an Armv7-A CPU with the crypto extension or under
 * qemu-arm. `cosim_enter` loads D0-D31 from `cosim_qregs` and R0-R12, LR,
 * APSR, and SP from `cosim_state`, runs the one A32 instruction in
 * `cosim_slot`, and stores the state it reaches back to both, with how far
 * from the instruction it landed: 4 when it falls through, or -8, -4, 8, 12,
 * or 16 when it branches to one of the slots around it, the first two a
 * backward branch's, or 21 when it interworks to the T32 slot at 20, the
 * model's PC for that slot with the T bit set. It keeps D8-D15, which the
 * AAPCS has a callee keep. The section is writable, since `cosim_runner.c`
 * writes each instruction into the slot, and the scratch buffer and the
 * state follow the code in the next page, so a store to them never touches a
 * page that holds code. The buffer comes early there, which puts its first
 * words in reach of a literal load, at 32 bytes, which aligns it for any
 * Advanced SIMD alignment qualifier. */

	.syntax unified
	.arm
	.fpu	neon

	.section .text._start,"ax",%progbits
	.global _start
	.type _start, %function
_start:
	bl	cosim_main
	mov	r7, #248		@ exit_group
	svc	#0

	.section .cosim,"awx",%progbits
	.p2align 12
	.global cosim_enter
	.type cosim_enter, %function
cosim_enter:
	push	{r4-r11, lr}
	vpush	{d8-d15}
	str	sp, host_sp
	ldr	r0, =cosim_qregs
	vldmia	r0!, {d0-d15}
	vldmia	r0, {d16-d31}
	ldr	r0, =cosim_state
	ldr	r1, [r0, #56]
	msr	APSR_nzcvq, r1
	ldr	sp, [r0, #60]
	ldm	r0, {r0-r12, lr}
	b	cosim_slot
	b	landm8
	b	landm4

	.global cosim_slot
cosim_slot:
	.word	0xe1a00000		@ the instruction under test
	b	land4
	b	land8
	b	land12
	b	land16
	.thumb
landt20:			@ the T32 slot, which BX or a load into PC reaches
	bx	pc		@ at its address plus 1, and which goes back to A32
	nop			@ at its address plus 4
	.arm
	str	r0, saved_r0
	mov	r0, #21
	b	landed

land4:	str	r0, saved_r0
	mov	r0, #4
	b	landed
land8:	str	r0, saved_r0
	mov	r0, #8
	b	landed
land12:	str	r0, saved_r0
	mov	r0, #12
	b	landed
land16:	str	r0, saved_r0
	mov	r0, #16
	b	landed
landm8:	str	r0, saved_r0
	mvn	r0, #7			@ -8
	b	landed
landm4:	str	r0, saved_r0
	mvn	r0, #3			@ -4
	b	landed

landed:
	str	r0, landing
	ldr	r0, =cosim_state
	stmib	r0, {r1-r12, lr}
	mrs	r1, APSR
	str	r1, [r0, #56]
	str	sp, [r0, #60]
	ldr	r1, landing
	str	r1, [r0, #64]
	ldr	r1, saved_r0
	str	r1, [r0]
	ldr	r0, =cosim_qregs
	vstmia	r0!, {d0-d15}
	vstmia	r0, {d16-d31}
	ldr	sp, host_sp
	vpop	{d8-d15}
	pop	{r4-r11, pc}
	.ltorg

	.p2align 12
host_sp:
	.word	0
saved_r0:
	.word	0
landing:
	.word	0
	.p2align 5
	.global cosim_scratch
cosim_scratch:			@ what the instruction under test reads and writes
	.space	256
	.global cosim_state
cosim_state:			@ R0-R12, LR, APSR, SP, landing
	.space	68
	.global cosim_qregs
cosim_qregs:			@ Q0-Q15
	.space	256

	.section .note.GNU-stack,"",%progbits
