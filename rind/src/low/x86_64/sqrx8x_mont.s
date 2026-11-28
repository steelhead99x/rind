# Copyright 2005-2016 The OpenSSL Project Authors. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
#
# rind's structured copy of aws-lc's `bn_sqr8x_mont`, from
# crypto/fipsmodule/bn/asm/x86_64-mont.pl at aws-lc
# 5ed12cce0fd4453f2f63300d44325ed14f845d6f, for CPUs with BMI2 and ADX:
# aws-lc's instructions, in the structure of the program
# `proofs/verified-garbage/RindIsa/X86_64/Sqrx8xMont.lean` proves, whose bytes
# `admin/prove lean` checks this assembles to. It always squares by
# `bn_sqrx8x_internal`, so it drops aws-lc's test of its third argument and
# its branch to `bn_sqr8x_internal`, and ignores its third argument. The frame's
# alternative bound, `4096 - 64 + 2 r9`, is `lea` of `r9` twice rather than of
# no base, the same value in as many bytes, which rind's model can encode.
# Instructions aws-lc writes as bytes are spelled out.
	movl	%r9d,%r9d
	movq	%rsp,%rax
.cfi_def_cfa_register	%rax
	pushq	%rbx
.cfi_offset	%rbx,-16
	pushq	%rbp
.cfi_offset	%rbp,-24
	pushq	%r12
.cfi_offset	%r12,-32
	pushq	%r13
.cfi_offset	%r13,-40
	pushq	%r14
.cfi_offset	%r14,-48
	pushq	%r15
.cfi_offset	%r15,-56
	movl	%r9d,%r10d
	shll	$3,%r9d
	shlq	$3+2,%r10
	negq	%r9
	leaq	-64(%rsp,%r9,2),%r11
	movq	%rsp,%rbp
	movq	(%r8),%r8
	subq	%rsi,%r11
	andq	$4095,%r11
	cmpq	%r11,%r10
	jb	1f
	subq	%r11,%rbp
	leaq	-64(%rbp,%r9,2),%rbp
	jmp	2f

	.p2align	5
1:
	leaq	4096-64(%r9,%r9,1),%r10
	leaq	-64(%rbp,%r9,2),%rbp
	subq	%r10,%r11
	movq	$0,%r10
	cmovcq	%r10,%r11
	subq	%r11,%rbp
2:
	andq	$-64,%rbp
	movq	%rsp,%r11
	subq	%rbp,%r11
	andq	$-4096,%r11
	leaq	(%r11,%rbp,1),%rsp
	movq	(%rsp),%r10
	cmpq	%rbp,%rsp
	ja	3f
	jmp	4f

	.p2align	4
3:
	leaq	-4096(%rsp),%rsp
	movq	(%rsp),%r10
	cmpq	%rbp,%rsp
	ja	3b
4:
	movq	%r9,%r10
	negq	%r9
	movq	%r8,32(%rsp)
	movq	%rax,40(%rsp)
.cfi_escape	0x0f,0x05,0x77,0x28,0x06,0x23,0x08
	movq	%rcx,%xmm2
	pxor	%xmm0,%xmm0
	movq	%rdi,%xmm1
	movq	%r10,%xmm3
	movdqu	%xmm0,48(%rsp,%r9,2)
	call	{bn_sqrx8x_internal}
	leaq	(%r8,%rcx,1),%rbx
	movq	%rcx,%r9
	movq	%rcx,%rdx
	movq	%xmm1,%rdi
	sarq	$3+2,%rcx
	jmp	5f

	.p2align	5
5:
	movq	0(%rbx),%r12
	movq	8(%rbx),%r13
	movq	16(%rbx),%r14
	movq	24(%rbx),%r15
	leaq	32(%rbx),%rbx
	sbbq	0(%rbp),%r12
	sbbq	8(%rbp),%r13
	sbbq	16(%rbp),%r14
	sbbq	24(%rbp),%r15
	leaq	32(%rbp),%rbp
	movq	%r12,0(%rdi)
	movq	%r13,8(%rdi)
	movq	%r14,16(%rdi)
	movq	%r15,24(%rdi)
	leaq	32(%rdi),%rdi
	incq	%rcx
	jnz	5b

	sbbq	$0,%rax
	leaq	(%rbx,%r9,1),%rbx
	leaq	(%rdi,%r9,1),%rdi
	movq	%rax,%xmm1
	pxor	%xmm0,%xmm0
	pshufd	$0,%xmm1,%xmm1
	movq	40(%rsp),%rsi
.cfi_def_cfa	%rsi,8
	jmp	6f

	.p2align	5
6:
	movdqa	0(%rbx),%xmm2
	movdqa	16(%rbx),%xmm3
	leaq	32(%rbx),%rbx
	movdqu	0(%rdi),%xmm4
	movdqu	16(%rdi),%xmm5
	leaq	32(%rdi),%rdi
	movdqa	%xmm0,-32(%rbx)
	movdqa	%xmm0,-16(%rbx)
	movdqa	%xmm0,-32(%rbx,%rdx,1)
	movdqa	%xmm0,-16(%rbx,%rdx,1)
	pcmpeqd	%xmm1,%xmm0
	pand	%xmm1,%xmm2
	pand	%xmm1,%xmm3
	pand	%xmm0,%xmm4
	pand	%xmm0,%xmm5
	pxor	%xmm0,%xmm0
	por	%xmm2,%xmm4
	por	%xmm3,%xmm5
	movdqu	%xmm4,-32(%rdi)
	movdqu	%xmm5,-16(%rdi)
	addq	$32,%r9
	jnz	6b

	movq	$1,%rax
	movq	-48(%rsi),%r15
.cfi_restore	%r15
	movq	-40(%rsi),%r14
.cfi_restore	%r14
	movq	-32(%rsi),%r13
.cfi_restore	%r13
	movq	-24(%rsi),%r12
.cfi_restore	%r12
	movq	-16(%rsi),%rbp
.cfi_restore	%rbp
	movq	-8(%rsi),%rbx
.cfi_restore	%rbx
	leaq	(%rsi),%rsp
.cfi_def_cfa_register	%rsp
	.byte	0xf3,0xc3
