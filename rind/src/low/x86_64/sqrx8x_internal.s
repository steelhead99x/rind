# Copyright 2011-2016 The OpenSSL Project Authors. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
#
# rind's structured copy of aws-lc's `bn_sqrx8x_internal`, from
# crypto/fipsmodule/bn/asm/x86_64-mont5.pl at aws-lc
# 5ed12cce0fd4453f2f63300d44325ed14f845d6f: aws-lc's instructions, in the
# structure of the program `proofs/verified-garbage/RindIsa/X86_64/Sqrx8x.lean`
# proves, whose bytes `admin/prove lean` checks this assembles to. Each loop
# tests at its bottom: one that aws-lc leaves from its middle runs its head
# once before it and again at its bottom, and the shift-and-add loop tests
# `rcx` again there by `jrcxz` over a `jmp`. The zeroing loop clears the
# whole product rather than jumping past its first eight words, which the
# squaring writes before it reads. Instructions aws-lc writes as bytes are
# spelled out, and its padding prefixes and NOPs dropped.
	leaq	48+8(%rsp),%rdi
	leaq	(%rsi,%r9,1),%rbp
	movq	%r9,0+8(%rsp)
	movq	%rbp,8+8(%rsp)
	.p2align	5
1:
	movdqa	%xmm0,0(%rdi)
	movdqa	%xmm0,16(%rdi)
	movdqa	%xmm0,32(%rdi)
	movdqa	%xmm0,48(%rdi)
	movdqa	%xmm0,64(%rdi)
	movdqa	%xmm0,80(%rdi)
	movdqa	%xmm0,96(%rdi)
	movdqa	%xmm0,112(%rdi)
	leaq	128(%rdi),%rdi
	subq	$64,%r9
	jnz	1b

	movq	0(%rsi),%rdx

	xorq	%r10,%r10
	xorq	%r11,%r11
	xorq	%r12,%r12
	xorq	%r13,%r13
	xorq	%r14,%r14
	xorq	%r15,%r15
	leaq	48+8(%rsp),%rdi
	xorq	%rbp,%rbp
	mulxq	8(%rsi),%r8,%rax
	adcxq	%r9,%r8
	adoxq	%rax,%r10
	mulxq	16(%rsi),%r9,%rax
	adcxq	%r10,%r9
	adoxq	%rax,%r11
	mulxq	24(%rsi),%r10,%rax
	adcxq	%r11,%r10
	adoxq	%rax,%r12
	mulxq	32(%rsi),%r11,%rax
	adcxq	%r12,%r11
	adoxq	%rax,%r13
	mulxq	40(%rsi),%r12,%rax
	adcxq	%r13,%r12
	adoxq	%rax,%r14
	mulxq	48(%rsi),%r13,%rax
	adcxq	%r14,%r13
	adoxq	%r15,%rax
	mulxq	56(%rsi),%r14,%r15
	movq	8(%rsi),%rdx
	adcxq	%rax,%r14
	adoxq	%rbp,%r15
	adcq	64(%rdi),%r15
	movq	%r8,8(%rdi)
	movq	%r9,16(%rdi)
	sbbq	%rcx,%rcx
	xorq	%rbp,%rbp

	mulxq	16(%rsi),%r8,%rbx
	mulxq	24(%rsi),%r9,%rax
	adcxq	%r10,%r8
	adoxq	%rbx,%r9
	mulxq	32(%rsi),%r10,%rbx
	adcxq	%r11,%r9
	adoxq	%rax,%r10
	mulxq	40(%rsi),%r11,%rax
	adcxq	%r12,%r10
	adoxq	%rbx,%r11
	mulxq	48(%rsi),%r12,%rbx
	adcxq	%r13,%r11
	adoxq	%r14,%r12
	mulxq	56(%rsi),%r13,%r14
	movq	16(%rsi),%rdx
	adcxq	%rax,%r12
	adoxq	%rbx,%r13
	adcxq	%r15,%r13
	adoxq	%rbp,%r14
	adcxq	%rbp,%r14

	movq	%r8,24(%rdi)
	movq	%r9,32(%rdi)

	mulxq	24(%rsi),%r8,%rbx
	mulxq	32(%rsi),%r9,%rax
	adcxq	%r10,%r8
	adoxq	%rbx,%r9
	mulxq	40(%rsi),%r10,%rbx
	adcxq	%r11,%r9
	adoxq	%rax,%r10
	mulxq	48(%rsi),%r11,%rax
	adcxq	%r12,%r10
	adoxq	%r13,%r11
	mulxq	56(%rsi),%r12,%r13
	movq	24(%rsi),%rdx
	adcxq	%rbx,%r11
	adoxq	%rax,%r12
	adcxq	%r14,%r12
	movq	%r8,40(%rdi)
	movq	%r9,48(%rdi)
	mulxq	32(%rsi),%r8,%rax
	adoxq	%rbp,%r13
	adcxq	%rbp,%r13

	mulxq	40(%rsi),%r9,%rbx
	adcxq	%r10,%r8
	adoxq	%rax,%r9
	mulxq	48(%rsi),%r10,%rax
	adcxq	%r11,%r9
	adoxq	%r12,%r10
	mulxq	56(%rsi),%r11,%r12
	movq	32(%rsi),%rdx
	movq	40(%rsi),%r14
	adcxq	%rbx,%r10
	adoxq	%rax,%r11
	movq	48(%rsi),%r15
	adcxq	%r13,%r11
	adoxq	%rbp,%r12
	adcxq	%rbp,%r12

	movq	%r8,56(%rdi)
	movq	%r9,64(%rdi)

	mulxq	%r14,%r9,%rax
	movq	56(%rsi),%r8
	adcxq	%r10,%r9
	mulxq	%r15,%r10,%rbx
	adoxq	%rax,%r10
	adcxq	%r11,%r10
	mulxq	%r8,%r11,%rax
	movq	%r14,%rdx
	adoxq	%rbx,%r11
	adcxq	%r12,%r11

	adcxq	%rbp,%rax

	mulxq	%r15,%r14,%rbx
	mulxq	%r8,%r12,%r13
	movq	%r15,%rdx
	leaq	64(%rsi),%rsi
	adcxq	%r14,%r11
	adoxq	%rbx,%r12
	adcxq	%rax,%r12
	adoxq	%rbp,%r13

	mulxq	%r8,%r8,%r14
	adcxq	%r8,%r13
	adcxq	%rbp,%r14

	cmpq	8+8(%rsp),%rsi
	je	9f

2:
	negq	%rcx
	movq	$-8,%rcx
	movq	%rbp,%r15
	movq	64(%rdi),%r8
	adcxq	72(%rdi),%r9
	adcxq	80(%rdi),%r10
	adcxq	88(%rdi),%r11
	adcq	96(%rdi),%r12
	adcq	104(%rdi),%r13
	adcq	112(%rdi),%r14
	adcq	120(%rdi),%r15
	leaq	(%rsi),%rbp
	leaq	128(%rdi),%rdi
	sbbq	%rax,%rax

	movq	-64(%rsi),%rdx
	movq	%rax,16+8(%rsp)
	movq	%rdi,24+8(%rsp)


	xorl	%eax,%eax
	jmp	3f

	.p2align	5
3:
	movq	%r8,%rbx
	mulxq	0(%rbp),%rax,%r8
	adcxq	%rax,%rbx
	adoxq	%r9,%r8

	mulxq	8(%rbp),%rax,%r9
	adcxq	%rax,%r8
	adoxq	%r10,%r9

	mulxq	16(%rbp),%rax,%r10
	adcxq	%rax,%r9
	adoxq	%r11,%r10

	mulxq	24(%rbp),%rax,%r11
	adcxq	%rax,%r10
	adoxq	%r12,%r11

	mulxq	32(%rbp),%rax,%r12
	adcxq	%rax,%r11
	adoxq	%r13,%r12

	mulxq	40(%rbp),%rax,%r13
	adcxq	%rax,%r12
	adoxq	%r14,%r13

	mulxq	48(%rbp),%rax,%r14
	movq	%rbx,(%rdi,%rcx,8)
	movl	$0,%ebx
	adcxq	%rax,%r13
	adoxq	%r15,%r14

	mulxq	56(%rbp),%rax,%r15
	movq	8(%rsi,%rcx,8),%rdx
	adcxq	%rax,%r14
	adoxq	%rbx,%r15
	adcxq	%rbx,%r15

	incq	%rcx
	jnz	3b

	leaq	64(%rbp),%rbp
	movq	$-8,%rcx
	cmpq	8+8(%rsp),%rbp
	je	5f

4:
	subq	16+8(%rsp),%rbx
	movq	-64(%rsi),%rdx
	adcxq	0(%rdi),%r8
	adcxq	8(%rdi),%r9
	adcq	16(%rdi),%r10
	adcq	24(%rdi),%r11
	adcq	32(%rdi),%r12
	adcq	40(%rdi),%r13
	adcq	48(%rdi),%r14
	adcq	56(%rdi),%r15
	leaq	64(%rdi),%rdi
	sbbq	%rax,%rax
	xorl	%ebx,%ebx
	movq	%rax,16+8(%rsp)
	jmp	3f

	.p2align	5
3:
	movq	%r8,%rbx
	mulxq	0(%rbp),%rax,%r8
	adcxq	%rax,%rbx
	adoxq	%r9,%r8

	mulxq	8(%rbp),%rax,%r9
	adcxq	%rax,%r8
	adoxq	%r10,%r9

	mulxq	16(%rbp),%rax,%r10
	adcxq	%rax,%r9
	adoxq	%r11,%r10

	mulxq	24(%rbp),%rax,%r11
	adcxq	%rax,%r10
	adoxq	%r12,%r11

	mulxq	32(%rbp),%rax,%r12
	adcxq	%rax,%r11
	adoxq	%r13,%r12

	mulxq	40(%rbp),%rax,%r13
	adcxq	%rax,%r12
	adoxq	%r14,%r13

	mulxq	48(%rbp),%rax,%r14
	movq	%rbx,(%rdi,%rcx,8)
	movl	$0,%ebx
	adcxq	%rax,%r13
	adoxq	%r15,%r14

	mulxq	56(%rbp),%rax,%r15
	movq	8(%rsi,%rcx,8),%rdx
	adcxq	%rax,%r14
	adoxq	%rbx,%r15
	adcxq	%rbx,%r15

	incq	%rcx
	jnz	3b

	leaq	64(%rbp),%rbp
	movq	$-8,%rcx
	cmpq	8+8(%rsp),%rbp
	jne	4b

5:
	xorq	%rbp,%rbp
	subq	16+8(%rsp),%rbx
	adcxq	%rbp,%r8
	movq	24+8(%rsp),%rcx
	adcxq	%rbp,%r9
	movq	0(%rsi),%rdx
	adcq	$0,%r10
	movq	%r8,0(%rdi)
	adcq	$0,%r11
	adcq	$0,%r12
	adcq	$0,%r13
	adcq	$0,%r14
	adcq	$0,%r15
	cmpq	%rcx,%rdi
	je	6f

	movq	%r9,8(%rdi)
	movq	8(%rcx),%r9
	movq	%r10,16(%rdi)
	movq	16(%rcx),%r10
	movq	%r11,24(%rdi)
	movq	24(%rcx),%r11
	movq	%r12,32(%rdi)
	movq	32(%rcx),%r12
	movq	%r13,40(%rdi)
	movq	40(%rcx),%r13
	movq	%r14,48(%rdi)
	movq	48(%rcx),%r14
	movq	%r15,56(%rdi)
	movq	56(%rcx),%r15
	movq	%rcx,%rdi
6:
	mulxq	8(%rsi),%r8,%rax
	adcxq	%r9,%r8
	adoxq	%rax,%r10
	mulxq	16(%rsi),%r9,%rax
	adcxq	%r10,%r9
	adoxq	%rax,%r11
	mulxq	24(%rsi),%r10,%rax
	adcxq	%r11,%r10
	adoxq	%rax,%r12
	mulxq	32(%rsi),%r11,%rax
	adcxq	%r12,%r11
	adoxq	%rax,%r13
	mulxq	40(%rsi),%r12,%rax
	adcxq	%r13,%r12
	adoxq	%rax,%r14
	mulxq	48(%rsi),%r13,%rax
	adcxq	%r14,%r13
	adoxq	%r15,%rax
	mulxq	56(%rsi),%r14,%r15
	movq	8(%rsi),%rdx
	adcxq	%rax,%r14
	adoxq	%rbp,%r15
	adcq	64(%rdi),%r15
	movq	%r8,8(%rdi)
	movq	%r9,16(%rdi)
	sbbq	%rcx,%rcx
	xorq	%rbp,%rbp

	mulxq	16(%rsi),%r8,%rbx
	mulxq	24(%rsi),%r9,%rax
	adcxq	%r10,%r8
	adoxq	%rbx,%r9
	mulxq	32(%rsi),%r10,%rbx
	adcxq	%r11,%r9
	adoxq	%rax,%r10
	mulxq	40(%rsi),%r11,%rax
	adcxq	%r12,%r10
	adoxq	%rbx,%r11
	mulxq	48(%rsi),%r12,%rbx
	adcxq	%r13,%r11
	adoxq	%r14,%r12
	mulxq	56(%rsi),%r13,%r14
	movq	16(%rsi),%rdx
	adcxq	%rax,%r12
	adoxq	%rbx,%r13
	adcxq	%r15,%r13
	adoxq	%rbp,%r14
	adcxq	%rbp,%r14

	movq	%r8,24(%rdi)
	movq	%r9,32(%rdi)

	mulxq	24(%rsi),%r8,%rbx
	mulxq	32(%rsi),%r9,%rax
	adcxq	%r10,%r8
	adoxq	%rbx,%r9
	mulxq	40(%rsi),%r10,%rbx
	adcxq	%r11,%r9
	adoxq	%rax,%r10
	mulxq	48(%rsi),%r11,%rax
	adcxq	%r12,%r10
	adoxq	%r13,%r11
	mulxq	56(%rsi),%r12,%r13
	movq	24(%rsi),%rdx
	adcxq	%rbx,%r11
	adoxq	%rax,%r12
	adcxq	%r14,%r12
	movq	%r8,40(%rdi)
	movq	%r9,48(%rdi)
	mulxq	32(%rsi),%r8,%rax
	adoxq	%rbp,%r13
	adcxq	%rbp,%r13

	mulxq	40(%rsi),%r9,%rbx
	adcxq	%r10,%r8
	adoxq	%rax,%r9
	mulxq	48(%rsi),%r10,%rax
	adcxq	%r11,%r9
	adoxq	%r12,%r10
	mulxq	56(%rsi),%r11,%r12
	movq	32(%rsi),%rdx
	movq	40(%rsi),%r14
	adcxq	%rbx,%r10
	adoxq	%rax,%r11
	movq	48(%rsi),%r15
	adcxq	%r13,%r11
	adoxq	%rbp,%r12
	adcxq	%rbp,%r12

	movq	%r8,56(%rdi)
	movq	%r9,64(%rdi)

	mulxq	%r14,%r9,%rax
	movq	56(%rsi),%r8
	adcxq	%r10,%r9
	mulxq	%r15,%r10,%rbx
	adoxq	%rax,%r10
	adcxq	%r11,%r10
	mulxq	%r8,%r11,%rax
	movq	%r14,%rdx
	adoxq	%rbx,%r11
	adcxq	%r12,%r11

	adcxq	%rbp,%rax

	mulxq	%r15,%r14,%rbx
	mulxq	%r8,%r12,%r13
	movq	%r15,%rdx
	leaq	64(%rsi),%rsi
	adcxq	%r14,%r11
	adoxq	%rbx,%r12
	adcxq	%rax,%r12
	adoxq	%rbp,%r13

	mulxq	%r8,%r8,%r14
	adcxq	%r8,%r13
	adcxq	%rbp,%r14

	cmpq	8+8(%rsp),%rsi
	jne	2b

9:
	movq	%r9,72(%rdi)
	movq	%xmm3,%rcx
	movq	%r10,80(%rdi)
	movq	%r11,88(%rdi)
	movq	%r12,96(%rdi)
	movq	%r13,104(%rdi)
	movq	%r14,112(%rdi)
	leaq	48+8(%rsp),%rdi
	movq	(%rsi,%rcx,1),%rdx

	movq	8(%rdi),%r11
	xorq	%r10,%r10
	movq	0+8(%rsp),%r9
	adoxq	%r11,%r11
	movq	16(%rdi),%r12
	movq	24(%rdi),%r13


	.p2align	5
1:
	mulxq	%rdx,%rax,%rbx
	adoxq	%r12,%r12
	adcxq	%r10,%rax
	movq	8(%rsi,%rcx,1),%rdx
	movq	32(%rdi),%r10
	adoxq	%r13,%r13
	adcxq	%r11,%rbx
	movq	40(%rdi),%r11
	movq	%rax,0(%rdi)
	movq	%rbx,8(%rdi)

	mulxq	%rdx,%rax,%rbx
	adoxq	%r10,%r10
	adcxq	%r12,%rax
	movq	16(%rsi,%rcx,1),%rdx
	movq	48(%rdi),%r12
	adoxq	%r11,%r11
	adcxq	%r13,%rbx
	movq	56(%rdi),%r13
	movq	%rax,16(%rdi)
	movq	%rbx,24(%rdi)

	mulxq	%rdx,%rax,%rbx
	adoxq	%r12,%r12
	adcxq	%r10,%rax
	movq	24(%rsi,%rcx,1),%rdx
	leaq	32(%rcx),%rcx
	movq	64(%rdi),%r10
	adoxq	%r13,%r13
	adcxq	%r11,%rbx
	movq	72(%rdi),%r11
	movq	%rax,32(%rdi)
	movq	%rbx,40(%rdi)

	mulxq	%rdx,%rax,%rbx
	adoxq	%r10,%r10
	adcxq	%r12,%rax
	jrcxz	2f
	movq	(%rsi,%rcx,1),%rdx
	adoxq	%r11,%r11
	adcxq	%r13,%rbx
	movq	80(%rdi),%r12
	movq	88(%rdi),%r13
	movq	%rax,48(%rdi)
	movq	%rbx,56(%rdi)
	leaq	64(%rdi),%rdi
2:
	jrcxz	3f
	jmp	1b
3:
	adcxq	%r13,%rbx
	movq	%rax,48(%rdi)
	movq	%rbx,56(%rdi)
	leaq	64(%rdi),%rdi
	movq	%xmm2,%rbp
	xorl	%eax,%eax
	movq	32+8(%rsp),%rbx
	movq	48+8(%rsp),%rdx
	leaq	-64(%rbp,%r9,1),%rcx

	movq	%rcx,0+8(%rsp)
	movq	%rdi,8+8(%rsp)

	leaq	48+8(%rsp),%rdi

	.p2align	5
1:
	movq	8(%rdi),%r9
	movq	16(%rdi),%r10
	movq	24(%rdi),%r11
	movq	32(%rdi),%r12
	movq	%rdx,%r8
	imulq	%rbx,%rdx
	movq	40(%rdi),%r13
	movq	48(%rdi),%r14
	movq	56(%rdi),%r15
	movq	%rax,24+8(%rsp)

	leaq	64(%rdi),%rdi
	xorq	%rsi,%rsi
	movq	$-8,%rcx
	jmp	2f

	.p2align	5
2:
	movq	%r8,%rbx
	mulxq	0(%rbp),%rax,%r8
	adcxq	%rbx,%rax
	adoxq	%r9,%r8

	mulxq	8(%rbp),%rbx,%r9
	adcxq	%rbx,%r8
	adoxq	%r10,%r9

	mulxq	16(%rbp),%rbx,%r10
	adcxq	%rbx,%r9
	adoxq	%r11,%r10

	mulxq	24(%rbp),%rbx,%r11
	adcxq	%rbx,%r10
	adoxq	%r12,%r11

	mulxq	32(%rbp),%rbx,%r12
	movq	%rdx,%rax
	movq	%r8,%rdx
	adcxq	%rbx,%r11
	adoxq	%r13,%r12

	mulxq	32+8(%rsp),%rbx,%rdx
	movq	%rax,%rdx
	movq	%rax,64+48+8(%rsp,%rcx,8)

	mulxq	40(%rbp),%rax,%r13
	adcxq	%rax,%r12
	adoxq	%r14,%r13

	mulxq	48(%rbp),%rax,%r14
	adcxq	%rax,%r13
	adoxq	%r15,%r14

	mulxq	56(%rbp),%rax,%r15
	movq	%rbx,%rdx
	adcxq	%rax,%r14
	adoxq	%rsi,%r15
	adcxq	%rsi,%r15

	incq	%rcx
	jnz	2b

	movq	%rsi,%rax
	cmpq	0+8(%rsp),%rbp
	jae	5f

	movq	48+8(%rsp),%rdx
	addq	0(%rdi),%r8
	leaq	64(%rbp),%rbp
	movq	$-8,%rcx
	adcxq	8(%rdi),%r9
	adcxq	16(%rdi),%r10
	adcq	24(%rdi),%r11
	adcq	32(%rdi),%r12
	adcq	40(%rdi),%r13
	adcq	48(%rdi),%r14
	adcq	56(%rdi),%r15
	leaq	64(%rdi),%rdi
	sbbq	%rax,%rax

	xorq	%rsi,%rsi
	movq	%rax,16+8(%rsp)
	jmp	2f

	.p2align	5
2:
	movq	%r8,%rbx
	mulxq	0(%rbp),%rax,%r8
	adcxq	%rax,%rbx
	adoxq	%r9,%r8

	mulxq	8(%rbp),%rax,%r9
	adcxq	%rax,%r8
	adoxq	%r10,%r9

	mulxq	16(%rbp),%rax,%r10
	adcxq	%rax,%r9
	adoxq	%r11,%r10

	mulxq	24(%rbp),%rax,%r11
	adcxq	%rax,%r10
	adoxq	%r12,%r11

	mulxq	32(%rbp),%rax,%r12
	adcxq	%rax,%r11
	adoxq	%r13,%r12

	mulxq	40(%rbp),%rax,%r13
	adcxq	%rax,%r12
	adoxq	%r14,%r13

	mulxq	48(%rbp),%rax,%r14
	adcxq	%rax,%r13
	adoxq	%r15,%r14

	mulxq	56(%rbp),%rax,%r15
	movq	72+48+8(%rsp,%rcx,8),%rdx
	adcxq	%rax,%r14
	adoxq	%rsi,%r15
	movq	%rbx,(%rdi,%rcx,8)
	movq	%r8,%rbx
	adcxq	%rsi,%r15

	incq	%rcx
	jnz	2b

	cmpq	0+8(%rsp),%rbp
	jae	4f

3:
	subq	16+8(%rsp),%rsi
	movq	48+8(%rsp),%rdx
	leaq	64(%rbp),%rbp
	adcq	0(%rdi),%r8
	adcq	8(%rdi),%r9
	adcq	16(%rdi),%r10
	adcq	24(%rdi),%r11
	adcq	32(%rdi),%r12
	adcq	40(%rdi),%r13
	adcq	48(%rdi),%r14
	adcq	56(%rdi),%r15
	leaq	64(%rdi),%rdi
	sbbq	%rax,%rax
	subq	$8,%rcx

	xorq	%rsi,%rsi
	movq	%rax,16+8(%rsp)
	jmp	2f

	.p2align	5
2:
	movq	%r8,%rbx
	mulxq	0(%rbp),%rax,%r8
	adcxq	%rax,%rbx
	adoxq	%r9,%r8

	mulxq	8(%rbp),%rax,%r9
	adcxq	%rax,%r8
	adoxq	%r10,%r9

	mulxq	16(%rbp),%rax,%r10
	adcxq	%rax,%r9
	adoxq	%r11,%r10

	mulxq	24(%rbp),%rax,%r11
	adcxq	%rax,%r10
	adoxq	%r12,%r11

	mulxq	32(%rbp),%rax,%r12
	adcxq	%rax,%r11
	adoxq	%r13,%r12

	mulxq	40(%rbp),%rax,%r13
	adcxq	%rax,%r12
	adoxq	%r14,%r13

	mulxq	48(%rbp),%rax,%r14
	adcxq	%rax,%r13
	adoxq	%r15,%r14

	mulxq	56(%rbp),%rax,%r15
	movq	72+48+8(%rsp,%rcx,8),%rdx
	adcxq	%rax,%r14
	adoxq	%rsi,%r15
	movq	%rbx,(%rdi,%rcx,8)
	movq	%r8,%rbx
	adcxq	%rsi,%r15

	incq	%rcx
	jnz	2b

	cmpq	0+8(%rsp),%rbp
	jb	3b

4:
	xorq	%rax,%rax
	addq	24+8(%rsp),%r8
	adcq	$0,%r9
	adcq	$0,%r10
	adcq	$0,%r11
	adcq	$0,%r12
	adcq	$0,%r13
	adcq	$0,%r14
	adcq	$0,%r15
	adcq	$0,%rax

	subq	16+8(%rsp),%rsi
5:
	adcq	0(%rdi),%r8
	movq	%xmm3,%rcx
	adcq	8(%rdi),%r9
	movq	56(%rbp),%rsi
	movq	%xmm2,%rbp
	adcq	16(%rdi),%r10
	adcq	24(%rdi),%r11
	adcq	32(%rdi),%r12
	adcq	40(%rdi),%r13
	adcq	48(%rdi),%r14
	adcq	56(%rdi),%r15
	adcq	$0,%rax

	movq	32+8(%rsp),%rbx
	movq	64(%rdi,%rcx,1),%rdx

	movq	%r8,0(%rdi)
	leaq	64(%rdi),%r8
	movq	%r9,8(%rdi)
	movq	%r10,16(%rdi)
	movq	%r11,24(%rdi)
	movq	%r12,32(%rdi)
	movq	%r13,40(%rdi)
	movq	%r14,48(%rdi)
	movq	%r15,56(%rdi)

	leaq	64(%rdi,%rcx,1),%rdi
	cmpq	8+8(%rsp),%r8
	jb	1b
	.byte	0xf3,0xc3
