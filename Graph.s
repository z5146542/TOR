	.file	"Graph.c"
	.text
	.globl	is_wellformed
	.type	is_wellformed, @function
is_wellformed:
.LFB0:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	movl	$0, -4(%rbp)
	jmp	.L2
.L6:
	movq	-24(%rbp), %rax
	movq	8(%rax), %rax
	movl	-4(%rbp), %edx
	salq	$3, %rdx
	addq	%rdx, %rax
	movq	(%rax), %rax
	movq	%rax, -12(%rbp)
	movq	-24(%rbp), %rax
	movl	(%rax), %edx
	movl	-12(%rbp), %eax
	cmpl	%eax, %edx
	ja	.L3
	movl	$0, %eax
	jmp	.L7
.L3:
	movq	-24(%rbp), %rax
	movl	(%rax), %edx
	movl	-8(%rbp), %eax
	cmpl	%eax, %edx
	ja	.L5
	movl	$0, %eax
	jmp	.L7
.L5:
	addl	$1, -4(%rbp)
.L2:
	movq	-24(%rbp), %rax
	movl	4(%rax), %eax
	cmpl	%eax, -4(%rbp)
	jb	.L6
	movl	$1, %eax
.L7:
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	is_wellformed, .-is_wellformed
	.globl	trian
	.type	trian, @function
trian:
.LFB1:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	movq	%rdx, -40(%rbp)
	movl	$0, -4(%rbp)
	jmp	.L9
.L12:
	movq	-24(%rbp), %rax
	movq	8(%rax), %rax
	movl	-4(%rbp), %edx
	salq	$3, %rdx
	addq	%rdx, %rax
	movl	4(%rax), %eax
	movl	%eax, %eax
	leaq	0(,%rax,4), %rdx
	movq	-32(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %edx
	movq	-24(%rbp), %rax
	movq	8(%rax), %rax
	movl	-4(%rbp), %ecx
	salq	$3, %rcx
	addq	%rcx, %rax
	movl	(%rax), %eax
	movl	%eax, %eax
	leaq	0(,%rax,4), %rcx
	movq	-32(%rbp), %rax
	addq	%rcx, %rax
	movl	(%rax), %eax
	movl	-4(%rbp), %ecx
	leaq	0(,%rcx,4), %rsi
	movq	-40(%rbp), %rcx
	addq	%rsi, %rcx
	movl	(%rcx), %ecx
	addl	%ecx, %eax
	cmpl	%eax, %edx
	jle	.L10
	movl	$0, %eax
	jmp	.L11
.L10:
	addl	$1, -4(%rbp)
.L9:
	movq	-24(%rbp), %rax
	movl	4(%rax), %eax
	cmpl	%eax, -4(%rbp)
	jb	.L12
	movl	$1, %eax
.L11:
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1:
	.size	trian, .-trian
	.globl	just
	.type	just, @function
just:
.LFB2:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	movq	%rdx, -40(%rbp)
	movl	%ecx, -44(%rbp)
	movq	%r8, -56(%rbp)
	movq	%r9, -64(%rbp)
	movl	$0, -4(%rbp)
	jmp	.L14
.L20:
	movl	-4(%rbp), %eax
	leaq	0(,%rax,4), %rdx
	movq	-64(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %eax
	movl	%eax, -8(%rbp)
	movl	-4(%rbp), %eax
	cmpl	-44(%rbp), %eax
	je	.L15
	movl	-4(%rbp), %eax
	leaq	0(,%rax,4), %rdx
	movq	-56(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %eax
	testl	%eax, %eax
	js	.L15
	movq	-24(%rbp), %rax
	movl	4(%rax), %eax
	cmpl	%eax, -8(%rbp)
	jb	.L16
	movl	$0, %eax
	jmp	.L17
.L16:
	movq	-24(%rbp), %rax
	movq	8(%rax), %rax
	movl	-8(%rbp), %edx
	salq	$3, %rdx
	addq	%rdx, %rax
	movl	4(%rax), %eax
	cmpl	%eax, -4(%rbp)
	je	.L18
	movl	$0, %eax
	jmp	.L17
.L18:
	movl	-4(%rbp), %eax
	leaq	0(,%rax,4), %rdx
	movq	-32(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %edx
	movq	-24(%rbp), %rax
	movq	8(%rax), %rax
	movl	-8(%rbp), %ecx
	salq	$3, %rcx
	addq	%rcx, %rax
	movl	(%rax), %eax
	movl	%eax, %eax
	leaq	0(,%rax,4), %rcx
	movq	-32(%rbp), %rax
	addq	%rcx, %rax
	movl	(%rax), %eax
	movl	-8(%rbp), %ecx
	leaq	0(,%rcx,4), %rsi
	movq	-40(%rbp), %rcx
	addq	%rsi, %rcx
	movl	(%rcx), %ecx
	addl	%ecx, %eax
	cmpl	%eax, %edx
	je	.L19
	movl	$0, %eax
	jmp	.L17
.L19:
	movl	-4(%rbp), %eax
	leaq	0(,%rax,4), %rdx
	movq	-56(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %edx
	movq	-24(%rbp), %rax
	movq	8(%rax), %rax
	movl	-8(%rbp), %ecx
	salq	$3, %rcx
	addq	%rcx, %rax
	movl	(%rax), %eax
	movl	%eax, %eax
	leaq	0(,%rax,4), %rcx
	movq	-56(%rbp), %rax
	addq	%rcx, %rax
	movl	(%rax), %eax
	addl	$1, %eax
	cmpl	%eax, %edx
	je	.L15
	movl	$0, %eax
	jmp	.L17
.L15:
	addl	$1, -4(%rbp)
.L14:
	movq	-24(%rbp), %rax
	movl	(%rax), %eax
	cmpl	%eax, -4(%rbp)
	jb	.L20
	movl	$1, %eax
.L17:
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE2:
	.size	just, .-just
	.globl	no_path
	.type	no_path, @function
no_path:
.LFB3:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	movq	%rdx, -40(%rbp)
	movl	$0, -4(%rbp)
	jmp	.L22
.L26:
	movl	-4(%rbp), %eax
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-32(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %eax
	testl	%eax, %eax
	jns	.L23
	movl	-4(%rbp), %eax
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-40(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %eax
	testl	%eax, %eax
	js	.L24
	movl	$0, %eax
	jmp	.L25
.L23:
	movl	-4(%rbp), %eax
	cltq
	leaq	0(,%rax,4), %rdx
	movq	-40(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %eax
	testl	%eax, %eax
	jns	.L24
	movl	$0, %eax
	jmp	.L25
.L24:
	addl	$1, -4(%rbp)
.L22:
	movq	-24(%rbp), %rax
	movl	(%rax), %edx
	movl	-4(%rbp), %eax
	cmpl	%eax, %edx
	ja	.L26
	movl	$1, %eax
.L25:
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE3:
	.size	no_path, .-no_path
	.globl	pos_cost
	.type	pos_cost, @function
pos_cost:
.LFB4:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -24(%rbp)
	movq	%rsi, -32(%rbp)
	movl	$0, -4(%rbp)
	jmp	.L28
.L29:
	addl	$1, -4(%rbp)
.L28:
	movq	-24(%rbp), %rax
	movl	4(%rax), %eax
	cmpl	%eax, -4(%rbp)
	jb	.L29
	movl	$1, %eax
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE4:
	.size	pos_cost, .-pos_cost
	.globl	check_basic_just_sp
	.type	check_basic_just_sp, @function
check_basic_just_sp:
.LFB5:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$48, %rsp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movq	%rdx, -24(%rbp)
	movl	%ecx, -28(%rbp)
	movq	%r8, -40(%rbp)
	movq	%r9, -48(%rbp)
	movq	-8(%rbp), %rax
	movq	%rax, %rdi
	call	is_wellformed
	testl	%eax, %eax
	jne	.L32
	movl	$0, %eax
	jmp	.L33
.L32:
	movl	-28(%rbp), %eax
	leaq	0(,%rax,4), %rdx
	movq	-16(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %eax
	testl	%eax, %eax
	jle	.L34
	movl	$0, %eax
	jmp	.L33
.L34:
	movq	-24(%rbp), %rdx
	movq	-16(%rbp), %rcx
	movq	-8(%rbp), %rax
	movq	%rcx, %rsi
	movq	%rax, %rdi
	call	trian
	testl	%eax, %eax
	jne	.L35
	movl	$0, %eax
	jmp	.L33
.L35:
	movq	-48(%rbp), %r8
	movq	-40(%rbp), %rdi
	movl	-28(%rbp), %ecx
	movq	-24(%rbp), %rdx
	movq	-16(%rbp), %rsi
	movq	-8(%rbp), %rax
	movq	%r8, %r9
	movq	%rdi, %r8
	movq	%rax, %rdi
	call	just
	testl	%eax, %eax
	jne	.L36
	movl	$0, %eax
	jmp	.L33
.L36:
	movl	$1, %eax
.L33:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE5:
	.size	check_basic_just_sp, .-check_basic_just_sp
	.globl	check_sp
	.type	check_sp, @function
check_sp:
.LFB6:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$48, %rsp
	movq	%rdi, -8(%rbp)
	movq	%rsi, -16(%rbp)
	movq	%rdx, -24(%rbp)
	movl	%ecx, -28(%rbp)
	movq	%r8, -40(%rbp)
	movq	%r9, -48(%rbp)
	movq	-48(%rbp), %r8
	movq	-40(%rbp), %rdi
	movl	-28(%rbp), %ecx
	movq	-24(%rbp), %rdx
	movq	-16(%rbp), %rsi
	movq	-8(%rbp), %rax
	movq	%r8, %r9
	movq	%rdi, %r8
	movq	%rax, %rdi
	call	check_basic_just_sp
	testl	%eax, %eax
	jne	.L38
	movl	$0, %eax
	jmp	.L39
.L38:
	movq	-8(%rbp), %rax
	movl	(%rax), %eax
	cmpl	%eax, -28(%rbp)
	jb	.L40
	movl	$0, %eax
	jmp	.L39
.L40:
	movl	-28(%rbp), %eax
	leaq	0(,%rax,4), %rdx
	movq	-16(%rbp), %rax
	addq	%rdx, %rax
	movl	(%rax), %eax
	testl	%eax, %eax
	je	.L41
	movl	$0, %eax
	jmp	.L39
.L41:
	movq	-40(%rbp), %rdx
	movq	-16(%rbp), %rcx
	movq	-8(%rbp), %rax
	movq	%rcx, %rsi
	movq	%rax, %rdi
	call	no_path
	testl	%eax, %eax
	jne	.L42
	movl	$0, %eax
	jmp	.L39
.L42:
	movq	-24(%rbp), %rdx
	movq	-8(%rbp), %rax
	movq	%rdx, %rsi
	movq	%rax, %rdi
	call	pos_cost
	testl	%eax, %eax
	jne	.L43
	movl	$0, %eax
	jmp	.L39
.L43:
	movl	$1, %eax
.L39:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE6:
	.size	check_sp, .-check_sp
	.globl	main
	.type	main, @function
main:
.LFB7:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movl	%edi, -4(%rbp)
	movq	%rsi, -16(%rbp)
	movl	$0, %eax
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE7:
	.size	main, .-main
	.ident	"GCC: (Debian 8.2.0-13) 8.2.0"
	.section	.note.GNU-stack,"",@progbits
