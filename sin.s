#if __riscv_flen >= 64

.section .text
.global sin
.type sin, @function

sin:
	addi sp, sp, -8
	sd ra, 0(sp)
	
	fmv.x.d t0, fa0 # move input bits from float to integer
	
	# NaN formation
	lui a1, 524160 # 0b01111111111110000000
	slli a1, a1, 32 # shift left by 32, now it is 0x7ff8000000000000
	
	# input = NaN, return NaN
	beq t0, a1, .returnNaN 
	
	# +Inf Formation	
	lui a2, 524032 # 0b01111111111100000000
	slli a2, a2, 32 # shift left by 32
	
	# input = +Inf, return NaN
	beq t0, a2, .returnNaN 
	
	# -Inf Formation	
	lui a2, 1048320 # 0b11111111111100000000
	slli a2, a2, 32 # shift left by 32
	
	# input = -Inf, return NaN
	beq t0, a2, .returnNaN 
	
	# PI FORMATION
	# load upper half of PI
	lui t0, 262290 # 0b01000000000010010010
	addi t0, t0, 507 # 0b000111111011
	
	slli t0,t0,32 # shift left by 32
	
	# load lower half of PI
	lui t1, 345155 # 0b01010100010001000011                         !!!QUESTION
	# 0b01010100010001000010 needed but somehow it makes -1 beacause of - 744
	addi t1, t1, -744 # 0b110100011000
	
	or t0, t0, t1 # Unite halfs to get PI
	
	fmv.d.x fa1, t0 # move PI bits from integer to float
	
	# x = PI * k + x*
	fdiv.d ft0, fa0, fa1 # ft0 = x/pi
	
	fcvt.l.d t0, ft0, rdn # t0 = k = rounded_down(x/pi)
	fcvt.d.l ft0, t0 # ft0 = k = rounded_down(x/pi)
	
	fmul.d ft0, ft0, fa1 # ft0 = k * PI
	
	fsub.d fa0, fa0, ft0 # ft0 = x - k * PI = k * PI + x* - k * PI = x*
	
	addi sp, sp, -8
	sd t0, 0(sp)
	jal ra, __sin # count sin(x*)
	ld t0, 0(sp)
	addi sp, sp, 8
	
	li t1, 1
	and t0, t0, t1 # check even or odd
	
	beq t0, t1, .negativeSin # if odd, change sign
	
	ld ra, 0(sp)
	addi sp, sp, 8
	ret
	
.returnNaN:
	fmv.d.x fa0, a1 # move bits from integer to float
	ld ra, 0(sp)
	addi sp, sp, 8
	ret
	
.negativeSin:
	fcvt.d.l ft0, zero
	fsub.d fa0, ft0, fa0
	ld ra, 0(sp)
	addi sp, sp, 8
	ret
	
.type __sin, @function
__sin:	
	li t0, 2
	fcvt.d.l ft0, t0
	fdiv.d ft0, ft0, fa1 # fa3 = 2/pi
	
	fmul.d ft0, ft0, ft0 # ft0 = (2/pi)^2
	fmul.d ft0, ft0, fa0 # ft0 = (2/pi)^2 * x
	fsub.d ft1, fa1, fa0 # ft1 = pi - x
	fmul.d ft0, ft0, ft1 # ft0 = s(x) = (2/pi)^2 * x * (pi - x)
	
	# 0.224 FORMATION
	# load upper half of 0.224
	lui t0, 261323 # 0b00111111110011001011
	addi t0, t0, -1016 # 0b110000001000
	
	slli t0,t0,32 # shift left by 32
	
	# load lower half of 0.224
	lui t1, 201327 # 0b00110001001001101111
	addi t1, t1, -1672 # 0b100101111000
	
	or t0, t0, t1 # Unite halfs to get 0.224
	fmv.d.x ft1, t0 # move PI bits from integer to float
	
	li t0, 1
	fcvt.d.l ft2, t0 # ft2 = 1.0
	fsub.d ft2, ft2, ft1 # ft2 = 0,776
	fmul.d ft1, ft1, ft0 # ft1 = 0.224 * s(x)
	fadd.d ft1, ft1, ft2 # ft1 = 0,776 + 0.224 * s(x)
	fmul.d fa0, ft0, ft1 # fa0 = s(x)(0,776 + 0.224 * s(x))
	
	ret
	
#else

#include "../sin.c"

#endif
