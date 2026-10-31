// AArch64 residue kernels for 2-adic arithmetic (macOS / Apple assembler).
// These are decoded-residue kernels, not a packed 64-bit format implementation.
// x0 = a, x1 = b, x2 = 2^r-1, 1 <= r <= 64. Return residue in x0.
// For r=64 use UINT64_MAX, not (1ULL << 64)-1.
// Add/sub also take x3=ea and x4=eb (signed exponents), and align internally.
// Mul/div operands are odd unit residues; division requires an odd denominator.
// For addition/subtraction choose e=min(ea,eb), A=min(ea+ra,eb+rb), r=A-e.
// The caller selects that common-precision mask before calling add/sub.
// If result z!=0: k=ctz(z); m=z>>k; exponent=e+k; known precision=r-k.
// If z==0: return uncertain zero O(2^A), not exact zero.
// For multiplication/division use r=min(ra,rb), exponent=ea+eb / ea-eb.
// Exponent overflow, exact-zero special cases and packing are caller tasks.
// Darwin C symbols have a leading underscore; remove it for ELF targets.
.text
.p2align 2

// Shared inline alignment. Use six distinct 64-bit general-purpose registers.
// a/b are updated; ea/eb are preserved; e/shift are written. Clobbers NZCV.
// No calls or stack traffic.
// Shifts >=64 must produce zero, not wrap modulo 64 as LSL alone would.
.macro padic2_align_pair a:req, b:req, ea:req, eb:req, e:req, shift:req
    cmp     \ea, \eb
    csel    \e, \ea, \eb, lt   // e = min(ea, eb), signed comparison.

    sub     \shift, \ea, \e    // da = ea - e >= 0.
    cmp     \shift, #64
    lsl     \a, \a, \shift
    csel    \a, \a, xzr, lo   // Zero if da >= 64; LSL preserves flags.

    sub     \shift, \eb, \e    // db = eb - e >= 0.
    cmp     \shift, #64
    lsl     \b, \b, \shift
    csel    \b, \b, xzr, lo
.endm

.globl _padic2_add
_padic2_add:
    padic2_align_pair x0, x1, x3, x4, x5, x6
    add     x0, x0, x1
    and     x0, x0, x2
    ret

.globl _padic2_sub
_padic2_sub:
    padic2_align_pair x0, x1, x3, x4, x5, x6
    sub     x0, x0, x1
    and     x0, x0, x2
    ret

.globl _padic2_neg
_padic2_neg:
    neg     x0, x0
    and     x0, x0, x2
    ret

.globl _padic2_mul
_padic2_mul:
    mul     x0, x0, x1       // Low 64 product bits suffice.
    and     x0, x0, x2
    ret

// Shared unsigned integer primitive: exact 64-by-64 -> 128-bit product.
// __uint128_t integer_mul_wide(uint64_t a, uint64_t b)
// Darwin ARM64 returns the low/high words in x0/x1. No modular reduction,
// sign, exponent or rounding policy. FP64Integer.c uses it for significand
// multiplication, real reciprocal refinement, and exact quotient correction.
.globl _integer_mul_wide
_integer_mul_wide:
    mul     x2, x0, x1
    umulh   x1, x0, x1
    mov     x0, x2
    ret

.globl _padic2_div
_padic2_div:
    mov     x3, x1           // b*b = 1 mod 8 for every odd b.
    mov     x4, #2
    .rept 5                 // Correct bits: 3 -> 6 -> 12 -> 24 -> 48 -> 64.
    msub    x5, x1, x3, x4  // t = 2 - b*y, modulo 2^64.
    mul     x3, x3, x5      // y = y*t, modulo 2^64.
    .endr
    mul     x0, x0, x3      // a/b modulo 2^64.
    and     x0, x0, x2
    ret

// Alignment helper: x0 = m, x1 = nonnegative shift d, x2 = mask.
// Return (m << d) modulo 2^r, including d >= 64.
// AArch64 register shifts use only the low 6 shift-count bits, so guard d >= 64.
.globl _padic2_align
_padic2_align:
    cmp     x1, #64
    lsl     x0, x0, x1
    csel    x0, x0, xzr, lo
    and     x0, x0, x2
    ret

// Trailing-zero count: caller handles zero separately; ctz(0) returns 64.
.globl _padic2_ctz
_padic2_ctz:
    rbit    x0, x0
    clz     x0, x0
    ret

// void padic2_from_double(double value, uint64_t mask, Padic2Decoded *out)
// Darwin ARM64 C ABI: value=d0, mask=x0, out=x1 (FP/GP argument banks separate).
// Output fields: residue at +0, signed exponent at +8, status at +16.
// No packing or exponent clamping: all finite binary64 valuations are retained.
.globl _padic2_from_double
_padic2_from_double:
    mov     x9, x1
    mov     x2, x0
    fmov    x0, d0          // Bit transfer, not FP arithmetic/conversion.
    lsr     x5, x0, #63
    ubfx    x3, x0, #52, #11
    and     x4, x0, #0x000fffffffffffff
    cmp     x3, #2047
    b.eq    Lfp_nonfinite
    cbz     x3, Lfp_subnormal
    orr     x4, x4, #0x0010000000000000
    sub     x1, x3, #1075   // E - 1023 - 52.
    b       Lfp_normalize
Lfp_subnormal:
    cbz     x4, Lfp_zero
    mov     x1, #-1074
Lfp_normalize:
    rbit    x6, x4
    clz     x6, x6
    lsr     x4, x4, x6
    add     x1, x1, x6
    cmp     x5, #0
    cneg    x0, x4, ne
    and     x0, x0, x2
    mov     x7, #0          // PADIC2_FINITE.
    b       Lfp_store
Lfp_zero:
    mov     x7, #1          // PADIC2_EXACT_ZERO, including -0.0.
    b       Lfp_special
Lfp_nonfinite:
    mov     x7, #2          // PADIC2_NONFINITE: infinity or NaN.
Lfp_special:
    mov     x0, #0
    mov     x1, #0
Lfp_store:
    stp     x0, x1, [x9]
    str     x7, [x9, #16]
    ret

// double padic2_to_double_dyadic(const Padic2Decoded *value, uint64_t r)
// C ABI: value=x0, r=x1, result=d0. Caller-saved registers only.
// Select the signed r-bit integer representative; pack s*2^e as binary64.
// Round ONCE, ties-to-even, even for subnormals (SCVTF then scaling can round twice).
// No FP arithmetic or FPCR dependence; no IEEE exception flags are raised.
.globl _padic2_to_double_dyadic
_padic2_to_double_dyadic:
    sub     x2, x1, #1
    cmp     x2, #63
    b.hi    Ldy_nan         // Reject r=0 or r>64 before variable shifts.
    ldr     x3, [x0, #16]
    cmp     x3, #1
    b.eq    Ldy_exact_zero
    cbnz    x3, Ldy_nan
    mov     x2, x1
    ldp     x0, x1, [x0]    // m, e.
    mov     x4, #64
    sub     x4, x4, x2
    lsl     x0, x0, x4
    asr     x0, x0, x4      // Sign-extend the low r bits, including r=64.
    asr     x3, x0, #63
    eor     x0, x0, x3
    sub     x0, x0, x3      // Unsigned magnitude; handles INT64_MIN.
    and     x3, x3, #0x8000000000000000
    cbz     x0, Ldy_signed_zero

    // Bound e before adding the leading-bit index: int64 extremes cannot wrap.
    cmp     x1, #1024
    b.ge    Ldy_infinity
    mov     x4, #-1138
    cmp     x1, x4
    b.le    Ldy_signed_zero // Even 2^63 * 2^-1138 is only half a subnormal ulp.
    clz     x2, x0
    mov     x4, #63
    sub     x2, x4, x2      // h = floor(log2(magnitude)).
    add     x4, x1, x2      // Unbiased binary64 exponent E = e+h.
    cmp     x4, #1024
    b.ge    Ldy_infinity
    mov     x5, #-1022
    cmp     x4, x5
    b.lt    Ldy_subnormal

    add     x6, x4, #1022
    lsl     x6, x6, #52     // Encoding base; significand supplies implicit 1.
    sub     x5, x2, #52     // Right-shift count for 53 significant bits.
    b       Ldy_shift
Ldy_subnormal:
    mov     x6, #0
    mov     x5, #-1074
    sub     x5, x5, x1      // Express magnitude in units of 2^-1074.
Ldy_shift:
    cmp     x5, #0
    b.le    Ldy_left
    // 1<=shift<=63. Compare the discarded portion with exactly half an ulp.
    mov     x7, #1
    lsl     x7, x7, x5
    sub     x9, x7, #1
    and     x9, x0, x9      // Remainder.
    lsr     x7, x7, #1      // Half.
    lsr     x0, x0, x5      // Retained integer.
    cmp     x9, x7
    cset    x9, hi
    cset    x10, eq
    and     x10, x10, x0    // Tie rounds up only when retained integer is odd.
    orr     x9, x9, x10
    add     x0, x0, x9
    b       Ldy_pack
Ldy_left:
    neg     x5, x5
    lsl     x0, x0, x5      // Exact shift, 0..52.
Ldy_pack:
    add     x0, x6, x0      // Rounding carry naturally advances exponent.
    orr     x0, x0, x3
    fmov    d0, x0
    ret
Ldy_infinity:
    mov     x0, #0x7ff0000000000000
    orr     x0, x0, x3
    fmov    d0, x0
    ret
Ldy_signed_zero:
    fmov    d0, x3          // Preserve negative sign on underflow.
    ret
Ldy_exact_zero:
    fmov    d0, xzr
    ret
Ldy_nan:
    mov     x0, #0x7ff8000000000000
    fmov    d0, x0
    ret

// int padic2_compare_dyadic_units(int64_t a,int64_t ea,int64_t b,int64_t eb)
// x0=a, x1=ea, x2=b, x3=eb. Exponents -1023..1023; return w0=-1/0/+1.
// Compare chosen signed representatives directly, without subtraction or FP.
.globl _padic2_compare_dyadic_units
_padic2_compare_dyadic_units:
    cbz     x0, Lcmp_a_zero
    cbz     x2, Lcmp_b_zero
    eor     x4, x0, x2
    tbnz    x4, #63, Lcmp_signs_differ

    asr     x4, x0, #63     // Common sign mask: 0 or -1.
    eor     x0, x0, x4
    sub     x0, x0, x4      // Unsigned magnitude, including |INT64_MIN|.
    eor     x2, x2, x4
    sub     x2, x2, x4
    clz     x5, x0
    clz     x6, x2
    sub     x7, x1, x5      // e + highest-bit index, minus common constant 63.
    sub     x8, x3, x6
    cmp     x7, x8
    b.ne    Lcmp_heights

    // Equal leading-bit positions: align magnitudes without discarding bits.
    lsl     x0, x0, x5
    lsl     x2, x2, x6
    cmp     x0, x2
    cset    w0, hi
    cset    w1, lo
    sub     w0, w0, w1
    b       Lcmp_apply_sign
Lcmp_heights:
    cset    w0, gt
    cset    w1, lt
    sub     w0, w0, w1
Lcmp_apply_sign:
    cmp     x4, #0
    cneg    w0, w0, ne      // Reverse magnitude order for negative values.
    ret
Lcmp_signs_differ:
    asr     x0, x0, #63
    orr     x0, x0, #1      // Negative a -> -1; positive a -> +1.
    ret
Lcmp_a_zero:
    cmp     x2, #0
    cset    w0, lt
    cset    w1, gt
    sub     w0, w0, w1
    ret
Lcmp_b_zero:
    cmp     x0, #0
    cset    w1, lt
    cset    w0, gt
    sub     w0, w0, w1
    ret

// a^power mod 2^r. x0=a, x1=unsigned power, x2=mask; return x0.
// Low-word wraparound is sufficient; only the final result needs masking.
.globl _padic2_pow_unit
_padic2_pow_unit:
    mov     x3, #1
    cbz     x1, Lpow_done
Lpow_loop:
    tbz     x1, #0, Lpow_skip
    mul     x3, x3, x0
Lpow_skip:
    lsr     x1, x1, #1
    cbz     x1, Lpow_done
    mul     x0, x0, x0
    b       Lpow_loop
Lpow_done:
    and     x0, x3, x2
    ret

// Root of u==1 mod 8. x0=u, x1=output mask (at most 63 bits).
// Newton inverse-root update: z <- z*(3-u*z*z)/2, starting z=1.
// If epsilon=1-u*z*z, epsilon_new=epsilon^2*(3+epsilon)/4.
// Error valuations: 3,4,6,10,18,34,66; word arithmetic caps this at 64.
// The exact even numerator is shifted after low-word truncation, retaining
// 63 quotient bits. Return u*z on the branch 1 mod 4; precision is n-1
// when u is known to n bits. There is no modular inversion of the even 2.
.globl _padic2_sqrt_unit
_padic2_sqrt_unit:
    mov     x2, #1
    mov     x3, #3
    .rept 6
    mul     x4, x2, x2
    msub    x4, x0, x4, x3
    lsr     x4, x4, #1
    mul     x2, x2, x4
    .endr
    mul     x0, x0, x2
    and     x0, x0, x1
    ret

// Bounded rational reconstruction. All state is caller-saved, no stack or FP.
// Shared state: x1=Q, x2=out, x3=a, x4=b, x5=s, x6=t, x10=(Q-1)/2.
// Invariant: a == m*s and b == m*t (mod Q). Remainders are nonnegative;
// signed coefficients alternate signs and have magnitude <= Q/gcd(Q,m).
// With Q<=INT64_MAX the coefficient updates fit a signed 64-bit register.
// Euclidean reduction without division or an explicitly constructed quotient.
// Preconditions: a>=b>0, a<=INT64_MAX, and the reconstruction coefficient
// invariant. Returns (a,s) <- (a%b, s-floor(a/b)*t), leaving (b,t) unchanged.
// Small quotients use direct subtraction; large ones subtract aligned powers
// of two. Coefficient updates follow exactly the same multiples of the divisor.
// Clobbers x8,x9,x11,x13,x14 and flags. x12 stays the fixed reconstruction bound.
.macro padic_rat_reduce a, b, s, t
    sub     \a, \a, \b
    sub     \s, \s, \t
    cmp     \a, \b
    b.lo    Lrat_reduce_done_\@
    sub     \a, \a, \b
    sub     \s, \s, \t
    cmp     \a, \b
    b.lo    Lrat_reduce_done_\@
    sub     \a, \a, \b
    sub     \s, \s, \t
    cmp     \a, \b
    b.lo    Lrat_reduce_done_\@
    clz     x11, \b
Lrat_reduce_bits_\@:
    clz     x9, \a
    sub     x9, x11, x9
    lsl     x13, \b, x9
    cmp     x13, \a
    sub     x14, x9, #1
    csel    x9, x14, x9, hi
    lsr     x14, x13, #1
    csel    x13, x14, x13, hi // Largest shifted divisor <= remainder.
    sub     \a, \a, x13
    lsl     x14, \t, x9
    sub     \s, \s, x14
    cmp     \a, \b
    b.hs    Lrat_reduce_bits_\@
Lrat_reduce_done_\@:
.endm

.macro padic_rat_step
    padic_rat_reduce x3, x4, x5, x6
    mov     x8, x3
    mov     x3, x4
    mov     x4, x8
    mov     x9, x5
    mov     x5, x6
    mov     x6, x9
.endm

// int padic_rational_reconstruct(uint64_t m, uint64_t Q, Pair *out)
// x0=m, x1=Q, x2=out. Strict bounds: 2*b*b<Q and 2*t*t<Q.
.globl _padic_rational_reconstruct
_padic_rational_reconstruct:
    cmp     x1, #3
    b.lo    Lrat_fail
    tbnz    x1, #63, Lrat_fail
    cmp     x0, x1
    b.hs    Lrat_fail
    cbz     x0, Lrat_zero
    mov     x3, x1
    mov     x4, x0
    mov     x5, #0
    mov     x6, #1
    sub     x10, x1, #1
    lsr     x10, x10, #1    // Strict test b*b <= floor((Q-1)/2).
Lrat_loop:
    lsr     x7, x4, #32
    cbnz    x7, Lrat_step   // Large square cannot satisfy the bound; don't overflow.
    mul     x7, x4, x4
    cmp     x7, x10
    b.ls    Lrat_validate
Lrat_step:
    padic_rat_step
    b       Lrat_loop

// int padic2_reconstruct54(uint64_t m, Pair *out): x0=m, x1=out.
// Specialized loop removes the general bound's product and overflow test.
// Alternate register roles for two Euclidean steps: no state-copy MOVs in loop.
.globl _padic2_reconstruct54
_padic2_reconstruct54:
    mov     x2, x1
    mov     x1, #0x0040000000000000 // Q=2^54.
    cmp     x0, x1
    b.hs    Lrat_fail
    cbz     x0, Lrat_zero
    mov     x3, x1
    mov     x4, x0
    mov     x5, #0
    mov     x6, #1
    mov     x10, #0x001fffffffffffff // (Q-1)/2=2^53-1.
    movz    x12, #0x2799
    movk    x12, #0x05a8, lsl #16 // 94906265, exact integer bound.
    cmp     x4, x12
    b.ls    Lrat_validate
Lrat54_loop:
    padic_rat_reduce x3, x4, x5, x6
    cmp     x3, x12
    b.ls    Lrat54_candidate_a
    padic_rat_reduce x4, x3, x6, x5
    cmp     x4, x12
    b.hi    Lrat54_loop
    b       Lrat_validate
Lrat54_candidate_a:
    mov     x4, x3
    mov     x6, x5

Lrat_validate:
    cbz     x6, Lrat_fail
    cmp     x6, #0
    cneg    x11, x6, mi     // Positive denominator magnitude.
    lsr     x7, x11, #32
    cbnz    x7, Lrat_fail
    mul     x7, x11, x11
    cmp     x7, x10
    b.hi    Lrat_fail

    // Validate gcd(b,abs(t))=1 BEFORE division/cancellation. The congruence
    // invariant then also implies gcd(t,Q)=1: any common divisor divides b.
    // Binary GCD avoids further UDIV instructions during validation.
    mov     x13, x4
    mov     x14, x11
    cbz     x13, Lrat_gcd_done_zero
    orr     x7, x13, x14
    tbz     x7, #0, Lrat_fail // Both even -> unreduced candidate.
    rbit    x15, x13
    clz     x15, x15
    lsr     x13, x13, x15
Lrat_gcd_loop:
    rbit    x15, x14
    clz     x15, x15
    lsr     x14, x14, x15
    cmp     x13, x14
    sub     x16, x13, x14
    sub     x17, x14, x13
    csel    x13, x13, x14, lo // min(u,v).
    csel    x14, x17, x16, lo // abs(u-v).
    cbnz    x14, Lrat_gcd_loop
    cmp     x13, #1
    b.ne    Lrat_fail
    b       Lrat_store
Lrat_gcd_done_zero:
    cmp     x14, #1
    b.ne    Lrat_fail
Lrat_store:
    cmp     x6, #0
    cneg    x4, x4, mi      // Normalize denominator sign; no rational reduction.
    stp     x4, x11, [x2]
    mov     w0, #1
    ret
Lrat_zero:
    mov     x3, #1
    stp     xzr, x3, [x2]
    mov     w0, #1
    ret
Lrat_fail:
    stp     xzr, xzr, [x2]
    mov     w0, #0
    ret
