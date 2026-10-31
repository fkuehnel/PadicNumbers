// Integer-only IEEE binary64 arithmetic alongside the p-adic ARM64 kernels.
// Build this translation unit with -mgeneral-regs-only on ARM64; see FP64Integer.md.
#include "FP64Integer.h"
#include "Padic2AArch64.h"

typedef __uint128_t Wide;

#define SIGN UINT64_C(0x8000000000000000)
#define INF UINT64_C(0x7ff0000000000000)
#define FRAC UINT64_C(0x000fffffffffffff)
#define HIDDEN UINT64_C(0x0010000000000000)
#define QUIET UINT64_C(0x0008000000000000)
#define NAN_BITS (INF | QUIET)

typedef struct {
    uint64_t magnitude; // 53 bits, including leading 1; sign is kept separately.
    int exponent;       // value magnitude = magnitude * 2^exponent.
} Finite;

static int is_nan(uint64_t a) { return (a & ~SIGN) > INF; }
static int is_inf(uint64_t a) { return (a & ~SIGN) == INF; }
static int is_zero(uint64_t a) { return (a & ~SIGN) == 0; }

static uint64_t propagate_nan(uint64_t a, uint64_t b, FP64Flags *flags) {
    if ((is_nan(a) && !(a & QUIET)) || (is_nan(b) && !(b & QUIET)))
        *flags |= FP64_INVALID;
    return (is_nan(a) ? a : b) | QUIET;
}

static uint64_t invalid(FP64Flags *flags) {
    *flags |= FP64_INVALID;
    return NAN_BITS;
}

// Nonzero finite inputs only. Normalize subnormals without losing source bits.
static Finite unpack(uint64_t a) {
    unsigned field = (unsigned)((a >> 52) & 2047);
    uint64_t m = a & FRAC;
    if (field) return (Finite){m | HIDDEN, (int)field - 1075};
    unsigned shift = (unsigned)__builtin_clzll(m) - 11;
    return (Finite){m << shift, -1074 - (int)shift};
}

static uint64_t overflow(uint64_t sign, FP64Rounding mode, FP64Flags *flags) {
    *flags |= FP64_OVERFLOW | FP64_INEXACT;
    int infinity = mode == FP64_NEAREST_EVEN ||
        (mode == FP64_UPWARD && !sign) || (mode == FP64_DOWNWARD && sign);
    return sign | (infinity ? INF : INF - 1);
}

// Round (m + t)*2^e, with m>0 and either t=0 or 0<t<1 (tail=1).
// Callers with a tail retain at least two low guard positions at the normal
// rounding boundary, so t's nonzeroness suffices; its magnitude is not needed.
// Subnormal alignment and significand reduction happen in this SAME rounding.
static uint64_t round_pack(uint64_t sign, Wide m, int e, int tail,
                           FP64Rounding mode, FP64Flags *flags) {
    uint64_t hi = (uint64_t)(m >> 64);
    int h = hi ? 127 - __builtin_clzll(hi) : 63 - __builtin_clzll((uint64_t)m);
    int top = e + h;
    if (top > 1023) return overflow(sign, mode, flags);
    int unit = top >= -1022 ? top - 52 : -1074;
    int shift = unit - e;
    uint64_t retained;
    int inexact = tail;
    int half_compare = -1;
    if (shift > 0) {
        Wide remainder;
        if (shift < 128) {
            retained = (uint64_t)(m >> shift);
            remainder = m & (((Wide)1 << shift) - 1);
            Wide half = (Wide)1 << (shift - 1);
            half_compare = (remainder > half) - (remainder < half);
        } else {
            retained = 0;
            remainder = m;
            if (shift == 128) {
                Wide half = (Wide)1 << 127;
                half_compare = (m > half) - (m < half);
            }
        }
        inexact |= remainder != 0;
        if (half_compare == 0 && tail) half_compare = 1;
    } else {
        // This branch is exact: only cancellation or a small exact result can
        // require left alignment. The callers never supply a tail here.
        retained = (uint64_t)(m << -shift);
    }
    int increment = 0;
    if (inexact) {
        *flags |= FP64_INEXACT;
        if (mode == FP64_NEAREST_EVEN)
            increment = half_compare > 0 || (half_compare == 0 && (retained & 1));
        else
            increment = (mode == FP64_UPWARD && !sign) ||
                        (mode == FP64_DOWNWARD && sign);
    }
    retained += (unsigned)increment;
    if (retained == (HIDDEN << 1)) {
        retained >>= 1;
        ++unit;
    }
    if (retained < HIDDEN) {
        if (inexact) *flags |= FP64_UNDERFLOW;
        return sign | retained; // Subnormal or signed zero; tininess after rounding.
    }
    if (unit + 52 > 1023) return overflow(sign, mode, flags);
    return sign | ((uint64_t)(unit + 1075) << 52) | (retained & FRAC);
}

static uint64_t addsub(uint64_t a, uint64_t b, int subtract,
                       FP64Rounding mode, FP64Flags *flags) {
    // Preserve the original NaN sign/payload even for subtraction.
    if (is_nan(a) || is_nan(b)) return propagate_nan(a, b, flags);
    if (subtract) b ^= SIGN;
    if (is_inf(a) || is_inf(b)) {
        if (is_inf(a) && is_inf(b) && ((a ^ b) & SIGN)) return invalid(flags);
        return is_inf(a) ? a : b;
    }
    if (is_zero(a) && is_zero(b))
        return ((a ^ b) & SIGN) ? (mode == FP64_DOWNWARD ? SIGN : 0) : a;
    if (is_zero(a)) return b;
    if (is_zero(b)) return a;

    // Positive binary64 encodings are ordered by magnitude, including subnormals.
    if ((a & ~SIGN) < (b & ~SIGN)) {
        uint64_t swap = a; a = b; b = swap;
    }
    uint64_t sign = a & SIGN;
    int opposite = ((a ^ b) & SIGN) != 0;
    Finite x = unpack(a), y = unpack(b);
    int gap = x.exponent - y.exponent; // Nonnegative after magnitude ordering.
    if (gap <= 64) {
        // Exact alignment fits in 118 bits, including the sum carry. This also
        // covers every cancellation case requiring many normalization shifts.
        Wide large = (Wide)x.magnitude << gap;
        Wide m = opposite ? large - y.magnitude : large + y.magnitude;
        if (!m) return mode == FP64_DOWNWARD ? SIGN : 0;
        return round_pack(sign, m, y.exponent, 0, mode, flags);
    }
    // The smaller magnitude is strictly between 0 and one guard-position unit.
    // For subtraction, floor(L-small)=L-1 with a positive fractional tail;
    // addition has floor(L+small)=L with a positive fractional tail. No severe
    // cancellation is possible, so three guard positions suffice here.
    Wide m = ((Wide)x.magnitude << 3) - (unsigned)opposite;
    return round_pack(sign, m, x.exponent - 3, 1, mode, flags);
}

uint64_t fp64_integer_add(uint64_t a, uint64_t b, FP64Rounding mode, FP64Flags *flags) {
    return addsub(a, b, 0, mode, flags);
}

uint64_t fp64_integer_sub(uint64_t a, uint64_t b, FP64Rounding mode, FP64Flags *flags) {
    return addsub(a, b, 1, mode, flags);
}

uint64_t fp64_integer_mul(uint64_t a, uint64_t b, FP64Rounding mode, FP64Flags *flags) {
    if (is_nan(a) || is_nan(b)) return propagate_nan(a, b, flags);
    uint64_t sign = (a ^ b) & SIGN;
    if (is_inf(a) || is_inf(b)) {
        if (is_zero(a) || is_zero(b)) return invalid(flags);
        return sign | INF;
    }
    if (is_zero(a) || is_zero(b)) return sign;
    Finite x = unpack(a), y = unpack(b);
    Wide m = integer_mul_wide(x.magnitude, y.magnitude);
    return round_pack(sign, m, x.exponent + y.exponent, 0, mode, flags);
}

// d is a normalized 53-bit significand: 2^52 <= d < 2^53 (odd or even).
// Encode the real reciprocal as r/2^115. The tutorial's seed 2^-53 is
// therefore r=2^62; the exact scaled reciprocal T=2^115/d lies in (2^62,2^63].
// Newton: r <- r + r*(1-d*r/2^115), rounding both retained products down.
// The residual is kept with 63 fractional bits so every product fits 128 bits.
// Each update stays below T and loses less than two integer units relative
// to exact Newton. Six updates give 0 <= T-r < 6; see FP64Integer.md.
static uint64_t reciprocal_significand(uint64_t d) {
    const Wide scale = (Wide)1 << 115;
    uint64_t r = UINT64_C(1) << 62;
    for (unsigned i = 0; i < 6; ++i) {
        Wide residual = scale - integer_mul_wide(d, r);
        uint64_t e = (uint64_t)(residual >> 52);
        r += (uint64_t)(integer_mul_wide(r, e) >> 63);
    }
    return r;
}

// Produce floor(a*2^56/d) and its exact remainder for normalized significands.
// One numerator-times-reciprocal product estimates the quotient. Because
// T-r<6 and a<2^53, the unrounded estimate is less than 6/64 below a*2^56/d.
// Its floor is therefore correct or one too small. One exact q*d product
// certifies it; a single correction supplies the exact quotient and sticky bit.
static uint64_t divide_significands(uint64_t a, uint64_t d, uint64_t *remainder) {
    uint64_t r = reciprocal_significand(d);
    uint64_t q = (uint64_t)(integer_mul_wide(a, r) >> 59);
    Wide rem = ((Wide)a << 56) - integer_mul_wide(q, d);
    if (rem >= d) {
        ++q;
        rem -= d;
    }
    *remainder = (uint64_t)rem;
    return q;
}

uint64_t fp64_integer_div(uint64_t a, uint64_t b, FP64Rounding mode, FP64Flags *flags) {
    if (is_nan(a) || is_nan(b)) return propagate_nan(a, b, flags);
    uint64_t sign = (a ^ b) & SIGN;
    if ((is_inf(a) && is_inf(b)) || (is_zero(a) && is_zero(b))) return invalid(flags);
    if (is_inf(a)) return sign | INF;
    if (is_inf(b)) return sign;
    if (is_zero(b)) {
        *flags |= FP64_DIVZERO;
        return sign | INF;
    }
    if (is_zero(a)) return sign;
    Finite x = unpack(a), y = unpack(b);

    // Retain 56 fractional quotient bits, then round only once to binary64.
    uint64_t remainder;
    uint64_t q = divide_significands(x.magnitude, y.magnitude, &remainder);
    return round_pack(sign, q, x.exponent - y.exponent - 56,
                      remainder != 0, mode, flags);
}
