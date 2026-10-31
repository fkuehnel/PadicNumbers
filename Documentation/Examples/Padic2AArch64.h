#ifndef PADIC2_AARCH64_H
#define PADIC2_AARCH64_H

#include <stdint.h>

// Shared unsigned 64-by-64 -> 128-bit product, implemented by MUL/UMULH.
// No modular mask or FP rounding; Darwin ARM64 returns low/high words in x0/x1.
__uint128_t integer_mul_wide(uint64_t a, uint64_t b);

enum {
    PADIC2_FINITE = 0,
    PADIC2_EXACT_ZERO = 1,
    PADIC2_NONFINITE = 2
};

// Decoded fields, NOT the proposed packed 64-bit encoding.
// FINITE: residue * 2^exponent modulo the precision selected by the mask.
// EXACT_ZERO merges +0.0 and -0.0; NONFINITE rejects infinities and NaNs.
// For both special statuses, residue and exponent are zero placeholders.
// The caller retains precision and handles exponent limits when packing.
typedef struct {
    uint64_t residue;
    int64_t exponent;
    uint64_t status;
} Padic2Decoded;

// mask = 2^r-1, 1 <= r <= 64; use UINT64_MAX for r=64.
void padic2_from_double(double value, uint64_t mask, Padic2Decoded *out);

// Choose the centered signed r-bit representative s and convert s * 2^exponent.
// r=1..64; high residue bits are ignored. This is NOT rational reconstruction.
// Fixed round-to-nearest, ties-to-even; gradual underflow; overflow to infinity.
// Uses integer bit packing, independent of FPCR; does not raise FP exceptions.
// EXACT_ZERO -> +0.0; NONFINITE/unknown status or invalid r -> quiet NaN.
// FINITE residue zero selects +0.0; it does not certify an underlying exact zero.
// Unchanged finite FP64 sources roundtrip at r>=54, including all subnormals;
// the source -0.0 sign was deliberately discarded by padic2_from_double.
double padic2_to_double_dyadic(const Padic2Decoded *value, uint64_t r);

uint64_t padic2_add(uint64_t a,uint64_t b,uint64_t mask,int64_t ea,int64_t eb);
uint64_t padic2_sub(uint64_t a,uint64_t b,uint64_t mask,int64_t ea,int64_t eb);
uint64_t padic2_neg(uint64_t a,uint64_t unused,uint64_t mask);
uint64_t padic2_mul(uint64_t a,uint64_t b,uint64_t mask);
uint64_t padic2_div(uint64_t a,uint64_t odd_b,uint64_t mask);
uint64_t padic2_align(uint64_t m,uint64_t shift,uint64_t mask);
uint64_t padic2_ctz(uint64_t m);

// Compare exact signed dyadics a*2^ea and b*2^eb using integers only.
// Signed units may be zero; exponents must be in -1023..1023.
// Returns -1, 0 or +1. This compares representatives, not p-adic balls.
int padic2_compare_dyadic_units(int64_t a,int64_t ea,int64_t b,int64_t eb);

// Unsigned integer power modulo 2^r (r=1..64), by repeated squaring.
uint64_t padic2_pow_unit(uint64_t a,uint64_t power,uint64_t mask);

// Precondition: u == 1 mod 8, known modulo 2^n for 3<=n<=64.
// Returns the root branch 1 mod 4, masked to at most n-1 known bits.
// Six inverse-square-root updates; only integer products and exact /2 shifts.
uint64_t padic2_sqrt_unit(uint64_t u,uint64_t mask);

typedef struct {
    int64_t numerator;
    int64_t denominator;
} PadicRationalPair;

// Strict symmetric rational reconstruction: |u|, v < sqrt(modulus/2),
// gcd(u,v)=gcd(v,modulus)=1, and u == m*v (mod modulus), with v>0.
// Return 1 on success, 0 on no bounded rational or invalid input. Failure
// writes {0,0}; no cancellation or residue fallback can fabricate a success.
// Requires a valid output pointer; accepts 3 <= modulus <= INT64_MAX and m<modulus.
// A success certifies the unique bounded candidate, not an unknown source value.
// Both kernels avoid hardware division: subtract small divisor multiples,
// then use CLZ-aligned power-of-two reductions with matching coefficient updates.
// GCD validation also uses shifts and subtraction; no FP operations or stack.
int padic_rational_reconstruct(uint64_t m,uint64_t modulus,PadicRationalPair *out);

// Same contract for modulus=2^54; 0 <= m < 2^54. Uses the exact constant
// bound floor(sqrt((2^54-1)/2))=94906265 in its Euclidean loop.
int padic2_reconstruct54(uint64_t m,PadicRationalPair *out);

#endif
