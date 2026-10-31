#ifndef PADIC2_PACKED64_H
#define PADIC2_PACKED64_H

#include <stdint.h>

typedef uint64_t Padic64;
// A software model of a caller-owned/thread-local sticky exception register.
// Clear explicitly by assigning zero. Flags never supply per-value precision.
typedef uint32_t Padic64Flags;
enum {
    PADIC64_INVALID = 1u << 0,
    PADIC64_DIVZERO = 1u << 1,
    PADIC64_PRECISION_LOST = 1u << 2,
    PADIC64_INSUFFICIENT_PRECISION = 1u << 3,
    PADIC64_EXPONENT_RANGE = 1u << 4,
    PADIC64_FP_OVERFLOW = 1u << 5
};

// Bits 63..53: signed 11-bit valuation, -1023..1023.
// Bits 52..0: unit >> 1; the odd low bit is implicit. Relative precision is 54.
// Exponent -1024 is reserved. Its payload selects the special value below.
// Other reserved payloads are invalid. No separate status field in the word.
#define PADIC64_ZERO UINT64_C(0x8000000000000000)
#define PADIC64_NAN  UINT64_C(0x8000000000000001)
#define PADIC64_NEEDS_PRECISION UINT64_C(0x8000000000000002)
#define PADIC64_POS_INFINITY UINT64_C(0x8000000000000003)
#define PADIC64_NEG_INFINITY UINT64_C(0x8000000000000004)
#define PADIC64_RESIDUE_MASK ((UINT64_C(1) << 54) - 1)

// Nonzero finite words always certify all 54 relative bits. If cancellation
// loses any, return NEEDS_PRECISION; never fill unknown digits with zeros.
// Recompute from retained sources with more precision; clearing flags is not
// a repair. Independent input balls are assumed even when their words match.
// flags must point to valid storage. Operations OR exceptions into *flags.
// FP interchange preserves both infinities. NaNs are canonicalized to quiet
// PADIC64_NAN: importing sNaN raises INVALID; qNaN propagates without raising it.
// NaN payload/sign and signed zero are not preserved. Finite range is unchanged.
// Infinities are interchange tags, not elements of Q_2. Wrapper arithmetic uses
// extended signed-dyadic conventions: finite signs mean centered representatives.
// Opposite infinities in addition, equal infinities in subtraction, 0*infinity
// and infinity/infinity raise INVALID. Finite/infinity gives unsigned exact zero.
// Finite/zero retains the p-adic INVALID|DIVZERO policy, not IEEE signed infinity.
Padic64 padic64_from_double(double value, Padic64Flags *flags);
double padic64_to_double_dyadic(Padic64 value, Padic64Flags *flags);
Padic64 padic64_add(Padic64 a, Padic64 b, Padic64Flags *flags);
Padic64 padic64_sub(Padic64 a, Padic64 b, Padic64Flags *flags);
Padic64 padic64_neg(Padic64 a, Padic64Flags *flags);
Padic64 padic64_mul(Padic64 a, Padic64 b, Padic64Flags *flags);
Padic64 padic64_div(Padic64 a, Padic64 b, Padic64Flags *flags);

// Signed integer powers; negative powers use modular inversion. Nonzero a^0=1.
// Exact 0^0 is INVALID; negative powers of exact zero are INVALID|DIVZERO.
// Exponent products are range checked, including an INT64_MIN power.
// Infinity^0=1; negative powers of infinity give unsigned zero. NaN propagates
// even at exponent zero (this is not the real libm pow contract).
Padic64 padic64_pow(Padic64 a,int64_t power,Padic64Flags *flags);

// 2-adic square root: nonzero input needs even valuation and unit == 1 mod 8.
// Select the unit-root branch == 1 mod 4, not a real-positive square root.
// Exact zero returns exact zero; nonsquares return NaN with INVALID.
// +Infinity passes through; -Infinity raises INVALID. Quiet NaN propagates.
// An ordinary 54-bit input yields only 53 root bits, so sqrt returns
// NEEDS_PRECISION with PRECISION_LOST|INSUFFICIENT_PRECISION.
Padic64 padic64_sqrt(Padic64 a,Padic64Flags *flags);
// To obtain a full 54-bit root, supply a source-certified unit modulo 2^55.
// It must be <2^55 and agree with a's low 54 bits. Do not invent the extra bit.
// Exact zero requires refined_unit=0. Mismatched refinements are INVALID.
Padic64 padic64_sqrt_refined(Padic64 a,uint64_t refined_unit,Padic64Flags *flags);

// Mutually exclusive comparison conditions, returned per instruction.
// These are NOT sticky exception bits; flags still accumulates exceptions.
typedef enum {
    PADIC64_CMP_LT = 1,
    PADIC64_CMP_EQ = 2,
    PADIC64_CMP_GT = 4,
    PADIC64_CMP_UNORDERED = 8
} Padic64Comparison;

// Order the centered signed-dyadic representatives, without FP conversion.
// EQ does not certify equality of the underlying unknown p-adic values.
// Infinities bound all finite representatives. Quiet NaN -> UNORDERED without
// a new exception; malformed tags -> UNORDERED + INVALID. NEEDS_PRECISION -> UNORDERED +
// INSUFFICIENT_PRECISION. Successful comparisons leave exception flags intact.
Padic64Comparison padic64_compare_dyadic(Padic64 a,Padic64 b,Padic64Flags *flags);

typedef struct {
    int64_t numerator;
    int64_t denominator;
    int64_t exponent;
} Padic64Rational;

// Reconstruct the normalized unit as u/v; the complete candidate is (u/v)*2^e.
// Return 1 on a bounded candidate, 0 on failure (output fields all zero).
// A candidate is not proof of the original source without certified size bounds.
// Exact zero -> {0,1,0}; no candidate -> INSUFFICIENT_PRECISION. Infinity and
// malformed tags -> INVALID; quiet NaN propagates failure without a new flag.
// This does not perform FP conversion, change the word, or fall back to a residue.
int padic64_reconstruct(Padic64 value,Padic64Rational *out,Padic64Flags *flags);

#endif
