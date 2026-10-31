#ifndef FP64_INTEGER_H
#define FP64_INTEGER_H

#include <stdint.h>

typedef enum {
    FP64_NEAREST_EVEN = 0,
    FP64_TOWARD_ZERO = 1,
    FP64_DOWNWARD = 2,
    FP64_UPWARD = 3
} FP64Rounding;

typedef uint32_t FP64Flags;
enum {
    FP64_INVALID = 1u << 0,
    FP64_DIVZERO = 1u << 1,
    FP64_OVERFLOW = 1u << 2,
    FP64_UNDERFLOW = 1u << 3,
    FP64_INEXACT = 1u << 4
};

// Binary64 interchange bits in/out; no double arguments, FP register transfers,
// FP arithmetic, or FPCR dependence. Gradual underflow, tininess AFTER rounding.
// mode must be one of the four values above; flags must point to valid storage.
// Exceptions accumulate in *flags; hardware FP exception state is untouched.
// Signed zeros and infinities follow IEEE arithmetic. NaNs: quiet and propagate
// the first NaN operand's sign/payload; either signaling NaN raises INVALID.
// Invalid operations without a NaN input return positive 0x7ff8000000000000.
// Each call rounds once. These are separate from the p-adic residue operations.
uint64_t fp64_integer_add(uint64_t a, uint64_t b, FP64Rounding mode, FP64Flags *flags);
uint64_t fp64_integer_sub(uint64_t a, uint64_t b, FP64Rounding mode, FP64Flags *flags);
uint64_t fp64_integer_mul(uint64_t a, uint64_t b, FP64Rounding mode, FP64Flags *flags);
// Division refines a real reciprocal with the shared integer MUL/UMULH kernel,
// multiplies by the numerator, and corrects from an exact integer remainder.
// The reciprocal is internal fixed point; there is no intermediate FP rounding.
uint64_t fp64_integer_div(uint64_t a, uint64_t b, FP64Rounding mode, FP64Flags *flags);

#endif
