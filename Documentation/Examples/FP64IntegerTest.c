// Native ARM64 oracle; FP instructions are intentionally confined to this test.
#include "FP64Integer.h"
#include <assert.h>
#include <fenv.h>
#include <float.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#pragma STDC FENV_ACCESS ON
_Static_assert(sizeof(double) == 8 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024,
               "Requires binary64");

typedef uint64_t (*Operation)(uint64_t, uint64_t, FP64Rounding, FP64Flags *);
static Operation operations[] = {
    fp64_integer_add, fp64_integer_sub, fp64_integer_mul, fp64_integer_div
};
static const char *names[] = {"add", "sub", "mul", "div"};
static const int modes[] = {FE_TONEAREST, FE_TOWARDZERO, FE_DOWNWARD, FE_UPWARD};
static uint64_t state = UINT64_C(0xd31a729c84e650bf);
static unsigned long checks, tininess_policy_differences;

static uint64_t random_word(void) {
    state ^= state << 13; state ^= state >> 7; state ^= state << 17;
    return state;
}
static double from_bits(uint64_t bits) {
    double value; memcpy(&value, &bits, sizeof value); return value;
}
static uint64_t bits_of(double value) {
    uint64_t bits; memcpy(&bits, &value, sizeof bits); return bits;
}
static int nan_bits(uint64_t bits) {
    return (bits & UINT64_C(0x7fffffffffffffff)) > UINT64_C(0x7ff0000000000000);
}
static FP64Flags native_flags(void) {
    int f = fetestexcept(FE_ALL_EXCEPT);
    return ((f & FE_INVALID) ? FP64_INVALID : 0) |
        ((f & FE_DIVBYZERO) ? FP64_DIVZERO : 0) |
        ((f & FE_OVERFLOW) ? FP64_OVERFLOW : 0) |
        ((f & FE_UNDERFLOW) ? FP64_UNDERFLOW : 0) |
        ((f & FE_INEXACT) ? FP64_INEXACT : 0);
}

static void check(unsigned op, uint64_t a, uint64_t b, FP64Rounding mode) {
    const FP64Flags sentinel = UINT32_C(0x80000000);
    FP64Flags flags = sentinel;
    feclearexcept(FE_ALL_EXCEPT);
    uint64_t actual = operations[op](a, b, mode, &flags);
    assert(fetestexcept(FE_ALL_EXCEPT) == 0); // Software path leaves FP state alone.
    assert(flags & sentinel);
    flags &= ~sentinel;
    volatile double x = from_bits(a), y = from_bits(b), z;
    switch (op) {
        case 0: z = x + y; break;
        case 1: z = x - y; break;
        case 2: z = x * y; break;
        default: z = x / y; break;
    }
    FP64Flags expected_flags = native_flags();
    uint64_t expected = bits_of(z);
    // Some ARM implementations detect tininess before rounding. Our declared
    // policy is after rounding; the exact Fraction oracle checks it separately.
    if ((expected_flags ^ flags) == FP64_UNDERFLOW &&
        (expected_flags & FP64_UNDERFLOW) &&
        (expected & UINT64_C(0x7fffffffffffffff)) == UINT64_C(0x0010000000000000)) {
        expected_flags &= ~FP64_UNDERFLOW;
        ++tininess_policy_differences;
    }
    if ((actual != expected && !(nan_bits(actual) && nan_bits(expected))) ||
        flags != expected_flags) {
        fprintf(stderr, "%s mode=%d a=%016" PRIx64 " b=%016" PRIx64
                " got=%016" PRIx64 "/%02x expected=%016" PRIx64 "/%02x\n",
                names[op], mode, a, b, actual, flags, expected, expected_flags);
        exit(1);
    }
    ++checks;
}

static void policies(void) {
    const uint64_t one = UINT64_C(0x3ff0000000000000);
    const uint64_t quiet = UINT64_C(0xfff8000000012345);
    const uint64_t signaling = UINT64_C(0x7ff0000000054321);
    for (unsigned op = 0; op < 4; ++op) {
        FP64Flags f = 0;
        assert(operations[op](quiet, signaling, FP64_NEAREST_EVEN, &f) == quiet);
        assert(f == FP64_INVALID);
        f = 0;
        assert(operations[op](one, signaling, FP64_NEAREST_EVEN, &f) ==
               (signaling | UINT64_C(0x0008000000000000)));
        assert(f == FP64_INVALID);
        f = 0;
        assert(operations[op](one, quiet, FP64_NEAREST_EVEN, &f) == quiet);
        assert(f == 0);
    }
    FP64Flags f = FP64_DIVZERO;
    assert(fp64_integer_mul(one, one, FP64_NEAREST_EVEN, &f) == one);
    assert(f == FP64_DIVZERO);
    // Halfway below the minimum normal rounds up to an exact normal encoding:
    // INEXACT, but no UNDERFLOW under our after-rounding policy.
    f = 0;
    assert(fp64_integer_mul(UINT64_C(0x0010000000000000),
                            UINT64_C(0x3fefffffffffffff), FP64_NEAREST_EVEN, &f) ==
           UINT64_C(0x0010000000000000));
    assert(f == FP64_INEXACT);
    puts("PASS: NaN payload/signaling policy, sticky flags, tininess after rounding.");
}

int main(void) {
    fenv_t saved;
    assert(fegetenv(&saved) == 0);
    assert(fesetenv(FE_DFL_ENV) == 0);
    policies();
    static const uint64_t edges[] = {
        0, 1, 2, 3, UINT64_C(0x0007ffffffffffff),
        UINT64_C(0x000ffffffffffffe), UINT64_C(0x000fffffffffffff),
        UINT64_C(0x0010000000000000), UINT64_C(0x0010000000000001),
        UINT64_C(0x001fffffffffffff), UINT64_C(0x0020000000000000),
        UINT64_C(0x3c90000000000000), UINT64_C(0x3ca0000000000000),
        UINT64_C(0x3cb0000000000000), UINT64_C(0x3fd5555555555555),
        UINT64_C(0x3fdfffffffffffff), UINT64_C(0x3fe0000000000000),
        UINT64_C(0x3fefffffffffffff), UINT64_C(0x3ff0000000000000),
        UINT64_C(0x3ff0000000000001), UINT64_C(0x3ff0000000000002),
        UINT64_C(0x3fffffffffffffff), UINT64_C(0x4000000000000000),
        UINT64_C(0x4008000000000000), UINT64_C(0x41a0000002000000),
        UINT64_C(0x4350000000000000), UINT64_C(0x7fdfffffffffffff),
        UINT64_C(0x7fe0000000000000), UINT64_C(0x7feffffffffffffe),
        UINT64_C(0x7fefffffffffffff), UINT64_C(0x7ff0000000000000),
        UINT64_C(0x7ff8000000001234), UINT64_C(0x7ff0000000004321)
    };
    size_t count = sizeof edges / sizeof *edges;
    for (unsigned mode = 0; mode < 4; ++mode) {
        assert(fesetround(modes[mode]) == 0);
        for (size_t i = 0; i < count; ++i)
            for (size_t j = 0; j < count; ++j)
                for (unsigned signs = 0; signs < 4; ++signs)
                    for (unsigned op = 0; op < 4; ++op)
                        check(op, edges[i] ^ ((uint64_t)(signs & 1) << 63),
                              edges[j] ^ ((uint64_t)(signs >> 1) << 63), mode);
        for (unsigned i = 0; i < 100000; ++i) {
            uint64_t a = random_word(), b = random_word();
            for (unsigned op = 0; op < 4; ++op) check(op, a, b, mode);
            // Exercise close cancellation and the exact/far alignment boundary.
            uint64_t finite = a & UINT64_C(0xffefffffffffffff);
            check(1, finite, finite ^ (b & 1023), mode);
            unsigned field = (unsigned)((finite >> 52) & 2047);
            if (field > 66) {
                uint64_t distant = (finite & UINT64_C(0x800fffffffffffff)) |
                    ((uint64_t)(field - 64 - (i & 1)) << 52);
                check(0, finite, distant, mode);
                check(1, finite, distant, mode);
            }
        }
    }
    assert(fesetenv(&saved) == 0);
    printf("PASS: %lu native result/flag comparisons, all four operations and rounding modes.\n", checks);
    printf("INFO: %lu native before-rounding tininess differences (declared policy).\n",
           tininess_policy_differences);
    return 0;
}
