// Inspect private fixed-point invariants against independent exact integer
// division. The production core is included only in this test translation unit.
#include "FP64Integer.c"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>

static uint64_t state = UINT64_C(0x4b196d82f3a75ce1);
static unsigned long checks, corrected, uncorrected;

static uint64_t random_word(void) {
    state ^= state << 13; state ^= state >> 7; state ^= state << 17;
    return state;
}

static void check(uint64_t a, uint64_t d) {
    const Wide scale = (Wide)1 << 115;
    uint64_t r = reciprocal_significand(d);
    Wide dr = (Wide)d * r;
    assert(dr <= scale);
    assert(scale - dr < (Wide)6 * d); // 0 <= exact scaled reciprocal - r < 6.
    Wide numerator = (Wide)a << 56;
    uint64_t expected = (uint64_t)(numerator / d);
    uint64_t expected_rem = (uint64_t)(numerator % d);
    uint64_t estimate = (uint64_t)(((Wide)a * r) >> 59);
    assert(estimate <= expected && expected - estimate <= 1);
    corrected += estimate != expected;
    uncorrected += estimate == expected;
    uint64_t rem;
    uint64_t actual = divide_significands(a, d, &rem);
    assert(actual == expected && rem == expected_rem);
    assert(rem < d && (Wide)actual * d + rem == numerator);
    ++checks;
}

int main(void) {
    // Exact powers of two, both ends of normalization, odd/even denominators,
    // exact quotients, and adjacent significands that expose one-unit corrections.
    for (uint64_t offset = 0; offset < 4096; ++offset) {
        uint64_t denominators[] = {HIDDEN + offset, (HIDDEN << 1) - 1 - offset};
        for (unsigned i = 0; i < 2; ++i) {
            uint64_t d = denominators[i];
            check(HIDDEN, d);
            check((HIDDEN << 1) - 1, d);
            check(d, d);
            if (d > HIDDEN) check(d - 1, d);
            if (d + 1 < (HIDDEN << 1)) check(d + 1, d);
        }
    }
    for (unsigned i = 0; i < 100000; ++i) {
        uint64_t a = HIDDEN | (random_word() & FRAC);
        uint64_t d = HIDDEN | (random_word() & FRAC);
        check(a, d);
        check(d, d);
    }
    assert(corrected && uncorrected);
    printf("PASS: %lu reciprocal bounds and exact quotient/remainder checks "
           "(%lu corrected, %lu already exact).\n", checks, corrected, uncorrected);
    return 0;
}
