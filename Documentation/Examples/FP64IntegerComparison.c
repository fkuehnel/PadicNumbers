// Side-by-side bit demo. Native FP instructions are reference/presentation only.
#include "FP64Integer.h"
#include "Padic2Packed64.h"
#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

typedef uint64_t (*IntegerOp)(uint64_t, uint64_t, FP64Rounding, FP64Flags *);
typedef Padic64 (*PadicOp)(Padic64, Padic64, Padic64Flags *);

static double from_bits(uint64_t bits) {
    double value; memcpy(&value, &bits, sizeof value); return value;
}
static uint64_t bits_of(double value) {
    uint64_t bits; memcpy(&bits, &value, sizeof bits); return bits;
}
static void record(const char *label, uint64_t bits, uint32_t flags) {
    printf("  %-18s 0x%016" PRIx64 "  %a  flags=0x%02x\n",
           label, bits, from_bits(bits), flags);
}
static void compare(const char *name, uint64_t a, uint64_t b,
                    IntegerOp integer_op, PadicOp padic_op, unsigned op) {
    FP64Flags fp_flags = 0;
    uint64_t result = integer_op(a, b, FP64_NEAREST_EVEN, &fp_flags);
    Padic64Flags padic_flags = 0;
    Padic64 pa = padic64_from_double(from_bits(a), &padic_flags);
    Padic64 pb = padic64_from_double(from_bits(b), &padic_flags);
    Padic64 pc = padic_op(pa, pb, &padic_flags);
    uint64_t padic_result = bits_of(padic64_to_double_dyadic(pc, &padic_flags));
    volatile double x = from_bits(a), y = from_bits(b), native;
    switch (op) {
        case 0: native = x + y; break;
        case 1: native = x - y; break;
        case 2: native = x * y; break;
        default: native = x / y; break;
    }
    assert(result == bits_of(native));
    printf("%s\n  inputs             0x%016" PRIx64 "  0x%016" PRIx64 "\n", name, a, b);
    record("p-adic export", padic_result, padic_flags);
    record("integer FP64", result, fp_flags);
    printf("  native FP64        0x%016" PRIx64 "  %a\n\n", bits_of(native), (double)native);
}
int main(void) {
    uint64_t one = UINT64_C(0x3ff0000000000000);
    uint64_t large = UINT64_C(0x4350000000000000);
    uint64_t m = UINT64_C(0x41a0000002000000);
    compare("1 + 1", one, one, fp64_integer_add, padic64_add, 0);
    compare("1 + 2^54", one, large, fp64_integer_add, padic64_add, 0);
    compare("1 - 2^54", one, large, fp64_integer_sub, padic64_sub, 1);
    compare("(2^27 + 1)^2", m, m, fp64_integer_mul, padic64_mul, 2);
    compare("1 / 3", one, UINT64_C(0x4008000000000000), fp64_integer_div, padic64_div, 3);
    puts("PASS: integer FP64 matches native FP64 bits in all five examples.");
    puts("Flag bit definitions are separate: FP64Integer.h versus Padic2Packed64.h.");
    return 0;
}
