// Compare FP64 1/3 import with packed modular 1/3 on ARM64 macOS.
// From the repository root:
// clang -Wall -Wextra -Werror -O2 -fsanitize=undefined \
//   Documentation/Examples/Padic2AArch64.s Documentation/Examples/Padic2Packed64.c \
//   Documentation/Examples/Padic2ThirdComparison.c -o /tmp/padic-third-comparison
// /tmp/padic-third-comparison
#include "Padic2Packed64.h"
#include <assert.h>
#include <float.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

_Static_assert(sizeof(double)==8 && FLT_RADIX==2 && DBL_MANT_DIG==53 &&
               DBL_MAX_EXP==1024 && DBL_MIN_EXP==-1021, "Requires binary64");

static uint64_t fp_bits(double value) {
    uint64_t bits;
    memcpy(&bits,&value,sizeof bits);
    return bits;
}

static void print_bits(const char *label,uint64_t bits,unsigned width) {
    printf("  %s: ",label);
    for(unsigned i=width;i>0;i--) putchar('0'+(int)((bits>>(i-1))&1));
    putchar('\n');
}

static double record(const char *label,Padic64 value,Padic64Comparison expected) {
    uint64_t payload=value&((UINT64_C(1)<<53)-1),unit=(payload<<1)|1;
    int64_t e=(int64_t)(value>>53);
    if(e>=1024) e-=2048;
    int64_t centered=unit<(UINT64_C(1)<<53)?(int64_t)unit:
                     (int64_t)unit-(INT64_C(1)<<54);
    Padic64Flags flags=0;
    double back=padic64_to_double_dyadic(value,&flags);
    Padic64Comparison comparison=padic64_compare_dyadic(value,PADIC64_ZERO,&flags);
    assert(comparison==expected && flags==0);
    uint64_t bits=fp_bits(back),fraction=bits&((UINT64_C(1)<<52)-1);
    uint64_t significand=(UINT64_C(1)<<52)|fraction;

    printf("%s\n",label);
    printf("  packed word: 0x%016" PRIx64 "\n",value);
    printf("  packed payload (53 bits): 0x%014" PRIx64 "\n",payload);
    print_bits("packed payload binary",payload,53);
    printf("  decoded odd unit (54 bits): 0x%014" PRIx64 "\n",unit);
    print_bits("decoded odd unit binary",unit,54);
    printf("  valuation e: %" PRId64 "\n",e);
    printf("  centered signed unit s: %" PRId64 "\n",centered);
    printf("  exported FP64: %.17g (%a)\n",back,back);
    printf("  exported FP64 bits: 0x%016" PRIx64 "\n",bits);
    printf("  FP64 sign: %" PRIu64 ", unbiased exponent: %d\n",
           bits>>63,(int)((bits>>52)&2047)-1023);
    printf("  FP64 significand (53 bits, implicit leading 1 included): 0x%014" PRIx64 "\n",
           significand);
    print_bits("FP64 significand binary",significand,53);
    printf("  comparison with zero: %s; flags: 0x%x\n\n",
           comparison==PADIC64_CMP_GT?"GT":"LT",(unsigned)flags);
    return back;
}

int main(void) {
    // Volatile operands force a native FP division instead of constant folding.
    volatile double one=1.0,three=3.0;
    double fp=one/three;
    assert(fp_bits(fp)==UINT64_C(0x3fd5555555555555)); // Nearest-even FP64.
    Padic64Flags direct_flags=0,division_flags=0;
    Padic64 direct=padic64_from_double(fp,&direct_flags);
    Padic64 a=padic64_from_double(one,&division_flags);
    Padic64 b=padic64_from_double(three,&division_flags);
    Padic64 modular=padic64_div(a,b,&division_flags);
    assert(direct_flags==0 && division_flags==0);

    double direct_back=record("A: native FP64 1/3 -> packed -> dyadic export",
                              direct,PADIC64_CMP_GT);
    double modular_back=record("B: packed(1) / packed(3) -> dyadic export",
                               modular,PADIC64_CMP_LT);
    uint64_t fraction_mask=(UINT64_C(1)<<52)-1;
    assert(fp_bits(direct_back)==fp_bits(fp));
    assert((fp_bits(direct_back)&fraction_mask)==(fp_bits(modular_back)&fraction_mask));
    assert(modular_back==-0x1p54*direct_back);
    uint64_t modular_unit=((modular&((UINT64_C(1)<<53)-1))<<1)|1;
    assert(((3*modular_unit)&PADIC64_RESIDUE_MASK)==1);
    printf("PASS: both exports have the same 53-bit FP64 significand.\n");
    printf("PASS: B = -2^54 * A exactly; their signs and FP64 exponents differ.\n");
    printf("PASS: modular unit satisfies 3*m == 1 modulo 2^54.\n");
    printf("PASS: both paths and comparisons raise no software flags.\n");
    return 0;
}
