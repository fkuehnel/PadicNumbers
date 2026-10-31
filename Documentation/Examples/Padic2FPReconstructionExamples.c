// Reproduce the finite FP64 -> packed p-adic operation -> rational
// reconstruction -> FP64 observations in Padic64Proposal.md.
// From the repository root on ARM64 macOS:
// clang -Wall -Wextra -Werror -O2 -fsanitize=undefined -I Documentation/Examples \
//   Documentation/Examples/Padic2AArch64.s Documentation/Examples/Padic2Packed64.c \
//   Documentation/Examples/Padic2FPReconstructionExamples.c -o /tmp/padic-fp-examples
// /tmp/padic-fp-examples
// This is a diagnostic example, not a general rational-to-FP converter. Native
// FP division appears only here to round recovered pairs for comparison.
#include "Padic2Packed64.h"
#include <math.h>
#include <stdio.h>
typedef Padic64 (*Operation)(Padic64,Padic64,Padic64Flags*);
static void check(const char *name,double x,double y,Operation op,double fp) {
    Padic64Flags flags=0;
    Padic64 a=padic64_from_double(x,&flags),b=padic64_from_double(y,&flags);
    Padic64 c=op(a,b,&flags);
    Padic64Rational r;
    if(padic64_reconstruct(c,&r,&flags)) {
        // The demonstrated successful cases have exponent zero, with both
        // integers exactly representable as FP64. One native division rounds
        // the exact reconstructed rational, so scaling/double rounding is absent.
        if(r.exponent!=0) {printf("unexpected test exponent\n");return;}
        double back=(double)r.numerator/(double)r.denominator;
        printf("%s: reconstructed %lld/%lld, FP %.17g vs expected %.17g, flags=0x%x\n",
            name,(long long)r.numerator,(long long)r.denominator,back,fp,flags);
    } else printf("%s: reconstruction failed, FP expected %.17g, flags=0x%x\n",name,fp,flags);
}
int main(void) {
    volatile double one=1,two=2,three=3,large=0x1p54,m=0x1p27+1;
    check("add 1+2",one,two,padic64_add,one+two);
    check("add 1+1",one,one,padic64_add,one+one);
    check("add 1+2^54",one,large,padic64_add,one+large);
    check("sub 1-2^54",one,large,padic64_sub,one-large);
    check("mul (2^27+1)^2",m,m,padic64_mul,m*m);
    check("div 1/3",one,three,padic64_div,one/three);
    check("div (2^27+1)/1",m,one,padic64_div,m/one);
    Padic64Flags flags=0;Padic64Rational r;
    Padic64 n=padic64_neg(padic64_from_double(m,&flags),&flags);
    int ok=padic64_reconstruct(n,&r,&flags);
    printf("neg (2^27+1): reconstruction success=%d, FP expected %.17g, flags=0x%x\n",
        ok,-m,flags);
    return 0;
}
