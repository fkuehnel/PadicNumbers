// Native smoke/property checks on an ARM64 Mac. From the repository root:
// clang -Wall -Wextra -Werror -O2 Documentation/Examples/Padic2AArch64.s \
//   Documentation/Examples/Padic2AArch64Test.c -o /tmp/padic2-test
// /tmp/padic2-test
// python3 Documentation/Examples/Padic2DyadicReferenceTest.py /tmp/padic2-test
#include "Padic2AArch64.h"
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <string.h>
#include <stddef.h>
#include <float.h>
#include <inttypes.h>
_Static_assert(sizeof(double)==8 && FLT_RADIX==2 && DBL_MANT_DIG==53 &&
               DBL_MAX_EXP==1024 && DBL_MIN_EXP==-1021, "Requires binary64");
_Static_assert(sizeof(Padic2Decoded)==24 && offsetof(Padic2Decoded,exponent)==8 &&
               offsetof(Padic2Decoded,status)==16, "Assembly output layout");
static uint64_t state=0x0123456789abcdefULL;
static uint64_t rnd(void) {state^=state<<13;state^=state>>7;state^=state<<17;return state;}

static uint64_t precision_mask(unsigned r) {return UINT64_MAX>>(64-r);}
static double from_bits(uint64_t bits) {double d;memcpy(&d,&bits,8);return d;}
static uint64_t double_bits(double d) {uint64_t bits;memcpy(&bits,&d,8);return bits;}

// Independent oracle using FP decomposition, not IEEE field extraction.
static Padic2Decoded reference_double(double value,uint64_t mask) {
    if(!isfinite(value)) return (Padic2Decoded){0,0,PADIC2_NONFINITE};
    if(value==0) return (Padic2Decoded){0,0,PADIC2_EXACT_ZERO};
    int e;
    double fraction=frexp(fabs(value),&e);
    uint64_t unit=(uint64_t)ldexp(fraction,53);
    e-=53;
    while((unit&1)==0) {unit>>=1;e++;}
    if(signbit(value)) unit=-unit;
    return (Padic2Decoded){unit&mask,e,PADIC2_FINITE};
}

static Padic2Decoded convert_checked(double value,unsigned r) {
    Padic2Decoded actual,expected=reference_double(value,precision_mask(r));
    padic2_from_double(value,precision_mask(r),&actual);
    assert(actual.status==expected.status && actual.residue==expected.residue &&
           actual.exponent==expected.exponent);
    return actual;
}

// Independent bit-by-bit reference for exponent alignment and truncation.
static uint64_t aligned(uint64_t m, int64_t exponent, int64_t base, unsigned r) {
    uint64_t out=0;
    for(unsigned bit=0;bit<64;bit++) {
        int64_t place=exponent-base+bit;
        if(place<(int64_t)r && ((m>>bit)&1)) out |= UINT64_C(1)<<place;
    }
    return out;
}

static void check_pair(uint64_t a,int64_t ea,unsigned ra,
                       uint64_t b,int64_t eb,unsigned rb) {
    int64_t e=ea<eb?ea:eb;
    int64_t aa=ea+ra, ab=eb+rb, absolute=aa<ab?aa:ab;
    unsigned r=(unsigned)(absolute-e);
    assert(r>=1 && r<=64);
    uint64_t mask=UINT64_MAX>>(64-r);
    uint64_t ma=aligned(a,ea,e,r), mb=aligned(b,eb,e,r);
    assert(padic2_add(a,b,mask,ea,eb)==((ma+mb)&mask));
    assert(padic2_sub(a,b,mask,ea,eb)==((ma-mb)&mask));
}

// Verify a residue and its normalized form against an exactly representable
// FP64 result. Arbitrary rounded FP arithmetic is NOT a 2-adic oracle.
static void check_exact_result(uint64_t m,int64_t e,unsigned r,double value) {
    Padic2Decoded expected=reference_double(value,UINT64_MAX);
    assert(expected.status!=PADIC2_NONFINITE);
    if(expected.status==PADIC2_EXACT_ZERO) {assert(m==0);return;}
    assert(expected.exponent>=e);
    assert(m==aligned(expected.residue,expected.exponent,e,r));
    if(m) {
        unsigned k=(unsigned)padic2_ctz(m);
        assert(e+k==expected.exponent);
        assert((m>>k)==(expected.residue&precision_mask(r-k)));
    }
}

static void check_fp64(void) {
    const uint64_t edges[]={0,UINT64_C(1)<<63,1,0x8000000000000001ULL,
        0xfffffffffffffULL,0x10000000000000ULL,0x7fefffffffffffffULL,
        0xffefffffffffffffULL,0x7ff0000000000000ULL,0xfff0000000000000ULL,
        0x7ff8000000000001ULL,0x7ff0000000000001ULL};
    unsigned long conversions=0,pairs=0;
    for(unsigned r=1;r<=64;r++) {
        for(unsigned j=0;j<sizeof(edges)/sizeof(edges[0]);j++) {
            convert_checked(from_bits(edges[j]),r);conversions++;
        }
        for(unsigned j=0;j<4096;j++) {
            double x=from_bits(rnd()),y=from_bits(rnd());
            unsigned rb=1+(j%64);
            Padic2Decoded a=convert_checked(x,r),b=convert_checked(y,rb);
            conversions+=2;
            if(a.status!=PADIC2_FINITE || b.status!=PADIC2_FINITE) continue;
            check_pair(a.residue,a.exponent,r,b.residue,b.exponent,rb);
            unsigned n=r<rb?r:rb;
            uint64_t mask=precision_mask(n);
            Padic2Decoded refa=reference_double(x,mask),refb=reference_double(y,mask);
            assert(padic2_neg(a.residue,0,precision_mask(r))==
                   reference_double(-x,precision_mask(r)).residue);
            assert(padic2_mul(a.residue,b.residue,mask)==
                   ((refa.residue*refb.residue)&mask));
            uint64_t q=padic2_div(a.residue,b.residue,mask);
            assert((q&~mask)==0 && ((q*refb.residue)&mask)==refa.residue);
            pairs++;
        }
    }
    // All five arithmetic results in these examples are exactly representable
    // in FP64; this also checks signs, cancellation and exponent bookkeeping.
    const double examples[][2]={{6.5,0.5},{-6.5,0.25},{1.25,-2.5},
                               {0.5,0.5},{0x1p-100,0x1p-100}};
    for(unsigned r=1;r<=64;r++) {
        uint64_t mask=precision_mask(r);
        for(unsigned j=0;j<sizeof(examples)/sizeof(examples[0]);j++) {
            double x=examples[j][0],y=examples[j][1];
            Padic2Decoded a=convert_checked(x,r),b=convert_checked(y,r);
            int64_t e=a.exponent<b.exponent?a.exponent:b.exponent;
            check_exact_result(padic2_add(a.residue,b.residue,mask,a.exponent,b.exponent),e,r,x+y);
            check_exact_result(padic2_sub(a.residue,b.residue,mask,a.exponent,b.exponent),e,r,x-y);
            check_exact_result(padic2_neg(a.residue,0,mask),a.exponent,r,-x);
            check_exact_result(padic2_mul(a.residue,b.residue,mask),a.exponent+b.exponent,r,x*y);
            check_exact_result(padic2_div(a.residue,b.residue,mask),a.exponent-b.exponent,r,x/y);
        }
    }
    Padic2Decoded demo=convert_checked(6.5,8);
    Padic2Decoded decimal=convert_checked(0.1,64);
    assert(decimal.residue==UINT64_C(3602879701896397) && decimal.exponent==-55);
    assert(convert_checked(0x1p1023,64).exponent==1023);
    printf("FP64 6.5 -> residue=%llu, exponent=%lld (8 relative bits).\n",
           (unsigned long long)demo.residue,(long long)demo.exponent);
    printf("PASS: %lu FP64 conversions; %lu converted-input arithmetic pairs; 1600 exact-result checks.\n",
           conversions,pairs);
}

static void check_dyadic(void) {
    unsigned long roundtrips=0;
    const uint64_t edges[]={0,UINT64_C(1)<<63,1,0x8000000000000001ULL,
        0xfffffffffffffULL,0x10000000000000ULL,0x7fefffffffffffffULL,
        0xffefffffffffffffULL,0x3ff0000000000000ULL,0xbff0000000000000ULL};
    for(unsigned r=54;r<=64;r++) {
        for(unsigned i=0;i<8192+sizeof(edges)/sizeof(edges[0]);i++) {
            uint64_t bits=i<sizeof(edges)/sizeof(edges[0])?edges[i]:rnd();
            double value=from_bits(bits);
            if(!isfinite(value)) continue;
            Padic2Decoded decoded=convert_checked(value,r);
            uint64_t actual=double_bits(padic2_to_double_dyadic(&decoded,r));
            // Our forward conversion intentionally merges the two signed zeros.
            assert(actual==(value==0?0:bits));
            roundtrips++;
        }
    }
    // Explicit representative semantics: 171 mod 256 becomes -85, not 1/3.
    Padic2Decoded p={171,0,PADIC2_FINITE};
    assert(padic2_to_double_dyadic(&p,8)==-85.0);
    p=(Padic2Decoded){243,-1,PADIC2_FINITE};
    assert(padic2_to_double_dyadic(&p,8)==-6.5);
    p=(Padic2Decoded){13,-1,PADIC2_FINITE};
    assert(padic2_to_double_dyadic(&p,8)==6.5);
    assert(isnan(padic2_to_double_dyadic(&p,0)));
    assert(isnan(padic2_to_double_dyadic(&p,65)));
    p.status=PADIC2_NONFINITE;
    assert(isnan(padic2_to_double_dyadic(&p,8)));
    p.status=99;
    assert(isnan(padic2_to_double_dyadic(&p,8)));
    p.status=PADIC2_EXACT_ZERO;
    assert(double_bits(padic2_to_double_dyadic(&p,8))==0);
    // One-rounding regression: rounding the integer first would lose the +1.
    p=(Padic2Decoded){(UINT64_C(1)<<53)+1,-1128,PADIC2_FINITE};
    assert(double_bits(padic2_to_double_dyadic(&p,64))==1);
    p.residue=-p.residue;
    assert(double_bits(padic2_to_double_dyadic(&p,64))==0x8000000000000001ULL);
    p=(Padic2Decoded){1,INT64_MAX,PADIC2_FINITE};
    assert(double_bits(padic2_to_double_dyadic(&p,64))==0x7ff0000000000000ULL);
    p=(Padic2Decoded){UINT64_MAX,INT64_MIN,PADIC2_FINITE};
    assert(double_bits(padic2_to_double_dyadic(&p,64))==0x8000000000000000ULL);
    printf("PASS: %lu finite FP64 roundtrips at r=54..64; dyadic policy and rounding regressions.\n",roundtrips);
}

// Optional oracle protocol used by Padic2DyadicReferenceTest.py.
static int dyadic_vectors(void) {
    uint64_t m,r,expected,count=0;
    int64_t e;
    int fields;
    while((fields=scanf("%" SCNx64 " %" SCNd64 " %" SCNu64 " %" SCNx64,
                        &m,&e,&r,&expected))==4) {
        Padic2Decoded p={m,e,PADIC2_FINITE};
        uint64_t actual=double_bits(padic2_to_double_dyadic(&p,r));
        if(actual!=expected) {
            fprintf(stderr,"Dyadic mismatch: m=%" PRIx64 " e=%" PRId64
                    " r=%" PRIu64 " actual=%" PRIx64 " expected=%" PRIx64 "\n",
                    m,e,r,actual,expected);
            return 1;
        }
        count++;
    }
    assert(fields==EOF);
    printf("PASS: %" PRIu64 " independent exact-rational dyadic conversion vectors.\n",count);
    return 0;
}

int main(int argc,char **argv) {
    if(argc==2 && strcmp(argv[1],"--dyadic-vectors")==0) return dyadic_vectors();
    unsigned long count=0;
    for(unsigned r=1;r<=64;r++) {
        uint64_t mask=UINT64_MAX>>(64-r);
        for(unsigned i=0;i<4096;i++) {
            uint64_t a=rnd()&mask,b=rnd()&mask;
            assert(padic2_add(a,b,mask,0,0)==((a+b)&mask));
            assert(padic2_sub(a,b,mask,0,0)==((a-b)&mask));
            assert(padic2_neg(a,0,mask)==((-a)&mask));
            assert(padic2_mul(a,b,mask)==((a*b)&mask));
            b|=1;
            uint64_t q=padic2_div(a,b,mask);
            assert((q&~mask)==0 && ((q*b)&mask)==a);
            unsigned d=i%129;
            assert(padic2_align(a,d,mask)==(d>=64?0:(a<<d)&mask));
            assert(padic2_ctz(a)==(uint64_t)(a?__builtin_ctzll(a):64));
            count++;
        }
    }
    // Normalize cancellations without inventing precision.
    assert(padic2_add(1,7,255,0,0)==8 && padic2_ctz(8)==3);
    assert(padic2_sub(17,17,255,0,0)==0);
    // 3*2^-2 +/- 5*2^1, at the common exponent -2: 3 +/- 40.
    assert(padic2_add(3,5,255,-2,1)==43);
    assert(padic2_sub(3,5,255,-2,1)==219);
    assert(padic2_sub(5,3,255,1,-2)==37);
    unsigned long mixed=0;
    for(unsigned ra=1;ra<=64;ra++) {
        unsigned gaps[]={0,1,ra-1,ra,ra+1,63,64,65,127,128,129,2046};
        for(unsigned rb=1;rb<=64;rb++) {
            uint64_t a=(rnd() | 1) & (UINT64_MAX>>(64-ra));
            uint64_t b=(rnd() | 1) & (UINT64_MAX>>(64-rb));
            for(unsigned j=0;j<sizeof(gaps)/sizeof(gaps[0]);j++) {
                int64_t ea=-1023, eb=ea+gaps[j];
                check_pair(a,ea,ra,b,eb,rb);
                check_pair(b,eb,rb,a,ea,ra);
                mixed+=2;
            }
        }
    }
    // 1/3 mod 2^8 = 171; (-5)/3 mod 2^8 = 169.
    assert(padic2_div(1,3,255)==171);
    assert(padic2_div(251,3,255)==169);
    printf("PASS: %lu cases across r=1..64, all 7 kernels; cancellation and division examples.\n",count);
    printf("PASS: %lu mixed-exponent/precision pairs, addition and subtraction.\n",mixed);
    check_fp64();
    check_dyadic();
}
