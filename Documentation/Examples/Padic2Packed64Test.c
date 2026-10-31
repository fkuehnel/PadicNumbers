// ARM64 Mac, from repository root:
// clang -Wall -Wextra -Werror -O2 -fsanitize=undefined \
//   Documentation/Examples/Padic2AArch64.s Documentation/Examples/Padic2Packed64.c \
//   Documentation/Examples/Padic2Packed64Test.c -o /tmp/padic64-test
// /tmp/padic64-test
#include "Padic2Packed64.h"
#include "Padic2AArch64.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <string.h>

static uint64_t state=0x136785aabc987623ULL;
static uint64_t random_word(void) {state^=state<<13;state^=state>>7;state^=state<<17;return state;}
static Padic64 word(uint64_t m,int64_t e) {
    return (((uint64_t)e & 2047)<<53) | ((m & PADIC64_RESIDUE_MASK)>>1);
}
static uint64_t unit(Padic64 x) {return ((x & ((UINT64_C(1)<<53)-1))<<1)|1;}
static int64_t valuation(Padic64 x) {int64_t e=(int64_t)(x>>53);return e<1024?e:e-2048;}
static uint64_t shifted(uint64_t m,int64_t d) {
    return d>=54?0:(m<<(unsigned)d)&PADIC64_RESIDUE_MASK;
}
static void expect_range(Padic64 result,int64_t e,Padic64Flags flags) {
    if(e < -1023 || e > 1023) assert(result==PADIC64_NAN && flags==PADIC64_EXPONENT_RANGE);
    else assert(result!=PADIC64_NAN && valuation(result)==e && flags==0);
}

static int64_t reference_signed(Padic64 w) {
    if(w==PADIC64_ZERO) return 0;
    uint64_t u=unit(w);
    return u<(UINT64_C(1)<<53)?(int64_t)u:(int64_t)u-(INT64_C(1)<<54);
}
// Exact independent oracle: compare occupied powers of two one bit at a time
// across the entire format range. No CLZ, FP conversion or truncating subtraction.
static Padic64Comparison reference_compare(Padic64 a,Padic64 b) {
    int64_t sa=reference_signed(a),sb=reference_signed(b);
    if(sa<0 && sb>=0) return PADIC64_CMP_LT;
    if(sa>=0 && sb<0) return PADIC64_CMP_GT;
    uint64_t ma=(uint64_t)(sa<0?-sa:sa),mb=(uint64_t)(sb<0?-sb:sb);
    int64_t ea=a==PADIC64_ZERO?0:valuation(a),eb=b==PADIC64_ZERO?0:valuation(b);
    for(int power=1075;power>=-1023;power--) {
        int64_t ia=power-ea,ib=power-eb;
        unsigned ba=ia>=0 && ia<54?(unsigned)((ma>>ia)&1):0;
        unsigned bb=ib>=0 && ib<54?(unsigned)((mb>>ib)&1):0;
        if(ba!=bb) {
            int less=ba<bb;
            if(sa<0) less=!less;
            return less?PADIC64_CMP_LT:PADIC64_CMP_GT;
        }
    }
    return PADIC64_CMP_EQ;
}
static Padic64Comparison reversed(Padic64Comparison c) {
    return c==PADIC64_CMP_LT?PADIC64_CMP_GT:c==PADIC64_CMP_GT?PADIC64_CMP_LT:c;
}
static void compare_checked(Padic64 a,Padic64 b) {
    Padic64Flags flags=PADIC64_DIVZERO; // Successful comparison must preserve flags.
    Padic64Comparison expected=reference_compare(a,b);
    assert(padic64_compare_dyadic(a,b,&flags)==expected);
    assert(padic64_compare_dyadic(b,a,&flags)==reversed(expected));
    assert(padic64_compare_dyadic(a,a,&flags)==PADIC64_CMP_EQ);
    assert(flags==PADIC64_DIVZERO);
}
static void check_comparison(void) {
    const Padic64 corners[]={PADIC64_ZERO,word(1,0),word(-1,0),word(3,0),word(-3,0),
        word(1,1),word(-1,1),word(1,-1023),word(-1,-1023),word(1,1023),word(-1,1023),
        word(3,1023),word(5,1023),word((UINT64_C(1)<<53)-1,0),
        word((UINT64_C(1)<<53)-3,0),word((UINT64_C(1)<<53)+1,0)};
    unsigned long pairs=0;
    for(unsigned i=0;i<sizeof(corners)/sizeof(corners[0]);i++)
        for(unsigned j=0;j<sizeof(corners)/sizeof(corners[0]);j++) {
            compare_checked(corners[i],corners[j]);pairs++;
        }
    for(unsigned i=0;i<100000;i++) {
        Padic64 a=word(random_word()|1,(int64_t)(random_word()%2047)-1023);
        Padic64 b=word(random_word()|1,(int64_t)(random_word()%2047)-1023);
        // Frequently force equal leading-bit positions: distinct units sharing
        // their top bit and exponent exercise the magnitude tie-break path.
        if(i%4==0) {
            uint64_t m=(random_word()&((UINT64_C(1)<<51)-1))|(UINT64_C(1)<<51)|1;
            a=word(m,valuation(a));b=word(m^2,valuation(a));
            if(i%8==0) {a=word(-unit(a),valuation(a));b=word(-unit(b),valuation(b));}
        }
        compare_checked(a,b);pairs++;
        if(i<1000) {
            Padic64 c=word(random_word()|1,(int64_t)(random_word()%2047)-1023);
            Padic64Flags flags=0;
            Padic64Comparison ab=padic64_compare_dyadic(a,b,&flags);
            Padic64Comparison bc=padic64_compare_dyadic(b,c,&flags);
            if(ab<=PADIC64_CMP_EQ && bc<=PADIC64_CMP_EQ)
                assert(padic64_compare_dyadic(a,c,&flags)<=PADIC64_CMP_EQ);
            assert(flags==0);
        }
    }
    Padic64Flags flags=0;
    assert(padic64_compare_dyadic(PADIC64_NAN,PADIC64_NAN,&flags)==PADIC64_CMP_UNORDERED);
    assert(flags==0);
    flags=0;
    assert(padic64_compare_dyadic(PADIC64_ZERO,PADIC64_NEEDS_PRECISION,&flags)==PADIC64_CMP_UNORDERED);
    assert(flags==PADIC64_INSUFFICIENT_PRECISION);
    flags=0;
    assert(padic64_compare_dyadic(PADIC64_NEEDS_PRECISION,PADIC64_ZERO,&flags)==PADIC64_CMP_UNORDERED);
    assert(flags==PADIC64_INSUFFICIENT_PRECISION);
    flags=0;
    assert(padic64_compare_dyadic(PADIC64_ZERO|37,PADIC64_NEEDS_PRECISION,&flags)==PADIC64_CMP_UNORDERED);
    assert(flags==PADIC64_INVALID);
    // Subtract-and-test would get this wrong: 1 - (-2^53) wraps the signed
    // representative window without any loss of modular relative precision.
    flags=0;
    Padic64 one=word(1,0),negative=word(-1,53);
    assert(padic64_compare_dyadic(one,negative,&flags)==PADIC64_CMP_GT);
    Padic64 difference=padic64_sub(one,negative,&flags);
    assert(padic64_compare_dyadic(difference,PADIC64_ZERO,&flags)==PADIC64_CMP_LT);
    assert(flags==0);
    // Both representatives overflow FP64, but their integer-only order is exact.
    assert(padic64_compare_dyadic(word(3,1023),word(5,1023),&flags)==PADIC64_CMP_LT);
    assert(flags==0);
    // The general assembly kernel also handles the largest signed magnitude.
    assert(padic2_compare_dyadic_units(INT64_MIN,0,-1,63)==0);
    assert(padic2_compare_dyadic_units(INT64_MIN,0,INT64_MAX,0)==-1);
    assert(padic2_compare_dyadic_units(0,-1023,0,1023)==0);
    printf("PASS: %lu exact signed-dyadic comparison pairs, reverse/self checks, special values and subtraction-overflow regression.\n",pairs);
}
static uint64_t reference_power(uint64_t a,uint64_t power,uint64_t mask) {
    // Left-to-right exponent scan, with explicit wide integer products.
    uint64_t result=1;
    for(int bit=63;bit>=0;bit--) {
        result=(uint64_t)((__uint128_t)result*result)&mask;
        if((power>>bit)&1) result=(uint64_t)((__uint128_t)result*a)&mask;
    }
    return result;
}
static uint64_t reference_root(uint64_t u,unsigned n) {
    // Independent one-bit-at-a-time root lifting; no Newton inverse root.
    uint64_t root=1;
    for(unsigned k=3;k<n;k++)
        root+=((u-root*root)>>k & 1) << (k-1);
    return root;
}
static void check_power_root(void) {
    unsigned long roots=0,powers=0;
    for(unsigned n=3;n<=64;n++) {
        uint64_t input_mask=UINT64_MAX>>(64-n),output_mask=input_mask>>1;
        for(unsigned i=0;i<512;i++) {
            uint64_t u=(random_word()&input_mask&~UINT64_C(7))|1;
            uint64_t root=padic2_sqrt_unit(u,output_mask);
            assert(root==reference_root(u,n));
            assert((root&3)==1 && ((root*root)&input_mask)==u);
            roots++;
        }
    }
    for(uint64_t u=1;u<(UINT64_C(1)<<16);u+=8) {
        assert(padic2_sqrt_unit(u,32767)==reference_root(u,16));roots++;
    }
    for(unsigned r=1;r<=64;r++) {
        uint64_t mask=UINT64_MAX>>(64-r);
        for(unsigned i=0;i<512;i++) {
            uint64_t a=random_word()&mask,k=random_word();
            assert(padic2_pow_unit(a,k,mask)==reference_power(a,k,mask));powers++;
        }
        assert(padic2_pow_unit(0,0,mask)==1); // Raw residue convention; wrapper rejects 0^0.
        assert(padic2_pow_unit(0,1,mask)==0);
        assert(padic2_pow_unit(3,UINT64_C(1)<<63,mask)==1);
    }
    Padic64Flags flags=0;
    assert(padic64_pow(PADIC64_ZERO,3,&flags)==PADIC64_ZERO && flags==0);
    assert(padic64_pow(PADIC64_ZERO,0,&flags)==PADIC64_NAN && flags==PADIC64_INVALID);
    flags=0;
    assert(padic64_pow(PADIC64_ZERO,-1,&flags)==PADIC64_NAN && flags==(PADIC64_INVALID|PADIC64_DIVZERO));
    flags=0;
    assert(padic64_pow(word(3,0),INT64_MIN,&flags)==word(1,0) && flags==0);
    assert(((unit(padic64_pow(word(3,0),INT64_MAX,&flags))*3)&PADIC64_RESIDUE_MASK)==1);
    assert(flags==0);
    assert(padic64_pow(word(3,1),INT64_MIN,&flags)==PADIC64_NAN && flags==PADIC64_EXPONENT_RANGE);
    flags=0;
    assert(padic64_pow(PADIC64_NEEDS_PRECISION,2,&flags)==PADIC64_NEEDS_PRECISION && flags==PADIC64_INSUFFICIENT_PRECISION);
    flags=0;
    assert(padic64_pow(PADIC64_NAN,0,&flags)==PADIC64_NAN && flags==0);
    for(unsigned i=0;i<10000;i++) {
        uint64_t m=(random_word()&PADIC64_RESIDUE_MASK)|1;
        int64_t e=(int64_t)(random_word()%41)-20,k=(int64_t)(random_word()%127)-63;
        uint64_t magnitude=(uint64_t)(k<0?-k:k);
        flags=0;
        Padic64 result=padic64_pow(word(m,e),k,&flags);
        expect_range(result,e*k,flags);
        if(!flags) {
            uint64_t positive=reference_power(m,magnitude,PADIC64_RESIDUE_MASK);
            if(k<0) assert(((unit(result)*positive)&PADIC64_RESIDUE_MASK)==1);
            else assert(unit(result)==positive);
        }
        powers++;
    }
    flags=0;
    assert(padic64_sqrt(PADIC64_ZERO,&flags)==PADIC64_ZERO && flags==0);
    assert(padic64_sqrt_refined(PADIC64_ZERO,0,&flags)==PADIC64_ZERO && flags==0);
    assert(padic64_sqrt_refined(PADIC64_ZERO,1,&flags)==PADIC64_NAN && flags==PADIC64_INVALID);
    const Padic64 nonsquares[]={word(3,0),word(5,0),word(7,0),word(1,1),word(1,-1)};
    for(unsigned i=0;i<sizeof(nonsquares)/sizeof(nonsquares[0]);i++) {
        flags=0;
        assert(padic64_sqrt(nonsquares[i],&flags)==PADIC64_NAN && flags==PADIC64_INVALID);
    }
    flags=0;
    assert(padic64_sqrt(PADIC64_NEEDS_PRECISION,&flags)==PADIC64_NEEDS_PRECISION && flags==PADIC64_INSUFFICIENT_PRECISION);
    flags=0;
    assert(padic64_sqrt(PADIC64_NAN,&flags)==PADIC64_NAN && flags==0);
    flags=0;
    assert(padic64_sqrt(word(25,0),&flags)==PADIC64_NEEDS_PRECISION);
    assert(flags==(PADIC64_PRECISION_LOST|PADIC64_INSUFFICIENT_PRECISION));
    flags=0;
    assert(padic64_sqrt_refined(word(25,0),25,&flags)==word(5,0) && flags==0);
    assert(padic64_sqrt_refined(word(9,0),9,&flags)==word(-3,0) && flags==0);
    assert(padic64_sqrt_refined(word(1,0),1,&flags)==word(1,0));
    assert(padic64_sqrt_refined(word(1,0),1+(UINT64_C(1)<<54),&flags)==word(1+(UINT64_C(1)<<53),0));
    assert(flags==0); // The missing input bit changes a real output bit.
    assert(padic64_sqrt_refined(word(25,0),9,&flags)==PADIC64_NAN && flags==PADIC64_INVALID);
    flags=0;
    assert(padic64_sqrt_refined(word(1,0),(UINT64_C(1)<<55)|1,&flags)==PADIC64_NAN && flags==PADIC64_INVALID);
    const uint64_t mask55=(UINT64_C(1)<<55)-1;
    for(unsigned i=0;i<10000;i++) {
        uint64_t m=(random_word()&PADIC64_RESIDUE_MASK)|1;
        int64_t e=(int64_t)(random_word()%1001)-500;
        flags=PADIC64_DIVZERO;
        Padic64 squared=padic64_pow(word(m,e),2,&flags);
        // Squaring a 54-bit unit certifies 55 bits: compute the extra bit from
        // the retained source, rather than guessing from the truncated square.
        uint64_t refined=(m*m)&mask55;
        Padic64 root=padic64_sqrt_refined(squared,refined,&flags);
        uint64_t expected=(m&3)==1?m:(-m)&PADIC64_RESIDUE_MASK;
        assert(root==word(expected,e));
        assert(padic64_pow(root,2,&flags)==squared);
        assert(flags==PADIC64_DIVZERO);
        roots++;
    }
    printf("PASS: %lu power cases; %lu root cases, including source-refined packed roots, domain/precision flags and exponent limits.\n",powers,roots);
}

static uint64_t double_bits(double d) {uint64_t bits;memcpy(&bits,&d,8);return bits;}
static double from_bits(uint64_t bits) {double d;memcpy(&d,&bits,8);return d;}

static void check_special_values(void) {
    const uint64_t cases[]={
        UINT64_C(0x7ff0000000000000),UINT64_C(0xfff0000000000000),
        UINT64_C(0x7ff8000000000000),UINT64_C(0xfff8000000000001),
        UINT64_C(0x7fffffffffffffff),UINT64_C(0xffffffffffffffff),
        UINT64_C(0x7ff0000000000001),UINT64_C(0xfff0000000000001),
        UINT64_C(0x7ff7ffffffffffff),UINT64_C(0xfff7ffffffffffff)};
    for(unsigned i=0;i<sizeof(cases)/sizeof(cases[0]);i++) {
        uint64_t bits=cases[i],fraction=bits&UINT64_C(0x000fffffffffffff);
        Padic64Flags flags=PADIC64_DIVZERO;
        Padic64 p=padic64_from_double(from_bits(bits),&flags);
        Padic64Flags expected=PADIC64_DIVZERO;
        if(fraction && !(fraction&UINT64_C(0x0008000000000000))) expected|=PADIC64_INVALID;
        assert(p==(fraction?PADIC64_NAN:(bits>>63?PADIC64_NEG_INFINITY:PADIC64_POS_INFINITY)));
        assert(flags==expected);
        uint64_t back=double_bits(padic64_to_double_dyadic(p,&flags));
        assert(back==(fraction?UINT64_C(0x7ff8000000000000):bits));
        assert(flags==expected); // Imported infinity is not FP overflow.
    }

    // Compare extended signed-dyadic behavior against native real arithmetic
    // only when at least one operand is infinity. Ordinary finite arithmetic
    // remains modular and is deliberately NOT subject to this oracle.
    const double values[]={-INFINITY,-3.0,0.0,2.0,INFINITY};
    Padic64 (*ops[])(Padic64,Padic64,Padic64Flags*)={padic64_add,padic64_sub,padic64_mul,padic64_div};
    unsigned checked=0;
    for(unsigned i=0;i<5;i++) for(unsigned j=0;j<5;j++) {
        if(!isinf(values[i]) && !isinf(values[j])) continue;
        volatile double a=values[i],b=values[j];
        Padic64Flags flags=0;
        Padic64 pa=padic64_from_double(a,&flags),pb=padic64_from_double(b,&flags);
        for(unsigned op=0;op<4;op++) {
            double expected;
            switch(op) {
                case 0:expected=a+b;break;
                case 1:expected=a-b;break;
                case 2:expected=a*b;break;
                default:expected=a/b;break;
            }
            flags=PADIC64_DIVZERO;
            Padic64 result=ops[op](pa,pb,&flags);
            double back=padic64_to_double_dyadic(result,&flags);
            if(isnan(expected)) {
                assert(result==PADIC64_NAN && isnan(back));
                assert(flags==(PADIC64_DIVZERO|PADIC64_INVALID));
            } else {
                assert(back==expected); // Zero signs intentionally merge.
                assert(flags==PADIC64_DIVZERO);
            }
            checked++;
        }
        flags=0;
        assert(padic64_compare_dyadic(pa,pb,&flags)==
            (a<b?PADIC64_CMP_LT:a>b?PADIC64_CMP_GT:PADIC64_CMP_EQ));
        assert(flags==0);
    }
    Padic64Flags flags=0;
    assert(padic64_neg(PADIC64_POS_INFINITY,&flags)==PADIC64_NEG_INFINITY);
    assert(padic64_neg(PADIC64_NEG_INFINITY,&flags)==PADIC64_POS_INFINITY);
    assert(padic64_pow(PADIC64_NEG_INFINITY,3,&flags)==PADIC64_NEG_INFINITY);
    assert(padic64_pow(PADIC64_NEG_INFINITY,2,&flags)==PADIC64_POS_INFINITY);
    assert(padic64_pow(PADIC64_POS_INFINITY,INT64_MAX,&flags)==PADIC64_POS_INFINITY);
    assert(padic64_pow(PADIC64_NEG_INFINITY,INT64_MIN,&flags)==PADIC64_ZERO);
    assert(padic64_pow(PADIC64_POS_INFINITY,-1,&flags)==PADIC64_ZERO);
    assert(padic64_pow(PADIC64_NEG_INFINITY,0,&flags)==word(1,0));
    assert(padic64_sqrt(PADIC64_POS_INFINITY,&flags)==PADIC64_POS_INFINITY);
    assert(padic64_sqrt_refined(PADIC64_POS_INFINITY,0,&flags)==PADIC64_POS_INFINITY);
    assert(flags==0);
    assert(padic64_sqrt(PADIC64_NEG_INFINITY,&flags)==PADIC64_NAN && flags==PADIC64_INVALID);
    flags=0;
    assert(padic64_sqrt_refined(PADIC64_NEG_INFINITY,0,&flags)==PADIC64_NAN && flags==PADIC64_INVALID);

    const Padic64 companions[]={word(1,0),PADIC64_ZERO,PADIC64_POS_INFINITY,
        PADIC64_NEG_INFINITY,PADIC64_NEEDS_PRECISION,PADIC64_NAN};
    for(unsigned i=0;i<sizeof(companions)/sizeof(companions[0]);i++) {
        flags=PADIC64_DIVZERO;
        for(unsigned op=0;op<4;op++) {
            assert(ops[op](PADIC64_NAN,companions[i],&flags)==PADIC64_NAN);
            assert(ops[op](companions[i],PADIC64_NAN,&flags)==PADIC64_NAN);
        }
        assert(padic64_compare_dyadic(PADIC64_NAN,companions[i],&flags)==PADIC64_CMP_UNORDERED);
        assert(padic64_compare_dyadic(companions[i],PADIC64_NAN,&flags)==PADIC64_CMP_UNORDERED);
        assert(flags==PADIC64_DIVZERO);
    }
    flags=0;
    assert(padic64_neg(PADIC64_NAN,&flags)==PADIC64_NAN && flags==0);
    assert(padic64_sqrt_refined(PADIC64_NAN,0,&flags)==PADIC64_NAN && flags==0);
    // Tags must never fall through into ordinary finite-residue arithmetic.
    for(unsigned op=0;op<4;op++) {
        flags=0;
        assert(ops[op](PADIC64_POS_INFINITY,PADIC64_NEEDS_PRECISION,&flags)==PADIC64_NEEDS_PRECISION);
        assert(flags==PADIC64_INSUFFICIENT_PRECISION);
        flags=0;
        assert(ops[op](PADIC64_NAN,PADIC64_ZERO|37,&flags)==PADIC64_NAN);
        assert(flags==PADIC64_INVALID);
    }
    printf("PASS: infinity/NaN interchange (including signaling NaNs), %u infinity arithmetic cases, comparison, unary operations and sticky flags.\n",checked);
}

int main(void) {
    _Static_assert(sizeof(Padic64)==8,"Packed word must be 64 bits");
    Padic64Flags flags=0;
    Padic64 one=padic64_from_double(1.0,&flags),two=padic64_from_double(2.0,&flags);
    assert(one==0 && two==word(1,1) && flags==0);
    assert(padic64_from_double(-0.0,&flags)==PADIC64_ZERO);
    assert(padic64_add(one,PADIC64_ZERO,&flags)==one);
    assert(padic64_sub(PADIC64_ZERO,one,&flags)==padic64_neg(one,&flags));
    assert(padic64_mul(one,PADIC64_ZERO,&flags)==PADIC64_ZERO);
    assert(padic64_div(PADIC64_ZERO,one,&flags)==PADIC64_ZERO && flags==0);
    Padic64 three=padic64_add(one,two,&flags);
    assert(padic64_to_double_dyadic(three,&flags)==3.0 && flags==0);
    assert(padic64_to_double_dyadic(padic64_sub(one,two,&flags),&flags)==-1.0);
    assert(padic64_div(one,PADIC64_ZERO,&flags)==PADIC64_NAN);
    assert(flags==(PADIC64_DIVZERO|PADIC64_INVALID));
    // Sticky flags survive subsequent successful instructions.
    assert(padic64_add(one,two,&flags)==three && flags==(PADIC64_DIVZERO|PADIC64_INVALID));
    flags=0;
    Padic64 retry=padic64_add(one,one,&flags);
    assert(retry==PADIC64_NEEDS_PRECISION);
    assert(flags==(PADIC64_PRECISION_LOST|PADIC64_INSUFFICIENT_PRECISION));
    flags=0;
    assert(padic64_sub(one,one,&flags)==PADIC64_NEEDS_PRECISION);
    assert(flags==(PADIC64_PRECISION_LOST|PADIC64_INSUFFICIENT_PRECISION));
    flags=0;
    assert(padic64_mul(retry,one,&flags)==retry && flags==PADIC64_INSUFFICIENT_PRECISION);
    flags=0;
    assert(isnan(padic64_to_double_dyadic(retry,&flags)) && flags==PADIC64_INSUFFICIENT_PRECISION);
    flags=0;
    assert(padic64_neg(PADIC64_ZERO|37,&flags)==PADIC64_NAN && flags==PADIC64_INVALID);
    flags=0;
    assert(padic64_from_double(INFINITY,&flags)==PADIC64_POS_INFINITY && flags==0);
    flags=0;
    assert(padic64_from_double(NAN,&flags)==PADIC64_NAN && flags==0);
    flags=0;
    assert(padic64_from_double(0x1p-1074,&flags)==PADIC64_NAN && flags==PADIC64_EXPONENT_RANGE);
    flags=0;
    assert(padic64_from_double(0x1p-1023,&flags)==word(1,-1023) && flags==0);
    // Some small NORMAL FP64 values also have valuations below -1023.
    flags=0;
    assert(padic64_from_double(0x1.0000000000001p-1022,&flags)==PADIC64_NAN && flags==PADIC64_EXPONENT_RANGE);
    flags=0;
    assert(isinf(padic64_to_double_dyadic(word(3,1023),&flags)) && flags==PADIC64_FP_OVERFLOW);
    // Ordinary modular carry is not exponent overflow or precision loss.
    flags=0;
    assert(padic64_add(word(PADIC64_RESIDUE_MASK,0),two,&flags)==one && flags==0);

    unsigned long pairs=0;
    for(unsigned i=0;i<100000;i++) {
        uint64_t a=(random_word()&PADIC64_RESIDUE_MASK)|1;
        uint64_t b=(random_word()&PADIC64_RESIDUE_MASK)|1;
        int64_t ea=(int64_t)(random_word()%2047)-1023;
        int64_t eb=i%3==0?ea:(int64_t)(random_word()%2047)-1023;
        Padic64 wa=word(a,ea),wb=word(b,eb);
        int64_t e=ea<eb?ea:eb;
        uint64_t ma=shifted(a,ea-e),mb=shifted(b,eb-e);
        for(unsigned subtract=0;subtract<=1;subtract++) {
            uint64_t m=(subtract?ma-mb:ma+mb)&PADIC64_RESIDUE_MASK;
            flags=0;
            Padic64 out=subtract?padic64_sub(wa,wb,&flags):padic64_add(wa,wb,&flags);
            if((m&1)==0) {
                assert(out==PADIC64_NEEDS_PRECISION);
                assert(flags==(PADIC64_PRECISION_LOST|PADIC64_INSUFFICIENT_PRECISION));
            } else assert(out==word(m,e) && flags==0);
        }
        flags=0;
        assert(padic64_neg(wa,&flags)==word(-a,ea) && flags==0);
        flags=0;
        Padic64 out=padic64_mul(wa,wb,&flags);
        expect_range(out,ea+eb,flags);
        if(!flags) assert(out==word(a*b,ea+eb));
        flags=0;
        out=padic64_div(wa,wb,&flags);
        expect_range(out,ea-eb,flags);
        if(!flags) assert(((unit(out)*b)&PADIC64_RESIDUE_MASK)==a);
        pairs++;
    }
    unsigned long conversions=0;
    for(unsigned i=0;i<100000;i++) {
        uint64_t bits=random_word();double d;memcpy(&d,&bits,8);
        Padic2Decoded expected;padic2_from_double(d,PADIC64_RESIDUE_MASK,&expected);
        flags=0;
        Padic64 out=padic64_from_double(d,&flags);
        if(expected.status==PADIC2_NONFINITE) {
            uint64_t fraction=bits&UINT64_C(0x000fffffffffffff);
            if(fraction) {
                assert(out==PADIC64_NAN);
                assert(flags==((fraction&UINT64_C(0x0008000000000000))?0:PADIC64_INVALID));
                assert(isnan(padic64_to_double_dyadic(out,&flags)));
            } else {
                assert(out==(bits>>63?PADIC64_NEG_INFINITY:PADIC64_POS_INFINITY) && flags==0);
                assert(double_bits(padic64_to_double_dyadic(out,&flags))==bits && flags==0);
            }
        }
        else if(expected.status==PADIC2_EXACT_ZERO) assert(out==PADIC64_ZERO && flags==0);
        else if(expected.exponent < -1023 || expected.exponent > 1023)
            assert(out==PADIC64_NAN && flags==PADIC64_EXPONENT_RANGE);
        else {
            assert(out==word(expected.residue,expected.exponent) && flags==0);
            double back=padic64_to_double_dyadic(out,&flags);
            assert(back==d && flags==0);
        }
        conversions++;
    }
    printf("PASS: %lu packed arithmetic pairs; %lu FP64 conversions; reserved tags, sticky flags, precision rejection and range checks.\n",pairs,conversions);
    printf("Example: 1+2 -> 3; independent 54-bit 1+1 -> NEEDS_PRECISION, flags=0x%x.\n",
           PADIC64_PRECISION_LOST|PADIC64_INSUFFICIENT_PRECISION);
    check_comparison();
    check_power_root();
    check_special_values();
}
