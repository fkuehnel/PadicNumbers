// ARM64 Mac, from repository root:
// clang -Wall -Wextra -Werror -O2 -fsanitize=undefined \
//   Documentation/Examples/Padic2AArch64.s Documentation/Examples/Padic2Packed64.c \
//   Documentation/Examples/PadicRationalReconstructionTest.c -o /tmp/padic-rat-test
// /tmp/padic-rat-test
#include "Padic2AArch64.h"
#include "Padic2Packed64.h"
#include <assert.h>
#include <limits.h>
#include <stdio.h>

static uint64_t state=UINT64_C(0xbe72c8d4e53a1109);
static uint64_t random_word(void) {state^=state<<13;state^=state>>7;state^=state<<17;return state;}
static uint64_t magnitude(int64_t n) {return n<0?UINT64_C(0)-(uint64_t)n:(uint64_t)n;}
static uint64_t gcd(uint64_t a,uint64_t b) {while(b) {uint64_t r=a%b;a=b;b=r;}return a;}
static uint64_t reduce(__int128 n,uint64_t q) {
    __int128 r=n%q;return (uint64_t)(r<0?r+q:r);
}
static uint64_t inverse(uint64_t d,uint64_t q) {
    __int128 a=q,b=d,s=0,t=1;
    while(b) {__int128 k=a/b,r=a-k*b,c=s-k*t;a=b;b=r;s=t;t=c;}
    assert(a==1);return reduce(s,q);
}
static uint64_t bound(uint64_t q) {
    uint64_t lo=0,hi=UINT64_C(1)<<31;
    while(lo+1<hi) {
        uint64_t m=lo+(hi-lo)/2;
        if(2*(__uint128_t)m*m<q) lo=m;else hi=m;
    }
    return lo;
}
static void validate(uint64_t m,uint64_t q,int ok,PadicRationalPair out) {
    if(!ok) {assert(out.numerator==0 && out.denominator==0);return;}
    assert(out.denominator>0);
    assert(2*(__uint128_t)magnitude(out.numerator)*magnitude(out.numerator)<q);
    assert(2*(__uint128_t)out.denominator*out.denominator<q);
    assert(gcd(magnitude(out.numerator),(uint64_t)out.denominator)==1);
    assert(gcd((uint64_t)out.denominator,q)==1);
    assert(reduce((__int128)out.numerator-(__int128)m*out.denominator,q)==0);
}
// Wide-integer reference checks 64-bit intermediate safety. Exhaustive tests
// below independently enumerate fractions, rather than trusting this recurrence.
static int reference(uint64_t m,uint64_t q,PadicRationalPair *out) {
    *out=(PadicRationalPair){0,0};
    __int128 a=q,b=m,s=0,t=1;
    while(2*b*b>=q) {__int128 k=a/b,r=a-k*b,c=s-k*t;a=b;b=r;s=t;t=c;}
    if(t==0 || 2*t*t>=q || gcd((uint64_t)b,(uint64_t)(t<0?-t:t))!=1) return 0;
    if(t<0) {b=-b;t=-t;}
    *out=(PadicRationalPair){(int64_t)b,(int64_t)t};return 1;
}

static void exhaustive(void) {
    unsigned long cases=0;
    for(uint64_t q=3;q<=1024;q++) {
        PadicRationalPair expected[1024]={{0,0}};
        int64_t limit=(int64_t)bound(q);
        // Construct the complete answer table by enumerating every admissible
        // reduced fraction. Inverses use a brute-force search for independence.
        for(int64_t d=1;d<=limit;d++) {
            if(gcd((uint64_t)d,q)!=1) continue;
            uint64_t inv=1;
            while(((uint64_t)d*inv)%q!=1) inv++;
            for(int64_t n=-limit;n<=limit;n++) {
                if(gcd(magnitude(n),(uint64_t)d)!=1) continue;
                uint64_t m=reduce((__int128)n*inv,q);
                assert(expected[m].denominator==0);
                expected[m]=(PadicRationalPair){n,d};
            }
        }
        for(uint64_t m=0;m<q;m++) {
            PadicRationalPair out={99,99};
            int ok=padic_rational_reconstruct(m,q,&out);
            assert(ok==(expected[m].denominator!=0));
            assert(out.numerator==expected[m].numerator && out.denominator==expected[m].denominator);
            validate(m,q,ok,out);cases++;
        }
    }
    printf("PASS: %lu residues across every modulus 3..1024 against exhaustive fraction enumeration.\n",cases);
}

static void targeted(void) {
    PadicRationalPair out;
    assert(padic_rational_reconstruct(1591,2187,&out));
    assert(out.numerator==5 && out.denominator==11);
    const uint64_t badq[]={0,1,2,UINT64_C(1)<<63,UINT64_MAX};
    for(unsigned i=0;i<sizeof(badq)/sizeof(badq[0]);i++) {
        assert(!padic_rational_reconstruct(0,badq[i],&out));
        assert(out.numerator==0 && out.denominator==0);
    }
    assert(!padic_rational_reconstruct(9,9,&out));
    assert(!padic_rational_reconstruct(UINT64_MAX,INT64_MAX,&out));
    assert(!padic2_reconstruct54(UINT64_C(1)<<54,&out));
    assert(!padic2_reconstruct54(UINT64_MAX,&out));
    assert(!padic_rational_reconstruct(3,9,&out));
    assert(!padic_rational_reconstruct(6,9,&out));
    assert(!padic_rational_reconstruct(32,128,&out)); // Reject 0/4 before cancellation.
    assert(!padic_rational_reconstruct(202,1000,&out)); // Reject unreduced 10/5.
    const uint64_t edge[]={2,3,94906265,UINT64_C(2147483647)};
    for(unsigned i=0;i<sizeof(edge)/sizeof(edge[0]);i++) {
        uint64_t n=edge[i],q=2*n*n;
        assert(!padic_rational_reconstruct(n,q,&out)); // Equality is outside strict bound.
        assert(padic_rational_reconstruct(n,q+1,&out));
        assert(out.numerator==(int64_t)n && out.denominator==1);
        assert(padic_rational_reconstruct(q+1-n,q+1,&out));
        assert(out.numerator==-(int64_t)n && out.denominator==1);
    }
    const uint64_t q=UINT64_C(1)<<54,b=94906265;
    assert(padic2_reconstruct54(b,&out) && out.numerator==(int64_t)b && out.denominator==1);
    assert(padic2_reconstruct54(q-b,&out) && out.numerator==-(int64_t)b && out.denominator==1);
    assert(!padic2_reconstruct54((UINT64_C(1)<<27)+1,&out));
    assert(out.numerator==0 && out.denominator==0);
    // Successful 1 is a bounded candidate for residue 1, not proof that an
    // unknown source was 1 rather than 10 modulo 9.
    assert(padic_rational_reconstruct(1,9,&out) && out.numerator==1 && out.denominator==1);
    printf("PASS: 5/11 modulo 3^7, strict boundaries, input rejection and cancellation traps.\n");
}

static void large_moduli(void) {
    const uint64_t fixed=(UINT64_C(1)<<54);
    for(unsigned i=0;i<100000;i++) {
        uint64_t q;
        switch(i%4) {
            case 0:q=fixed;break;
            case 1:q=INT64_MAX;break;
            case 2:q=(UINT64_C(1)<<(2+i%61))-1;break;
            default:q=(random_word()&INT64_MAX)|3;break;
        }
        uint64_t m=random_word()%q;
        PadicRationalPair actual,expected;
        int ok=padic_rational_reconstruct(m,q,&actual),want=reference(m,q,&expected);
        assert(ok==want && actual.numerator==expected.numerator && actual.denominator==expected.denominator);
        validate(m,q,ok,actual);
        if(q==fixed) {
            PadicRationalPair fast;
            assert(padic2_reconstruct54(m,&fast)==ok);
            assert(fast.numerator==actual.numerator && fast.denominator==actual.denominator);
        }
        uint64_t limit=bound(q),d=1+random_word()%limit;
        while(gcd(d,q)!=1) d=d==limit?1:d+1;
        int64_t n=(int64_t)(random_word()%(2*limit+1))-(int64_t)limit;
        uint64_t common=gcd(magnitude(n),d);
        n/=(int64_t)common;d/=common;
        m=reduce((__int128)n*inverse(d,q),q);
        assert(padic_rational_reconstruct(m,q,&actual));
        assert(actual.numerator==n && actual.denominator==(int64_t)d);
        if(q==fixed) {
            assert(padic2_reconstruct54(m,&actual));
            assert(actual.numerator==n && actual.denominator==(int64_t)d);
        }
    }
    printf("PASS: 100000 large-modulus residues against a 128-bit reference and 100000 known bounded fractions; general/specialized agreement.\n");
}

static void large_quotients(void) {
    const uint64_t qs[]={(UINT64_C(1)<<32)-1,(UINT64_C(1)<<32)+1,
        (UINT64_C(1)<<54)-1,UINT64_C(1)<<54,(UINT64_C(1)<<54)+1,INT64_MAX};
    unsigned cases=0;
    for(unsigned i=0;i<sizeof(qs)/sizeof(qs[0]);i++) {
        uint64_t q=qs[i],limit=bound(q);
        for(uint64_t offset=1;offset<=4096;offset++) {
            // Just beyond the stopping bound: very large first quotients force
            // CLZ alignment, overshoot correction and multi-bit reductions.
            uint64_t m=limit+offset;
            PadicRationalPair actual,expected;
            int ok=padic_rational_reconstruct(m,q,&actual),want=reference(m,q,&expected);
            assert(ok==want && actual.numerator==expected.numerator && actual.denominator==expected.denominator);
            validate(m,q,ok,actual);
            if(q==(UINT64_C(1)<<54)) {
                assert(padic2_reconstruct54(m,&actual)==want);
                assert(actual.numerator==expected.numerator && actual.denominator==expected.denominator);
            }
            cases++;
        }
    }
    printf("PASS: %u large-quotient alignment and subtraction cases through INT64_MAX.\n",cases);
}

static Padic64 word(uint64_t m,int64_t e) {
    return (((uint64_t)e&2047)<<53)|((m&PADIC64_RESIDUE_MASK)>>1);
}
static void packed(void) {
    Padic64Flags flags=PADIC64_DIVZERO;
    Padic64Rational out;
    Padic64 one=word(1,0),three=word(3,0);
    Padic64 third=padic64_div(one,three,&flags);
    assert(padic64_reconstruct(third,&out,&flags));
    assert(out.numerator==1 && out.denominator==3 && out.exponent==0 && flags==PADIC64_DIVZERO);
    for(int e=-1023;e<=1023;e+=1023) {
        uint64_t m=reduce(-5*(__int128)inverse(11,UINT64_C(1)<<54),UINT64_C(1)<<54);
        assert(padic64_reconstruct(word(m,e),&out,&flags));
        assert(out.numerator==-5 && out.denominator==11 && out.exponent==e);
    }
    assert(padic64_reconstruct(PADIC64_ZERO,&out,&flags));
    assert(out.numerator==0 && out.denominator==1 && out.exponent==0 && flags==PADIC64_DIVZERO);
    const Padic64 bad[]={PADIC64_NAN,PADIC64_NEEDS_PRECISION,PADIC64_POS_INFINITY,
        PADIC64_NEG_INFINITY,PADIC64_ZERO|37,word((UINT64_C(1)<<27)+1,0)};
    const Padic64Flags errors[]={0,PADIC64_INSUFFICIENT_PRECISION,PADIC64_INVALID,
        PADIC64_INVALID,PADIC64_INVALID,PADIC64_INSUFFICIENT_PRECISION};
    for(unsigned i=0;i<sizeof(bad)/sizeof(bad[0]);i++) {
        flags=PADIC64_DIVZERO;out=(Padic64Rational){99,99,99};
        assert(!padic64_reconstruct(bad[i],&out,&flags));
        assert(out.numerator==0 && out.denominator==0 && out.exponent==0);
        assert(flags==(PADIC64_DIVZERO|errors[i]));
    }
    printf("PASS: packed 1/3 recovery, exponent restoration, exact zero, special tags and sticky flags.\n");
}

int main(void) {
    _Static_assert(sizeof(PadicRationalPair)==16,"Pair ABI must use two 64-bit fields");
    _Static_assert(sizeof(Padic64Rational)==24,"Packed reconstruction retains the exponent");
    targeted();exhaustive();large_moduli();large_quotients();packed();return 0;
}
