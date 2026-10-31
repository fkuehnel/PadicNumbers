// Bookkeeping around unchanged AArch64 integer kernels. This models a proposed
// format/status register in software; it does not modify the processor's FPSR.
#include "Padic2Packed64.h"
#include "Padic2AArch64.h"
#include <string.h>

static uint64_t payload(Padic64 x) {return x & ((UINT64_C(1)<<53)-1);}
static int special(Padic64 x) {return (x>>53)==1024;}
static int infinity(Padic64 x) {return x==PADIC64_POS_INFINITY || x==PADIC64_NEG_INFINITY;}
static int malformed(Padic64 x) {return special(x) && payload(x)>4;}
// A finite sign is the centered representative's sign, not an intrinsic Q_2 order.
static int negative(Padic64 x) {
    return x==PADIC64_NEG_INFINITY || (!special(x) && (payload(x)>>52)!=0);
}
static Padic64 signed_infinity(int sign) {
    return sign?PADIC64_NEG_INFINITY:PADIC64_POS_INFINITY;
}
static double fp_bits(uint64_t bits) {double d;memcpy(&d,&bits,8);return d;}
static int64_t exponent(Padic64 x) {
    uint64_t e=x>>53;
    return e<1024 ? (int64_t)e : (int64_t)e-2048;
}
static uint64_t residue(Padic64 x) {return (payload(x)<<1)|1;}
static Padic64 fail(Padic64Flags *flags,Padic64Flags reason,Padic64 result) {
    *flags |= reason;
    return result;
}
static Padic64 pack(uint64_t m,int64_t e,Padic64Flags *flags) {
    if(e < -1023 || e > 1023)
        return fail(flags,PADIC64_EXPONENT_RANGE,PADIC64_NAN);
    return (((uint64_t)e & 2047)<<53) | ((m & PADIC64_RESIDUE_MASK)>>1);
}

// Malformed tags, quiet NaN, then insufficient precision; infinities pass to wrappers.
static int reject(Padic64 a,Padic64 b,Padic64Flags *flags,Padic64 *out) {
    if(malformed(a) || malformed(b)) {
        *out=fail(flags,PADIC64_INVALID,PADIC64_NAN);return 1;
    }
    if(a==PADIC64_NAN || b==PADIC64_NAN) {*out=PADIC64_NAN;return 1;}
    if(a==PADIC64_NEEDS_PRECISION || b==PADIC64_NEEDS_PRECISION) {
        *out=fail(flags,PADIC64_INSUFFICIENT_PRECISION,PADIC64_NEEDS_PRECISION);return 1;
    }
    return 0;
}

Padic64 padic64_from_double(double value,Padic64Flags *flags) {
    uint64_t bits;memcpy(&bits,&value,8);
    if((bits & UINT64_C(0x7ff0000000000000))==UINT64_C(0x7ff0000000000000)) {
        if((bits & UINT64_C(0x000fffffffffffff))==0)
            return signed_infinity((int)(bits>>63));
        if((bits & UINT64_C(0x0008000000000000))==0) *flags |= PADIC64_INVALID;
        return PADIC64_NAN;
    }
    Padic2Decoded p;
    padic2_from_double(value,PADIC64_RESIDUE_MASK,&p);
    if(p.status==PADIC2_EXACT_ZERO) return PADIC64_ZERO;
    if(p.status!=PADIC2_FINITE) return fail(flags,PADIC64_INVALID,PADIC64_NAN);
    return pack(p.residue,p.exponent,flags);
}

double padic64_to_double_dyadic(Padic64 value,Padic64Flags *flags) {
    if(infinity(value)) return fp_bits(value==PADIC64_NEG_INFINITY?
        UINT64_C(0xfff0000000000000):UINT64_C(0x7ff0000000000000));
    Padic64 ignored;
    Padic2Decoded p={0,0,PADIC2_NONFINITE};
    if(!reject(value,PADIC64_ZERO,flags,&ignored)) {
        if(value==PADIC64_ZERO) p.status=PADIC2_EXACT_ZERO;
        else p=(Padic2Decoded){residue(value),exponent(value),PADIC2_FINITE};
    }
    double result=padic2_to_double_dyadic(&p,54);
    uint64_t bits;memcpy(&bits,&result,8);
    if((bits & UINT64_C(0x7fffffffffffffff))==UINT64_C(0x7ff0000000000000))
        *flags |= PADIC64_FP_OVERFLOW;
    return result;
}

static Padic64 addsub(Padic64 a,Padic64 b,int subtract,Padic64Flags *flags) {
    Padic64 out;
    if(reject(a,b,flags,&out)) return out;
    if(infinity(a) || infinity(b)) {
        int bsign=negative(b)^subtract;
        if(infinity(a) && infinity(b) && negative(a)!=bsign)
            return fail(flags,PADIC64_INVALID,PADIC64_NAN);
        return infinity(a)?a:signed_infinity(bsign);
    }
    if(b==PADIC64_ZERO) return a;
    if(a==PADIC64_ZERO) return subtract?padic64_neg(b,flags):b;
    int64_t ea=exponent(a),eb=exponent(b),e=ea<eb?ea:eb;
    uint64_t ma=residue(a),mb=residue(b);
    uint64_t m=subtract?padic2_sub(ma,mb,PADIC64_RESIDUE_MASK,ea,eb):
                        padic2_add(ma,mb,PADIC64_RESIDUE_MASK,ea,eb);
    // Common absolute precision is e+54. An even result would have fewer
    // than 54 relative bits after normalization; a zero residue is O(2^(e+54)).
    if((m&1)==0)
        return fail(flags,PADIC64_PRECISION_LOST|PADIC64_INSUFFICIENT_PRECISION,
                    PADIC64_NEEDS_PRECISION);
    return pack(m,e,flags);
}
Padic64 padic64_add(Padic64 a,Padic64 b,Padic64Flags *flags) {return addsub(a,b,0,flags);}
Padic64 padic64_sub(Padic64 a,Padic64 b,Padic64Flags *flags) {return addsub(a,b,1,flags);}
Padic64 padic64_neg(Padic64 a,Padic64Flags *flags) {
    Padic64 out;
    if(reject(a,PADIC64_ZERO,flags,&out)) return out;
    if(infinity(a)) return signed_infinity(!negative(a));
    if(a==PADIC64_ZERO) return a;
    return pack(padic2_neg(residue(a),0,PADIC64_RESIDUE_MASK),exponent(a),flags);
}
Padic64 padic64_mul(Padic64 a,Padic64 b,Padic64Flags *flags) {
    Padic64 out;
    if(reject(a,b,flags,&out)) return out;
    if(infinity(a) || infinity(b)) {
        if(a==PADIC64_ZERO || b==PADIC64_ZERO)
            return fail(flags,PADIC64_INVALID,PADIC64_NAN);
        return signed_infinity(negative(a)^negative(b));
    }
    if(a==PADIC64_ZERO || b==PADIC64_ZERO) return PADIC64_ZERO;
    return pack(padic2_mul(residue(a),residue(b),PADIC64_RESIDUE_MASK),
                exponent(a)+exponent(b),flags);
}
Padic64 padic64_div(Padic64 a,Padic64 b,Padic64Flags *flags) {
    Padic64 out;
    if(reject(a,b,flags,&out)) return out;
    if(infinity(a) && infinity(b)) return fail(flags,PADIC64_INVALID,PADIC64_NAN);
    if(infinity(a)) return signed_infinity(negative(a)^negative(b));
    if(infinity(b)) return PADIC64_ZERO;
    if(b==PADIC64_ZERO) return fail(flags,PADIC64_DIVZERO|PADIC64_INVALID,PADIC64_NAN);
    if(a==PADIC64_ZERO) return PADIC64_ZERO;
    return pack(padic2_div(residue(a),residue(b),PADIC64_RESIDUE_MASK),
                exponent(a)-exponent(b),flags);
}

static int64_t signed_unit(Padic64 x) {
    if(x==PADIC64_ZERO) return 0;
    uint64_t m=residue(x);
    return (int64_t)m - ((m>>53)?(INT64_C(1)<<54):0);
}
Padic64Comparison padic64_compare_dyadic(Padic64 a,Padic64 b,Padic64Flags *flags) {
    Padic64 ignored;
    if(reject(a,b,flags,&ignored)) return PADIC64_CMP_UNORDERED;
    if(infinity(a) || infinity(b)) {
        if(a==b) return PADIC64_CMP_EQ;
        return a==PADIC64_NEG_INFINITY || b==PADIC64_POS_INFINITY?
            PADIC64_CMP_LT:PADIC64_CMP_GT;
    }
    int order=padic2_compare_dyadic_units(signed_unit(a),a==PADIC64_ZERO?0:exponent(a),
                                        signed_unit(b),b==PADIC64_ZERO?0:exponent(b));
    return order<0?PADIC64_CMP_LT:order>0?PADIC64_CMP_GT:PADIC64_CMP_EQ;
}

Padic64 padic64_pow(Padic64 a,int64_t power,Padic64Flags *flags) {
    Padic64 out;
    if(reject(a,PADIC64_ZERO,flags,&out)) return out;
    if(infinity(a)) {
        if(power==0) return pack(1,0,flags);
        if(power<0) return PADIC64_ZERO;
        return signed_infinity(negative(a) && (power%2!=0));
    }
    if(a==PADIC64_ZERO) {
        if(power>0) return PADIC64_ZERO;
        return fail(flags,PADIC64_INVALID|(power<0?PADIC64_DIVZERO:0),PADIC64_NAN);
    }
    int64_t e;
    if(__builtin_mul_overflow(exponent(a),power,&e) || e < -1023 || e > 1023)
        return fail(flags,PADIC64_EXPONENT_RANGE,PADIC64_NAN);
    uint64_t m=residue(a);
    uint64_t k=power<0?UINT64_C(0)-(uint64_t)power:(uint64_t)power;
    if(power<0) m=padic2_div(1,m,PADIC64_RESIDUE_MASK);
    return pack(padic2_pow_unit(m,k,PADIC64_RESIDUE_MASK),e,flags);
}

static int sqrt_domain(Padic64 a,Padic64Flags *flags,Padic64 *out) {
    if(reject(a,PADIC64_ZERO,flags,out)) return 0;
    if(a==PADIC64_POS_INFINITY) {*out=a;return 0;}
    if(a==PADIC64_NEG_INFINITY) {*out=fail(flags,PADIC64_INVALID,PADIC64_NAN);return 0;}
    if(a!=PADIC64_ZERO && (exponent(a)%2!=0 || (residue(a)&7)!=1)) {
        *out=fail(flags,PADIC64_INVALID,PADIC64_NAN);return 0;
    }
    return 1;
}
Padic64 padic64_sqrt(Padic64 a,Padic64Flags *flags) {
    Padic64 out;
    if(!sqrt_domain(a,flags,&out)) return out;
    if(a==PADIC64_ZERO) return PADIC64_ZERO;
    return fail(flags,PADIC64_PRECISION_LOST|PADIC64_INSUFFICIENT_PRECISION,
                PADIC64_NEEDS_PRECISION);
}
Padic64 padic64_sqrt_refined(Padic64 a,uint64_t refined_unit,Padic64Flags *flags) {
    Padic64 out;
    if(!sqrt_domain(a,flags,&out)) return out;
    if(a==PADIC64_ZERO) {
        if(refined_unit==0) return PADIC64_ZERO;
        return fail(flags,PADIC64_INVALID,PADIC64_NAN);
    }
    if(refined_unit>=(UINT64_C(1)<<55) ||
       (refined_unit&PADIC64_RESIDUE_MASK)!=residue(a))
        return fail(flags,PADIC64_INVALID,PADIC64_NAN);
    return pack(padic2_sqrt_unit(refined_unit,PADIC64_RESIDUE_MASK),exponent(a)/2,flags);
}

int padic64_reconstruct(Padic64 value,Padic64Rational *out,Padic64Flags *flags) {
    *out=(Padic64Rational){0,0,0};
    Padic64 ignored;
    if(reject(value,PADIC64_ZERO,flags,&ignored)) return 0;
    if(infinity(value)) {*flags |= PADIC64_INVALID;return 0;}
    if(value==PADIC64_ZERO) {out->denominator=1;return 1;}
    PadicRationalPair pair;
    if(!padic2_reconstruct54(residue(value),&pair)) {
        *flags |= PADIC64_INSUFFICIENT_PRECISION;return 0;
    }
    *out=(Padic64Rational){pair.numerator,pair.denominator,exponent(value)};
    return 1;
}
