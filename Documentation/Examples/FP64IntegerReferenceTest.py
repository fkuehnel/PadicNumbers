#!/usr/bin/env python3
"""Exact Fraction oracle, including after-rounding tininess and all four modes.

Usage: python3 FP64IntegerReferenceTest.py /path/to/libfp64-integer.dylib
Python's Fraction-to-float conversion supplies independent nearest-even rounding;
exact rational comparisons then select the neighboring value for directed modes.
No third-party dependencies. FP operations here are reference/test code only.
"""
import ctypes
from fractions import Fraction
from functools import lru_cache
import random
import struct
import sys

SIGN = 1 << 63
INF = 0x7FF0000000000000
QUIET = 1 << 51
FRAC = (1 << 52) - 1
MIN_NORMAL = 1 << 52
INVALID, DIVZERO, OVERFLOW, UNDERFLOW, INEXACT = 1, 2, 4, 8, 16


@lru_cache(maxsize=65536)
def rational(bits):
    magnitude = bits & ~SIGN
    field = magnitude >> 52
    m = magnitude & FRAC
    assert field != 2047
    e = field - 1075 if field else -1074
    if field:
        m |= MIN_NORMAL
    if bits & SIGN:
        m = -m
    return Fraction(m << e, 1) if e >= 0 else Fraction(m, 1 << -e)


def rounded(value, sign, mode):
    value = abs(value)
    try:
        nearest = struct.unpack(">Q", struct.pack(">d", float(value)))[0]
    except OverflowError:
        nearest = INF
    # Map directed rounding to positive-magnitude floor or ceiling.
    ceiling = (mode == 3 and not sign) or (mode == 2 and sign)
    result = nearest
    if mode:
        if nearest == INF:
            result = INF if ceiling else INF - 1
        else:
            represented = rational(nearest)
            if ceiling and represented < value:
                result += 1
            elif not ceiling and represented > value:
                result -= 1
    inexact = result == INF or rational(result) != value
    flags = INEXACT if inexact else 0
    # An unbounded-exponent rounded result overflows at 2^1024. Directed
    # inward rounding of a value just above max finite can be merely inexact.
    if result == INF or value >= (1 << 1024):
        flags |= OVERFLOW | INEXACT
    if inexact and result < MIN_NORMAL:
        flags |= UNDERFLOW
    return result | sign, flags


def reference(op, a, b, mode):
    ma, mb = a & ~SIGN, b & ~SIGN
    if ma > INF or mb > INF:
        signaling = (ma > INF and not a & QUIET) or (mb > INF and not b & QUIET)
        return (a if ma > INF else b) | QUIET, INVALID if signaling else 0
    if op == 1:
        b ^= SIGN
    sign = (a ^ b) & SIGN
    if op < 2:
        if ma == INF or mb == INF:
            if ma == mb and sign:
                return INF | QUIET, INVALID
            return a if ma == INF else b, 0
        value = rational(a) + rational(b)
        if not value:
            zero_sign = a & SIGN if ma == mb == 0 and not sign else (SIGN if mode == 2 else 0)
            return zero_sign, 0
        return rounded(value, SIGN if value < 0 else 0, mode)
    if op == 2:
        if ma == INF or mb == INF:
            return (INF | QUIET, INVALID) if not ma or not mb else (sign | INF, 0)
        if not ma or not mb:
            return sign, 0
        return rounded(rational(a) * rational(b), sign, mode)
    if ma == mb == INF or ma == mb == 0:
        return INF | QUIET, INVALID
    if ma == INF:
        return sign | INF, 0
    if mb == INF:
        return sign, 0
    if not mb:
        return sign | INF, DIVZERO
    if not ma:
        return sign, 0
    return rounded(rational(a) / rational(b), sign, mode)


def main():
    library = ctypes.CDLL(sys.argv[1])
    functions = [getattr(library, "fp64_integer_" + name) for name in ("add", "sub", "mul", "div")]
    for function in functions:
        function.argtypes = [ctypes.c_uint64, ctypes.c_uint64, ctypes.c_int,
                             ctypes.POINTER(ctypes.c_uint32)]
        function.restype = ctypes.c_uint64
    edges = [0, 1, 2, 3, MIN_NORMAL - 2, MIN_NORMAL - 1,
             MIN_NORMAL, MIN_NORMAL + 1, 0x3C90000000000000,
             0x3CA0000000000000, 0x3CB0000000000000, 0x3FE0000000000000,
             0x3FEFFFFFFFFFFFFF, 0x3FF0000000000000, 0x3FF0000000000001,
             0x3FF0000000000002, 0x4000000000000000, 0x4008000000000000,
             0x41A0000002000000, 0x4350000000000000, INF - 2, INF - 1,
             INF, INF | 0x1234, INF | QUIET | 0x4321]
    pairs = [(a | sa, b | sb) for a in edges for b in edges
             for sa in (0, SIGN) for sb in (0, SIGN)]
    rng = random.Random(0x26953)
    pairs.extend((rng.getrandbits(64), rng.getrandbits(64)) for _ in range(2000))
    for gap in (0, 1, 2, 51, 52, 53, 54, 63, 64, 65, 66, 1022, 2045):
        for _ in range(30):
            field = rng.randrange(gap + 1, 2047)
            a = (field << 52) | rng.getrandbits(52)
            b = ((field - gap) << 52) | rng.getrandbits(52)
            pairs.extend(((a, b), (a, b | SIGN), (a | SIGN, b)))
    checks = 0
    for a, b in pairs:
        for mode in range(4):
            for op, function in enumerate(functions):
                expected, expected_flags = reference(op, a, b, mode)
                flags = ctypes.c_uint32(0x80000000)
                actual = function(a, b, mode, ctypes.byref(flags))
                assert (actual, flags.value) == (expected, expected_flags | 0x80000000), (
                    f"op={op} mode={mode} a={a:016x} b={b:016x}: "
                    f"got {actual:016x}/{flags.value:08x}, "
                    f"expected {expected:016x}/{expected_flags:02x}")
                checks += 1
    print(f"PASS: {checks} exact-rational result/flag checks, including NaN payloads and directed rounding.")


if __name__ == "__main__":
    main()
