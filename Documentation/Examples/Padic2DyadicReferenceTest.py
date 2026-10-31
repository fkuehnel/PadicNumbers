"""Check the native assembly against Python's exact Fraction -> binary64 conversion.

First build the C test executable as documented in Padic2AArch64Test.c, then:
python3 Documentation/Examples/Padic2DyadicReferenceTest.py /tmp/padic2-test
"""

from fractions import Fraction
import math
import random
import struct
import subprocess
import sys


def expected_bits(residue, exponent, precision):
    modulus = 1 << precision
    signed = residue % modulus
    if signed >= modulus // 2:
        signed -= modulus
    if not signed:
        value = 0.0
    elif exponent > 4096:
        value = math.copysign(math.inf, signed)
    elif exponent < -4096:
        value = math.copysign(0.0, signed)
    else:
        exact = Fraction(signed) * Fraction(2) ** exponent
        try:
            value = float(exact)
        except OverflowError:
            value = math.copysign(math.inf, signed)
    return struct.unpack(">Q", struct.pack(">d", value))[0]


def main():
    rng = random.Random(20261026)
    cases = []
    exponents = [-2**63, -1139, -1138, -1137, -1128, -1076, -1075,
                 -1074, -1073, -1023, -1022, -1000, -64, -1, 0, 1,
                 960, 970, 971, 1022, 1023, 1024, 2**63 - 1]
    for precision in range(1, 65):
        modulus = 1 << precision
        residues = [0, 1, modulus // 2 - 1, modulus // 2, modulus - 1,
                    (1 << 64) - 1]  # Also verify masking of unused high bits.
        for residue in residues:
            for exponent in exponents:
                cases.append((residue, exponent, precision))
        for _ in range(512):
            cases.append((rng.getrandbits(64), rng.randint(-1200, 1100), precision))

    # Halfway cases and adjacent values, including significand/exponent carry,
    # the largest subnormal, and overflow at the largest finite binary64 value.
    for shift in range(1, 12):
        for retained in [(1 << 52), (1 << 52) + 1, (1 << 53) - 1,
                         (1 << 52) - 1, 0]:
            for delta in [-1, 0, 1]:
                magnitude = (retained << shift) + (1 << (shift - 1)) + delta
                if not 0 <= magnitude <= (1 << 63):
                    continue
                for sign in [-1, 1]:
                    if sign == 1 and magnitude == 1 << 63:
                        continue
                    residue = (sign * magnitude) % (1 << 64)
                    for exponent in [-1074 - shift, -shift, 971 - shift]:
                        cases.append((residue, exponent, 64))

    data = "".join(f"{m:x} {e} {r} {expected_bits(m, e, r):x}\n"
                   for m, e, r in cases)
    subprocess.run([sys.argv[1], "--dyadic-vectors"], input=data, text=True, check=True)


if __name__ == "__main__":
    main()
