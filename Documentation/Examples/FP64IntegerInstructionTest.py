#!/usr/bin/env python3
"""Audit the optimized ARM64 core and its only external arithmetic primitive."""
from pathlib import Path
import re
import subprocess
import sys


def disassemble(path):
    listing = subprocess.check_output(["otool", "-tvV", str(path)], text=True)
    path.with_suffix(".disassembly.txt").write_text(listing)
    return listing


def instructions(listing):
    code = re.findall(r"^[0-9a-f]{16}[ \t]+([a-z0-9.]+)[ \t]*(.*)$", listing, re.MULTILINE)
    assert len(code) == len(re.findall(r"^[0-9a-f]{16}[ \t]", listing, re.MULTILINE))
    return code


def main():
    core, kernels = map(Path, sys.argv[1:])
    listing = disassemble(core)
    code = instructions(listing)
    assert code, "No decoded instructions; audit would be vacuous"
    for mnemonic, operands in code:
        assert not mnemonic.startswith("f"), (mnemonic, operands)
        assert not re.search(r"\b[bhdsqv](?:[0-9]|[12][0-9]|3[01])\b", operands), (mnemonic, operands)
        assert mnemonic not in ("udiv", "sdiv"), (mnemonic, operands)
        assert not re.search(r"\b(?:fpcr|fpsr)\b", operands, re.IGNORECASE), (mnemonic, operands)
    undefined = subprocess.check_output(["nm", "-u", str(core)], text=True).split()
    assert undefined == ["_integer_mul_wide"], undefined
    helper = disassemble(kernels).split("_integer_mul_wide:\n", 1)[1].split("\n_", 1)[0]
    assert instructions(helper) == [
        ("mul", "x2, x0, x1"), ("umulh", "x1, x0, x1"),
        ("mov", "x0, x2"), ("ret", "")
    ], helper
    print(f"PASS: {len(code)} core instructions use no FP/SIMD registers, FP state, or divide instructions.")
    print("PASS: sole external dependency is the four-instruction MUL/UMULH primitive.")


if __name__ == "__main__":
    main()
