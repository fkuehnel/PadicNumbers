# Integer-only FP64 second path

The ARM64 demo now has two arithmetic paths using integer instructions:

| Path | Input/output | Precision rule |
|---|---|---|
| Existing `padic2_*` / `padic64_*` | Decoded residues / packed p-adic words | Retain the low valuation-relative residue window |
| New `fp64_integer_*` | Raw IEEE binary64 `uint64_t` words | Retain enough information to round each real operation once |

The existing p-adic operations keep their contracts. The second path implements
**add, subtract, multiply and divide**, all four rounding modes (nearest-even,
toward zero, downward, upward), gradual underflow, signed zeros and infinities,
NaN handling, and caller-owned sticky exception flags. See [FP64Integer.h](FP64Integer.h)
for the interface and [FP64Integer.c](FP64Integer.c) for the implementation.

```c
FP64Flags flags = 0;
uint64_t result = fp64_integer_div(
    UINT64_C(0x3ff0000000000000), // 1.0
    UINT64_C(0x4008000000000000), // 3.0
    FP64_NEAREST_EVEN, &flags);
// result = 0x3fd5555555555555, flags = FP64_INEXACT.
```

Raw input words preserve all source bits without the range or metadata losses
of conversion through `Padic64`. Arithmetic quiets signaling NaNs, sets INVALID
if either input is signaling, and propagates the first NaN input's sign and
payload. Invalid operations without a NaN input produce `0x7ff8000000000000`.
The chosen underflow policy detects tininess **after rounding**: a tiny inexact
result rounded up to the minimum normal raises INEXACT but not UNDERFLOW.
Native ARM underflow flags can differ at that boundary. Hardware FPCR/FPSR
are not read or modified by the second path.

## Shared multiplication and rounding

Both paths use ordinary integer multiplication. The existing modular kernel
needs only `MUL` and a mask. The new `integer_mul_wide` primitive alongside it
uses `MUL` and `UMULH` to return an exact 128-bit product. Two unsigned 53-bit
significands occupy at most 106 product bits; sign and exponent are separate.
`FP64Integer.c` includes [Padic2AArch64.h](Padic2AArch64.h) and calls this
primitive in [Padic2AArch64.s](Padic2AArch64.s) for both multiplication and
reciprocal-based division. The modular `padic2_div` retains its own low-bit
Newton–Hensel iteration; its reciprocal is not a real reciprocal.
There is no bit reversal, modular truncation, or rational reconstruction in
the FP64 multiplication path. Normalization and rounding happen after the
complete product is available.

Addition/subtraction align exactly in a 128-bit workspace for exponent gaps
up to 64. This covers severe cancellation. For larger gaps the smaller input
is summarized by a positive fractional tail below three guard positions;
subtraction explicitly accounts for its borrow. Division refines a real
reciprocal, multiplies it by the numerator, and corrects the quotient using
an exact remainder. It retains 56 fractional quotient bits for final rounding.

All four operations use one `round_pack` routine. Its inputs specify an integer
magnitude, binary exponent, and any nonzero fractional tail. It performs one
rounding at the final normal or subnormal boundary, including rounding carries,
overflow, directed rounding, and software flags. No intermediate FP conversion
or double rounding is involved.

This implements the integer-significand route in
[One Convolution, Three Arithmetics](../English/Guides/ConvolutionArithmetics.md).
It demonstrates shared integer primitives and distinct precision policies;
it does not measure circuit area, power, or superiority to native FP hardware.

## Division by reciprocal refinement

After unpacking, numerator `A` and divisor `D` satisfy
`2^52 <= A,D < 2^53`, including normalized subnormal inputs. `D` can be odd
or even. The bit-length seed from the tutorial is therefore always `R0=2^-53`.
Keep the reciprocal in fixed point as `R=r/2^115`: the seed is `r=2^62`,
and the exact scaled target `T=2^115/D` lies in `(2^62,2^63]`.

Six Newton updates implement `R <- R + R*(1-D*R) = R*(2-D*R)`:

```text
r = 2^62
repeat six times:
    residual = 2^115 - D*r
    e = floor(residual / 2^52)
    r = r + floor(r*e / 2^63)
```

Here `e` encodes the residual with 63 fractional bits. Each iteration calls
the shared `integer_mul_wide` twice; both full products fit in 128 bits.
The powers of two are shifts, with no floating-point or integer divide
instructions. The resulting quotient and remainder are:

```text
q = floor(A*r / 2^59)
rem = A*2^56 - q*D
if rem >= D:
    q = q + 1
    rem = rem - D
```

There is one numerator-times-reciprocal multiplication and one additional
product `q*D` to certify the result. At most one upward correction is needed;
after it, `q=floor(A*2^56/D)` and `0 <= rem < D`. `round_pack` receives `q`,
the adjusted exponent, and `rem != 0` as its exact sticky bit. Rounding a
reciprocal to binary64 before multiplying would not provide this guarantee.

**Why six updates and one correction suffice.** Let `delta=T-r >= 0`.
Truncating the residual loses less than `r/2^63 <= 1` in the next iterate;
truncating the update loses less than one more unit. Thus each iterate stays
below `T`, with `delta_next < delta^2/T + 2`. In relative form,
`epsilon_next < epsilon^2 + 2^-61`, starting from `epsilon <= 1/2`.
For `1 <= k <= 5`, induction gives
`epsilon_k < 2^(-2^k) + k*2^-61`, hence `epsilon_5 < 2^-31` and
`epsilon_6 < 3*2^-62`. Since `T <= 2^63`, this proves `0 <= T-r < 6`.
The quotient estimate before flooring is therefore less than
`A*6/2^59 < 6/64 < 1` below the exact quotient, so its floor is correct or
one too small. All products and corrections use exact integer arithmetic.
This bound concerns the implemented truncations, not only ideal Newton
convergence; it does not assume that discarded reciprocal bits are zero.

## Run the demo and checks

On ARM64 macOS with Apple Clang and Python 3, from the repository root:

```sh
bash Documentation/Examples/FP64IntegerCheck.sh
```

An optional first argument chooses the build directory. By default a fresh
directory under `/private/tmp` retains binaries, the comparison output, and
disassembly listings. [FP64IntegerComparison.c](FP64IntegerComparison.c) displays
the p-adic export, integer FP64 result and native FP64 result side by side.
Floating-point operations appear only in reference/test/presentation code and
the pre-existing p-adic conversion interface; the second path itself is
compiled with `-mgeneral-regs-only`.

Validation performed on ARM64 macOS:

- **240,958 reciprocal-bound and exact quotient/remainder checks**, including
  normalized endpoints, odd/even divisors, exact quotients, and random pairs.
  Independent 128-bit integer division checks both correction outcomes:
  129,547 estimates need one correction and 111,411 are already exact.
- **2,843,204 native result/flag comparisons**, including all four operations
  and rounding modes, signs, subnormals, overflow, cancellation, alignment gaps,
  infinities and NaNs. NaN payload policy is checked separately from native
  payload selection. There were 116 expected native before-rounding tininess
  differences at the minimum-normal boundary.
- **90,720 independent exact-rational checks** using Python `Fraction`, including
  directed rounding, exact output bits, NaN payload policy, and all software flags.
- Optimized instruction/dependency audit: no FP/SIMD registers, FP state access,
  or integer divide instructions in the FP64 core; its only external dependency
  is the four-instruction `MUL`/`UMULH` primitive.
- Undefined-behavior sanitization and the existing decoded/packed p-adic tests.

These are implementation tests, not an exhaustive proof over every operand
pair. This path covers the four basic binary operations; it does not implement
FMA, square root, decimal conversions, traps, or all processor-specific FPCR
modes. Formal machine-checked proofs and performance comparisons remain future
work. Its software flags are a separate enum from `Padic64Flags`.
