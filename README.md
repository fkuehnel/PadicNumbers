# PadicNumbers

**Exact rational and finite-precision p-adic arithmetic, with refinable square roots in Mathematica.**

A Wolfram paclet implementing exact p-adic representations of rationals, including
periodic expansions, finite-precision approximations, rational reconstruction,
refinable p-adic square roots, and tree visualization.

---

## Installation

### Development install (local source)

Place the `PadicNumbers` folder anywhere on your machine, then:

```mathematica
PacletDirectoryLoad["/path/to/parent/folder"];
PacletInstall["PadicNumbers"];
Needs["PadicNumbers`"]
```

`PacletDirectoryLoad` registers the directory for the current session.
To make it permanent across restarts, add the `PacletDirectoryLoad` line
to your Mathematica init file at:

```
$UserBaseDirectory/Kernel/init.m
```

### Published install (Wolfram Paclet Repository)

Once published to the Wolfram Paclet Repository, installation becomes a single line:

```mathematica
PacletInstall["FrankKuehnel/PadicNumbers"]
Needs["PadicNumbers`"]
```

No directory setup, no `PacletDirectoryLoad` — Mathematica handles everything.
Updates can then be installed with:

```mathematica
PacletUpdate["FrankKuehnel/PadicNumbers"]
```

### Uninstall

```mathematica
PacletUninstall["PadicNumbers"]
```

---

## Quick Start

```mathematica
(* Exact p-adic representation of a rational *)
Padic[1/3, 7]          (* 7-adic expansion of 1/3 *)
Padic[-1/6, 5]         (* 5-adic expansion of -1/6 *)

(* P-adic order and absolute value *)
PadicOrder[1/3, 3]     (* -> -1 *)
PadicAbs[1/3, 3]       (* -> 3  *)

(* Exact arithmetic *)
Padic[1/3, 7] + Padic[1/7, 7]
Padic[1/3, 7] * Padic[2/5, 7]

(* Convert back to rational *)
Normal[Padic[1/3, 7]]  (* -> 1/3 *)
```

---

## Digit Display

Exact and finite-precision expansions use ordinary digit characters below base
10, and uppercase letters `A = 10`, `B = 11`, ..., `Z = 35` for bases through
36. For example, base 11 uses `0`–`9`, `A`; base 13 extends through `C`; base
17 through `G`; and base 31 through `U`. The existing spacing between digits
is retained.

At prime bases 37 and above, every digit is an ordinary decimal integer,
separated by `|`: for example, `12|36|4|10`. The cutoff at 36 is a display
policy, not an arithmetic limit. The radix point separates the integer and
fractional digit runs, as in `10.12|36`.

An overbar marks the block repeating toward the left. Its length counts
digits, including when decimal digit values take multiple characters. A bar
separator also marks the boundary between a repeating block and its finite
suffix at large bases. Existing scale-factor and finite-precision `~`/`O(...)`
displays are retained.

```mathematica
Padic[10, 11]                  (* one digit: A *)
Padic[11, 11]                  (* two digits: 1 0 *)
Padic[321/49, 13]              (* repeating 3 5 A B 5 3 C 9 7 2 1 7 9 0, suffix A *)
Padic[12*37 + 36, 37]          (* 12|36, subscript 37 *)
PadicN[12*37 + 36, 37, 2]     (* ~12|36, subscript 37 *)
PadicDigits[Padic[10, 11]]     (* {10}: digit data stays numeric *)
```

---

## Lossy (Approximate) Representation

```mathematica
(* Store as truncated p-adic expansion — drops periodicity *)
x = PadicN[1/3, 7, 8]      (* 8 digits of 7-adic precision *)

(* Reconstruct rational via RATCONVERT *)
Normal[x]                   (* -> 1/3 if precision is sufficient *)

(* Arithmetic works with different valuations and precisions *)
a = PadicN[1/3, 7, 8];
b = PadicN[1/7, 7, 5];
{a + b, a - b, a b, a/b, -a, a^-3}

(* Integer/rational scalars and exact Padic operands retain their exactness *)
{2 a, a + 1/49, a Padic[3/5, 7]}
```

### Lazy sources and late precision

`Padic[r,p]` remains the exact periodic constructor. `PadicN[r,p]` now retains
the exact rational source in a public `PadicLazy[expression,p]` object. Addition, subtraction,
multiplication, division, and integer powers build recipes. Request a finite
snapshot with three arguments, or use `Normal` for certified reconstruction:

```mathematica
s = PadicN[73/187,5] + PadicN[-3,5];
Normal[s]                  (* -488/187 *)
PadicN[s,5,Automatic]      (* PadicRationalN[898226,5,0,9] in FullForm *)
PadicN[s,5,2]              (* 1 + O(5^2), a finite snapshot *)
Normal[s]                  (* still -488/187; the sources remain intact *)
```

The recipe uses ordinary rational leaves and inactive arithmetic:

```mathematica
PadicN[73/187,5] // InputForm
(* PadicLazy[73/187,5] *)
s // InputForm
(* PadicLazy[Inactive[Plus][-3,73/187],5] *)
TreeForm[First[s]]         (* inspect the retained expression tree *)
```

`FullForm` exposes the same public structure, with fractions written as
`Rational[numerator,denominator]`. Inactive operations prevent premature
rational arithmetic. `First[s]` is the recipe and `Last[s]` is the base;
neither inspection requests more digits. `Activate[First[s]]` would explicitly
perform ordinary rational arithmetic, bypassing the package's modular evaluator.
For recipes containing square roots, activation also applies real/complex
branch conventions and does not preserve their p-adic meaning.
Direct construction of arbitrary recipes is not validated; use `PadicN` and
the arithmetic operators to build supported expressions.

The sum's numerator is bounded by `73 + 3*187 = 634`, its denominator by
`187`. Nine digits satisfy `5^n > 2*634^2`, without computing the exact
rational sum. Evaluation requests enough digits from each source and uses
modular arithmetic. `Normal` certifies its result from these bounds; it never
uses an intermediate finite object's `Normal` fallback. Bounds can overestimate
the required precision, particularly after cancellation.

Printing preserves the recipe in an `InterpretationBox`. Sources display at
most ten digits, or their smaller reconstruction precision; compound recipes
display ten relative digits. Printing or requesting a low-precision snapshot
does not limit later refinement. `PadicDigits[lazy]` returns preview digits;
use `PadicDigits[PadicN[lazy,p,n]]` for an explicit precision. Lazy digit-tree
rays request the required normalized unit digits directly.

Lazy rational-source operands may use the smaller prime base. If an operand
is already a finite snapshot, its base must match and its precision remains
a hard limit; an exact-zero summand can return the lazy operand unchanged.
The lazy implementation supports retained rational sources and square-root
recipes, not arbitrary digit generators or lattice precision. Recipes containing
roots remain tied to their prime; they cannot be implicitly combined with or
converted to a different base. Metadata is memoized
within each request; no persistent cache is retained. Bounds, cancellation,
and inverse checks can still make a request expensive.

### Eager automatic precision

`PadicN[r,p,Automatic]` selects the least positive relative
precision satisfying the symmetric rational-reconstruction bound for the
**normalized** fraction. For nonzero `r`, write

\[
r=p^e\frac{u}{v},\qquad \gcd(u,v)=1,\quad v>0,\quad p\nmid uv,
\qquad H=\max(|u|,v).
\]

The selected precision is

\[
n_{\min}=\min\{n\ge1:p^n>2H^2\}.
\]

This places both the numerator and denominator strictly below
\(\sqrt{p^n/2}\), where the reduced rational representative is unique. The
valuation `e` is retained separately and restored after reconstruction.
See [Wang, Guy, and Davenport (1982)](https://www.cecm.sfu.ca/personal/mmonagan/teaching/TopicsinCA13/GuyDavenWang.pdf).
The implementation uses `IntegerLength[2 H^2,p]`, avoiding floating-point
logarithms and treating exact power boundaries correctly. See
[Wolfram's IntegerLength documentation](https://reference.wolfram.com/language/ref/IntegerLength.html).

```mathematica
a = PadicN[73/187, 5, Automatic];
FullForm[a]                 (* PadicRationalN[38854,5,0,7] *)
Normal[a]                   (* 73/187: seven digits suffice; the exact period is 80 *)

PadicN[1/1000000007, 5, Automatic] (* 27 digits, without constructing the billion-digit cycle *)
PadicN[125/3, 5, Automatic]        (* valuation 3; precision chosen for the unit 1/3 *)
PadicN[0, 5, Automatic]            (* exact zero, with precision field 1 *)
```

This is the minimum under the stated symmetric sufficient bound. Other bounds
or reconstruction methods may need fewer digits. Matching a rational through
`Normal` at a lower precision, particularly through its integer fallback,
does not establish this guarantee.

Automatic precision applies to the exact input being converted. Arithmetic
can produce a result with a larger numerator or denominator, so its recovery
may require more precision than either input's automatic choice. Use a common
explicit precision when computing a result that must later be reconstructed:

```mathematica
Normal[PadicN[3/11,5,7] + PadicN[2/17,5,7]]  (* 73/187 *)
```

`PadicN[exactObject]` uses that object's base and retains its rational value lazily.
For an existing approximation, omitted precision or `Automatic` preserves the
known precision; the original exact rational is unavailable for selecting a
new bound. Request additional digits from the original exact input.

**Compatibility:** omitted precision now creates a lazy source. Write
`PadicN[r,p,Automatic]` for the previous minimal-bound eager behavior, or
`PadicN[r,p,8]` for the older eight-digit default. Every explicit positive
integer precision keeps its existing meaning. Existing `PadicRationalN`
objects do not become lazy when passed through `PadicN`.

### Arithmetic and reconstruction

Arithmetic operates directly on modular residues. Addition uses the common
absolute precision and accounts for cancellation; multiplication and inversion
track relative precision. Integer powers also retain precision gained by the
power map, including the special case of even powers of odd 2-adic units.
For example, `PadicN[1,2,1]^2` is known modulo 8.

Exact scalars add no uncertainty. Thus `1 + PadicN[25,5,4]` has six digits of
relative precision, preserving the original absolute precision. Arithmetic
involving an approximate p-adic object requires the same prime base for all
p-adic operands. Inversion of exact zero
or a value indistinguishable from zero emits a message and returns
`Indeterminate`.

`PadicN[exactPadic,p,n]` constructs the requested approximation directly from
the exact value. `PadicN[existingApproximation,p,n]` can reduce its relative
precision; requesting more digits leaves the known precision unchanged.
Converting an existing approximation to a different base is rejected.
Constructors require a prime base and a positive integer precision.

For a finite snapshot, `Normal` validates reconstructed fractions against the stored residue and
precision. If no bounded fraction passes validation, it returns the stored
integer representative, scaled by its valuation. For arbitrary approximations
this is a candidate for the original rational. Automatic construction from an
exact rational chooses enough digits to guarantee that input's recovery;
later truncation or arithmetic can lose that guarantee.

Exact zero and a zero residue with finite precision are distinct:

```mathematica
Normal[PadicN[0, 5, 4]]       (* 0: exact zero *)
z = PadicN[1, 5, 1] + PadicN[4, 5, 1]  (* O(5^1) *)
PadicOrder[z]                 (* Interval[{1, Infinity}] *)
PadicAbs[z]                   (* Interval[{0, 1/5}] *)
Normal[z]                    (* Missing["InsufficientPrecision", 1] *)
```

For `PadicRationalN[m,p,e,N]`, absolute precision is `e+N`. A finite-precision
zero retains this bound; its true valuation is unknown. Exact zero uses the
explicit marker `PadicRationalN[0,p,Infinity,N]`.

---

## Visualization

```mathematica
(* 3-adic tree to depth 4 *)
PadicDigitTree[3, 4]

(* Highlight the ray corresponding to 1/3 *)
PadicDigitTree[3, 4, RayDigits -> Padic[1/3, 3]]

(* Highlight multiple rationals *)
PadicDigitTree[3, 5, RayDigits -> {Padic[1/3, 3], Padic[2/3, 3]}]

(* With sector background coloring *)
PadicDigitTree[3, 4, SectorBackground -> True, SectorOpacity -> 0.1]

(* Top-down tree layout *)
PadicDigitTree[3, 4, Layout -> "TopDown"]
```

The custom option names are exported in `PadicNumbers\`` and can be passed
directly after loading the package. Paths specified as integer lists run from
the lowest digit outward, starting at the root.

| Option | Default | Accepted values or meaning |
|--------|---------|----------------------------|
| `RayDigits` | `None` | One digit list, multiple digit lists, exact/lazy/finite objects, or a mixture |
| `Layout` | `"Hyperbolic"` | `"Hyperbolic"`, `"TopDown"`, or `"Tree"` |
| `VertexLabelMode` | `"None"` | `"None"`, `"FirstLayer"`, `"Ray"`, `"All"` |
| `EdgeLabelMode` | `"Ray"` | `"None"`, `"FirstLevel"`, `"Ray"`, `"All"` |
| `DigitColors` | `Automatic` | An association from integer digits to colors, or at least `p` colors in a list |
| `SectorBackground` | `False` | Shade sectors in the hyperbolic layout |
| `SectorBackgroundDepth` | `1` | Number of sector levels to shade |
| `SectorOpacity` | `0.07` | Base opacity, reduced at deeper levels |
| `CantorBoundary` | `False` | Add the boundary overlay in the hyperbolic layout |
| `CantorDustRadius` | `1.12` | Boundary radius |
| `CantorPointSize` | `2` | Boundary dot size |
| `ImageSize` | `900` | Wolfram graphics image size |
| `Background` | `None` | Wolfram graphics background |

The tree accepts integer branching bases greater than one; its p-adic
interpretation uses a prime base. Automatic depth targets about 3,000 edges.
Explicit depth is reduced toward a 10,000-edge budget when possible; even
depth one can exceed that budget for a very large branching base.

Current visualization boundaries: object paths show the normalized unit and
do not apply the object's valuation. Finite snapshot paths are generated
from a reconstructed rational candidate and can extend beyond the stored
precision. Lazy paths request the required digits directly. Use explicit digit
lists to display only a known finite prefix. Tree
labels use decimal values; concatenated path labels can be ambiguous above
base 10. The expansion formatter's letter/bar policy applies to number
displays, not these tree labels.

---

## Public API

Use `?PadicN`, `?PadicDigits`, etc. in a Wolfram kernel to read each symbol's
usage text. Only `Padic` and `PadicN` automatically thread over lists.

### Construction and conversion

| Symbol | Description |
|--------|-------------|
| `Padic[r,p]` | Construct the exact eventually periodic expansion of an integer or rational; `p` must be prime |
| `Padic[s]`, `Padic[s,p]` | Keep an exact object or convert it to base `p`; certify lazy values with `Normal`; for a finite snapshot, promote `Normal[s]`'s candidate, propagating an uncertain zero's `Missing` result |
| `PadicN[r,p]` | Retain an exact rational source lazily; arithmetic builds refinable recipes |
| `PadicN[r,p,Automatic]` | Eagerly approximate an exact rational at the minimum symmetric reconstruction precision |
| `PadicN[r,p,n]` | Construct an approximation with exactly `n` digits of relative precision; require prime `p` and positive integer `n` |
| `PadicN[s]` | Retain an exact object's value lazily, preserve a lazy recipe, or canonicalize an existing finite approximation |
| `PadicN[s,p,n]` | Evaluate a lazy recipe, convert an exact object, or truncate a finite approximation without increasing known precision; `Automatic` uses sufficient bounds for lazy recipes |
| `PadicRational[m,p,e,n,k]` | Exact representation head: packed normalized digits, base, valuation, stored digit count, repeating digit count |
| `PadicRationalN[m,p,e,n]` | Approximate representation head for `m p^e + O(p^(e+n))`; exact zero uses `e=Infinity` |
| `PadicLazy[expression,p]` | Lazy representation head retaining rational sources and inactive arithmetic; inspect the recipe with `First[s]` or `TreeForm[First[s]]` |

Prefer the constructors to assembling representation heads directly: the heads
do not validate their fields. Exact construction stores one complete period,
which can be much larger than the original rational. Exact `Normal` always
returns the represented rational; lazy `Normal` certifies reconstruction from
retained sources and bounds; finite `Normal` follows the bounded
reconstruction and fallback rules above. `Padic[sApprox]` therefore constructs
an exact expansion of a candidate and does not certify the unknown original.
Here `sApprox` means a finite `PadicRationalN`, not a retained lazy source.

### Valuation, normalization, and inspection

| Symbol | Description |
|--------|-------------|
| `PadicOrder[r,p]` | Valuation of an integer or rational; zero gives `Infinity` |
| `PadicOrder[s]`, `PadicOrder[s,p]` | Use the object's base, or inspect an exact or lazy value at another base; a finite snapshot supports only its stored base |
| `PadicAbs[r,p]`, `PadicAbs[s]`, `PadicAbs[s,p]` | Corresponding p-adic absolute value, with value zero at exact zero; approximate zeros return interval bounds |
| `PadicNormalize[r,p]`, `PadicNormalize[s]` | Remove the valuation; object normalization retains the unit's relative precision, and leaves zero objects unchanged |
| `PadicCanonicalize[s]` | Rebuild an exact canonical expansion; normalize a finite residue while preserving absolute precision; return a lazy recipe unchanged |
| `PadicSignature[r,p]`, `PadicSignature[s]`, `PadicSignature[s,p]` | Return `{n,k}` for the normalized exact expansion; `n-k` is the nonrepeating digit count; zero gives `{0,0}` |
| `PadicPeriodLength[r,p]`, `PadicPeriodLength[s]`, `PadicPeriodLength[s,p]` | Compute the minimal eventual period of an exact rational without constructing its cycle; positive integers and zero give `0`, negative integers give `1` |
| `PadicDigits[s]`, `PadicDigits[r,p]`, `PadicDigits[s,p]` | Return integer digits from highest to lowest place; a finite snapshot with explicit matching base retains its stored digits, and another base is rejected; lazy values return preview digits |
| `PadicDigitTree[p]`, `PadicDigitTree[p,depth,opts]` | Draw the digit tree with automatic or explicit positive depth; see the option table and visualization boundaries above |

`PadicOrder`, `PadicAbs`, and scalar `PadicNormalize` accept integer bases
greater than one; their p-adic interpretation requires a prime. Constructors,
signatures, and period queries require prime bases. Cross-base inspection of
a finite snapshot is unsupported. Lazy values can be inspected at another
prime because their sources remain available.

| Inspection | `PadicRational` | `PadicLazy` | `PadicRationalN` |
|------------|-----------------|-------------|------------------|
| `Normal` | Exact rational | Certified rational reconstructed from retained sources | Bounded candidate, residue fallback, or `Missing` for uncertain zero |
| `PadicOrder`, `PadicAbs` | Exact value | Computed from the recipe | Exact valuation for nonzero residue; interval bounds for uncertain zero |
| `PadicNormalize` | Remove valuation | Retain a recipe for the unit | Remove valuation, retain relative precision; zero unchanged |
| `PadicCanonicalize` | Rebuild canonical expansion | Identity | Normalize residue, preserve absolute precision |
| `PadicDigits` | Stored exact digits | Preview digits | Stored finite digits |
| `PadicSignature`, `PadicPeriodLength` | Supported | No direct form | No direct form |

For a lazy value `s`, use `PadicSignature[Normal[s],p]` or
`PadicPeriodLength[Normal[s],p]` when an exact period query is wanted. A finite
snapshot cannot determine an unknown tail's period. Unsupported argument
forms may remain unevaluated; they do not all emit an error message.

The current API has no dedicated precision accessor or finite-precision
congruence predicate. For `PadicRationalN[m,p,e,n]`, relative precision is `n`
and absolute precision is `e+n`. A lazy value has no fixed precision; inspect
an explicit snapshot instead. `SameQ` compares representation structure and
is not a mathematical equality or congruence test.

`PadicDigits` returns numeric data, including leading zeros required by stored
precision. A positive valuation appends zeros. A negative valuation does not
insert a point or fractional padding; use the object's `e` field to locate its
places. Zero gives `{0}`, including an uncertain zero, so the digit list alone
does not convey the zero's precision or exactness.

### Arithmetic

All three representation heads support addition, subtraction, multiplication,
division, and integer powers, including operations with exact integer/rational
scalars. Exact arithmetic returns canonical exact representations; operands
in different bases are combined as rationals and re-encoded in the smaller
base. Lazy arithmetic retains inactive recipes and evaluates modularly when
digits or reconstruction are requested. Finite arithmetic computes on modular
residues and propagates precision; mixing an exact or lazy value with a finite
snapshot is limited by that snapshot (with exact-zero identity exceptions).
Combining p-adic objects in different bases is rejected when either
is a finite snapshot. Inverting exact zero or an
uncertain zero returns `Indeterminate` with a message.

Exact negation (`Minus[x]` or `-x`) complements the stored digits directly
and trims redundant prefix digits or a zero repeating tail. For canonical
inputs it preserves canonical form without decoding through `Normal`.
Integer powers also avoid `Normal`: positive powers of terminating expansions
raise the significand directly, while periodic powers and inverses use reduced
integer numerator/denominator pairs and recompute the period. They do not
construct intermediate Wolfram rationals. Exact addition and multiplication
still use the rational roundtrip. Zero to a negative power emits
`Padic::zeropow`; zero to the zeroth power emits `Power::indet`. Both return
`Indeterminate`.

Approximate arithmetic can return an exact scalar in cases such as a zeroth
power or adding an exact scalar to exact zero. See the zero and precision
rules above before reconstructing an arithmetic result with `Normal`.

### Square roots: residue branches rather than real positivity

`Sqrt[s]` (equivalently `s^(1/2)`) works for exact `PadicRational`, retained
`PadicLazy`, and eager `PadicRationalN` values. For a nonzero value `p^e u`,
the valuation `e` must be even. At odd primes the unit must be a nonzero square
modulo `p`; at `p=2` it must be 1 modulo 8. A proved nonsquare returns
`Indeterminate` with `Padic::sqrt`, even when a real square root exists.

The selected branch is deterministic and compatible with increasing precision:
the unit root is 1 modulo 4 at base 2, or the smaller positive residue root
modulo an odd prime. This is not a real-positive convention. Negating the
result gives the other root. It follows that `Sqrt[s^2]` need not be `s`.

```mathematica
Normal[Sqrt[Padic[9,2]]]             (* -3: its unit is 1 modulo 4 *)
Normal[Sqrt[Padic[4,3]]]             (* -2: residue 1 modulo 3 *)
Sqrt[Padic[2,2]]                    (* Indeterminate; no root in Q_2 *)

r = Sqrt[Padic[-7,2]];              (* PadicLazy[Inactive[Power][-7,1/2],2] *)
PadicN[r,2,20]                      (* 20 known relative digits *)
Normal[r]                          (* Missing["NotRational"] *)
Normal[r^2]                        (* -7 *)
Normal[r-r]                        (* 0 *)

Sqrt[PadicN[-7,2,12]] // FullForm   (* PadicRationalN[181,2,0,11] *)
PadicN[Sqrt[PadicN[-7,2]],2,12]     (* lazy source supplies an extra input bit *)
```

For an exact input whose selected root is rational, the result remains an exact
periodic `PadicRational`. An irrational root cannot have a repeating rational
expansion, so its exact defining recipe is retained as `PadicLazy`. Arithmetic
and nested square roots retain recipes, while finite snapshots are evaluated
modularly. `Normal` certifies a rational result when one exists; genuinely
irrational expressions return `Missing["NotRational"]`. It does not substitute
a real/complex radical or an unrelated bounded rational candidate. For example,
the selected roots of 2 and 8 in base 7 satisfy `sqrt(8) = -2 sqrt(2)`, so real
principal-radical identities must not be applied by activating a root recipe.

For eager nonzero snapshots, odd-prime square roots retain the input relative
precision. Binary square roots lose one known relative bit: `n` input bits
give `n-1` output bits. Their output valuation is `e/2`. At least three binary
unit bits are needed to certify existence; fewer bits can sometimes prove
nonexistence but cannot certify a root. If the domain is undecided, including
an uncertain zero, the result is `Missing["InsufficientPrecision", ...]` with
`PadicN::sqrtprec`. Exact zero remains exact zero. A lazy request for `n` root
bits obtains at least `n+1` unit bits from its binary source rather than filling
unknown positions. An eager result cannot regain the discarded bit.

Ordinary rational recipes retain their existing bound propagation. Composed
algebraic root recipes use square-free annihilating polynomials and modular
valuation bounds to certify zero and rationality without choosing a real
embedding. Polynomial degrees and coefficient sizes can grow with the recipe;
these certificates can be more expensive than a finite modular root itself.
The new square-root paths are checked by Wolfram tests; they do not add a Lean
formalization of square roots or algebraic recipes.

---

## Requirements

- Mathematica 13.2 or later

---

## Author

Frank O. Kuehnel

## License

MIT
