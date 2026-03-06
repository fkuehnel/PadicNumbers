# PadicNumbers

**Exact p-adic arithmetic for rational numbers in Mathematica.**

A Wolfram paclet implementing exact p-adic representations of rationals, including
periodic expansions, lossy (floating-point-style) approximations, rational reconstruction,
and tree visualization.

---

## Installation

### From GitHub (recommended)

```mathematica
PacletInstall["https://github.com/fkuehnel/PadicNumbers/releases/latest/download/PadicNumbers-0.0.7.paclet"]
```

### From local source

Clone the repository and install directly:

```bash
git clone https://github.com/fkuehnel/PadicNumbers.git
```

```mathematica
PacletInstall["/path/to/PadicNumbers"]
```

### Load the package

```mathematica
Needs["PadicNumbers`"]
```

---

## Quick Start

```mathematica
(* Exact p-adic representation of a rational *)
Padic[1/3, 7]          (* 3-adic expansion of 1/3 — purely periodic *)
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

## Lossy (Approximate) Representation

```mathematica
(* Store as truncated p-adic expansion — drops periodicity *)
x = PadicN[1/3, 7, 8]      (* 8 digits of 7-adic precision *)

(* Reconstruct rational via RATCONVERT *)
Normal[x]                   (* -> 1/3 if precision is sufficient *)

(* Lossy arithmetic *)
PadicN[1/3, 7, 8] + PadicN[1/7, 7, 8]
```

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

---

## Symbols

| Symbol | Description |
|--------|-------------|
| `Padic[r, p]` | Exact p-adic representation of integer or rational `r` |
| `PadicN[r, p, N]` | Lossy p-adic representation with `N` digits of precision |
| `PadicRational[m,p,e,N,k]` | Internal exact format: significand, base, valuation, precision, period |
| `PadicRationalN[m,p,e,N]` | Internal lossy format: significand, base, valuation, precision |
| `PadicOrder[r, p]` | p-adic valuation of `r` |
| `PadicAbs[r, p]` | p-adic absolute value of `r` |
| `PadicNormalize[r, p]` | Remove p-adic valuation factor |
| `PadicSignature[r, p]` | `{N, k}` — total precision and period length |
| `PadicCanonicalize[s]` | Minimize significand by removing redundant periodic digits |
| `PadicDigits[s]` | List of base-p digits of a p-adic number |
| `PadicDigitTree[p, depth]` | Visualize the p-adic tree with optional ray highlighting |

---

## Requirements

- Mathematica 13.2 or later

---

## Author

Frank O. Kuehnel

## License

MIT
