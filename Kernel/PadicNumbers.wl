(* ::Package:: *)

(* Exact-arithmetic revision, 2026-10-23.
   Load in a fresh kernel with Get["Kernel/PadicNumbers.wl"].
   PadicRational[m,p,e,n,k] stores n digits, of which the highest k
   repeat to the left; n-k is the preperiod of the normalized unit.
   PadicN uses modular finite-precision arithmetic with explicit bounds.
   Reconstruction and zero handling are checked separately. See README.md.
   Mathematical formula proofs and their verification boundary: Proofs/README.md. *)


BeginPackage["FrankKuehnel`PadicNumbers`"]

PadicOrder::usage = "PadicOrder[r,p] gives the valuation of an exact integer or rational r in integer base p>1. PadicOrder[s] uses the base of an exact, lazy, or finite p-adic object; PadicOrder[s,p] also accepts an explicit base. Exact zero has order Infinity. A finite-precision zero known to O(p^a) has order Interval[{a,Infinity}]. Finite snapshots support only their stored base; lazy objects can be inspected at another prime base.";
PadicAbs::usage = "PadicAbs[r,p] gives p^(-PadicOrder[r,p]) for an exact integer or rational r in integer base p>1; the value at zero is 0. PadicAbs[s] uses the base of an exact, lazy, or finite-precision p-adic object. A zero known only to O(p^a) has absolute-value bound Interval[{0,p^(-a)}]. Finite snapshots support only their stored base; lazy objects can be inspected at another prime base.";
PadicNormalize::usage = "PadicNormalize[r,p] removes the valuation from an exact rational r, giving r p^(-PadicOrder[r,p]); zero stays zero. PadicNormalize[s] sets a nonzero p-adic object's valuation to zero while retaining its unit digits and relative precision. For PadicLazy it retains a recipe for the normalized value. It leaves exact and uncertain zero objects unchanged.";
PadicSignature::usage = "PadicSignature[r,p] gives {n,k} for the exact expansion of the normalized rational unit: n stored digits, k repeating digits, and n-k nonrepeating digits. Zero has signature {0,0}; terminating expansions have k=0. PadicSignature[s] uses a PadicRational object's base; PadicSignature[s,p] uses prime p. The period is determined without enumerating its digits. Lazy and finite objects have no direct signature form; use PadicSignature[Normal[s],p] for a lazy value.";
PadicCanonicalize::usage = "PadicCanonicalize[s] rebuilds an exact PadicRational in canonical form, minimizing its period and normalizing its valuation. For PadicRationalN it normalizes the stored residue without changing the absolute precision e+n or reconstructing an exact rational. Lazy objects retain their recipe.";

Padic::usage = "Padic[r,p] constructs the exact, eventually periodic p-adic expansion of an integer or rational r at prime p. Normal[Padic[r,p]] returns r. Padic[s,p] converts an exact object to base p; Padic[s] leaves it unchanged. Sqrt[s] selects a local residue branch: rational roots remain PadicRational, while irrational roots retain a refinable PadicLazy recipe. A PadicLazy input is certified with Normal before exact periodic conversion; an irrational value returns Missing[\"NotRational\"]. Conversion of PadicRationalN uses Normal's candidate and does not certify the unknown original rational. The constructor threads over lists; storing an entire period can be expensive.";
PadicLazy::usage = "PadicLazy[expr,p] stores exact rational leaves and inactive Plus, Times, Minus, integer Power, and square-root Power[expr,1/2] nodes in prime base p. Sqrt chooses the unit root 1 modulo 4 at p=2, or the smaller root modulo an odd prime. PadicN[s,p,n] requests n relative digits and obtains extra source precision when needed. Normal certifies a rational value; a genuinely irrational root expression returns Missing[\"NotRational\"]. Root recipes remain tied to their prime base. First[s] exposes the recipe for InputForm or TreeForm. Direct construction does not validate the recipe. Display previews digits without discarding sources.";
PadicN::usage = "PadicN[r,p] retains an exact integer or rational source in a public PadicLazy[expr,p] representation. Arithmetic and Sqrt build refinable recipes; Normal certifies rational results or returns Missing[\"NotRational\"] for irrational root expressions. PadicN[r,p,n] eagerly returns PadicRationalN with positive relative precision n. PadicN[r,p,Automatic] is eager and selects minimum symmetric reconstruction precision for a rational source. PadicN[lazy,p,n] requests a snapshot; Automatic uses sufficient candidate bounds, not necessarily minimum precision. Existing finite approximations remain finite and cannot regain discarded digits. Sqrt of a finite snapshot preserves relative precision for odd primes and loses one bit at p=2; insufficient domain information gives Missing[\"InsufficientPrecision\"]. Bases must be prime. The constructor threads over lists. Display previews preserve sources.";
PadicPeriodLength::usage = "PadicPeriodLength[r,p] gives the minimal eventual period of an exact rational in prime base p without constructing its digit cycle. Terminating expansions, including zero, have period 0; negative integers have period 1. PadicPeriodLength[s] uses a PadicRational object's base; PadicPeriodLength[s,p] uses p. Lazy and finite objects have no direct period form; use PadicPeriodLength[Normal[s],p] for a lazy value.";
PadicRational::usage = "PadicRational[m,p,e,n,k] stores an exact rational with valuation e and n normalized unit digits packed into the nonnegative integer m; the highest k digits repeat toward the left. For k=0 its value is m p^e. Normal[s] returns its exact rational value. Prefer Padic to construct valid canonical objects; direct construction does not validate the fields.";
PadicRationalN::usage = "PadicRationalN[m,p,e,n] represents m p^e + O(p^(e+n)); n is relative precision and e+n is absolute precision. A zero significand with e=Infinity denotes exact zero; finite e denotes an uncertain zero. Normal attempts bounded rational reconstruction and otherwise returns m p^e; an uncertain zero gives Missing[\"InsufficientPrecision\",e+n]. Sqrt requires even valuation and a square unit, selects a deterministic local branch, and returns n relative digits for odd p or n-1 for p=2. Uncertain zero or insufficient binary digits gives Missing[\"InsufficientPrecision\"]; a proved nonsquare gives Indeterminate with Padic::sqrt. Prefer PadicN for finite snapshots; direct construction does not validate fields.";
PadicDigits::usage = "PadicDigits[s] gives the stored integer digits of an exact or finite-precision object from highest to lowest place, before display-symbol conversion. Positive valuations append zero digits; negative valuations do not insert a radix point or padding. Zero gives {0}. PadicDigits[r,p] first constructs the exact expansion of rational r. For a finite approximation, an explicit p must match its stored base and preserves its known digits. Lazy objects return preview digits; use PadicN[s,p,n] to request a specific precision.";

PadicDigitTree::usage = "PadicDigitTree[p,depth] draws a p-branching digit tree for integer p>1 and positive depth. PadicDigitTree[p] chooses a depth automatically; explicit depth may be reduced to limit tree size. Prime p gives the p-adic interpretation. RayDigits highlights paths specified in lowest-place-first order. Object rays currently use normalized unit digits; finite snapshot rays use a reconstructed rational candidate, while lazy rays request the required digits directly. See README.md for options and limitations.";
RayDigits::usage = "RayDigits is an option for PadicDigitTree specifying None, one list of lowest-place-first digits, a list of paths, or exact, lazy, or finite p-adic objects to highlight.";
Layout::usage = "Layout is an option for PadicDigitTree: \"Hyperbolic\" (default), \"TopDown\", or \"Tree\".";
VertexLabelMode::usage = "VertexLabelMode is an option for PadicDigitTree: \"None\" (default), \"FirstLayer\", \"Ray\", or \"All\".";
EdgeLabelMode::usage = "EdgeLabelMode is an option for PadicDigitTree: \"Ray\" (default), \"None\", \"FirstLevel\", or \"All\".";
DigitColors::usage = "DigitColors is an option for PadicDigitTree specifying Automatic, an association from digit integers to colors, or a list containing at least p colors.";
SectorBackground::usage = "SectorBackground is an option for PadicDigitTree enabling shaded sectors in the hyperbolic layout; the default is False.";
SectorBackgroundDepth::usage = "SectorBackgroundDepth is an option for PadicDigitTree specifying the number of sector levels to shade; the default is 1.";
SectorOpacity::usage = "SectorOpacity is an option for PadicDigitTree specifying the base sector opacity, reduced at deeper levels; the default is 0.07.";
CantorBoundary::usage = "CantorBoundary is an option for PadicDigitTree enabling a digit-boundary overlay in the hyperbolic layout; the default is False.";
CantorDustRadius::usage = "CantorDustRadius is an option for PadicDigitTree specifying the radius of the boundary overlay; the default is 1.12.";
CantorPointSize::usage = "CantorPointSize is an option for PadicDigitTree specifying the boundary dot size; the default is 2.";

Begin["`Private`"]

(******************* P-adic Order and Value ******************)

PadicOrder[0,p_Integer/;p>1] := Infinity
PadicOrder[n_Integer,p_Integer/;p>1] := IntegerExponent[n,p]
PadicOrder[r_Rational,p_Integer/;p>1] :=
    IntegerExponent[Numerator[r],p]-IntegerExponent[Denominator[r],p]
PadicAbs[0,p_Integer/;p>1] := 0
PadicAbs[n_Integer|n_Rational,p_Integer/;p>1] := p^(-PadicOrder[n,p])
PadicNormalize[n_Integer|n_Rational,p_Integer/;p>1] := n*PadicAbs[n,p]

(* PadicRational upvalues \[LongDash] no p needed as second argument *)

PadicRational /: PadicOrder[PadicRational[0,p_,___]] := Infinity
PadicRational /: PadicOrder[PadicRational[0,p_,___], p_] := Infinity
PadicRational /: PadicOrder[PadicRational[_,p_,e_,___]] := e
PadicRational /: PadicOrder[PadicRational[_,p_,e_,___], p_] := e
PadicRational /: PadicAbs[PadicRational[0,p_,___]] := 0
PadicRational /: PadicAbs[PadicRational[0,p_,___], p_] := 0
PadicRational /: PadicAbs[PadicRational[_,p_,e_,___]] := p^(-e)
PadicRational /: PadicAbs[PadicRational[_,p_,e_,___], p_] := p^(-e)
PadicRational /: PadicNormalize[PadicRational[m_,p_,e_,n_,k_]] :=
    PadicRational[m,p,0,n,k]

(* cross-base PadicOrder and PadicAbs *)
PadicRational /: PadicOrder[s:PadicRational[_,p1_,e_,___],
    p2_Integer/;p2>1] := PadicOrder[s//Normal,p2] /; p1 != p2
PadicRational /: PadicAbs[s:PadicRational[_,p1_,e_,___],
    p2_Integer/;p2>1] := PadicAbs[s//Normal,p2] /; p1 != p2

(* PadicRationalN upvalues -- lossy representation *)

PadicRationalN /: PadicOrder[PadicRationalN[0,p_,e_,n_]] :=
    If[e === Infinity, Infinity, Interval[{e+n, Infinity}]]
PadicRationalN /: PadicOrder[PadicRationalN[_,_,e_,_]] := e
PadicRationalN /: PadicOrder[s:PadicRationalN[_,p_,_,_], p_] := PadicOrder[s]
PadicRationalN /: PadicAbs[PadicRationalN[0,p_,e_,n_]] :=
    If[e === Infinity, 0, Interval[{0, p^(-e-n)}]]
PadicRationalN /: PadicAbs[PadicRationalN[_,p_,e_,_]] := p^(-e)
PadicRationalN /: PadicAbs[s:PadicRationalN[_,p_,_,_], p_] := PadicAbs[s]
PadicRationalN /: PadicNormalize[s:PadicRationalN[0,___]] := s
PadicRationalN /: PadicNormalize[PadicRationalN[m_,p_,e_,n_]] :=
    PadicRationalN[m,p,0,n]

(* Normalize the unit without changing the known absolute precision. *)
PadicRationalN /: PadicCanonicalize[s_PadicRationalN] := padicNCanonical[s]

(**************** Exact signatures and construction ****************)

Padic::prime = "The base `1` must be a prime integer.";
Padic::base = "Cannot combine bases `1` and `2`. Convert one operand explicitly with Padic[operand, targetBase].";
Padic::zeropow = "Zero has no multiplicative inverse (exponent `1`).";
Padic::sqrt = "The value has no square root in Q_`1`.";

(* Helpers receive a valid prime p and a reduced, normalized unit a/b.
   MultiplicativeOrder avoids walking and retaining the full cycle.
   For b=1: positive integers terminate; negative integers end in p-1. *)
padicPeriod[a_Integer, b_Integer, p_Integer] :=
    If[b == 1, If[a < 0, 1, 0], MultiplicativeOrder[p, b]];

padicUnitSignature[a_Integer, b_Integer, p_Integer] :=
    Module[{t = a, j = 0, d, inv, k},
        If[b == 1 && a > 0, Return[{IntegerLength[a, p], 0}]];
        k = padicPeriod[a, b, p];
        inv = If[b == 1, 1, PowerMod[b, -1, p]];
        (* A tail t/b is purely periodic precisely when -1 <= t/b < 0.
           Walk only the initial digits until entering that interval.
           The cycle itself is never enumerated. All arithmetic is exact. *)
        (* Lean: PadicExact.loop_terminates and modular_decode_roundtrip. *)
        While[t > 0 || t < -b,
            d = Mod[t inv, p];
            t = Quotient[t - b d, p];
            j++
        ];
        {j + k, k}
    ];

PadicPeriodLength[r : (_Integer | _Rational), p_Integer] :=
    Module[{u},
        If[!PrimeQ[p], Message[Padic::prime, p]; Return[$Failed]];
        If[r == 0, Return[0]];
        u = PadicNormalize[r, p];
        padicPeriod[Numerator[u], Denominator[u], p]
    ];
PadicPeriodLength[s_PadicRational] :=
    PadicPeriodLength[Normal[s], s[[2]]];
PadicPeriodLength[s_PadicRational, p_Integer] :=
    PadicPeriodLength[Normal[s], p];

PadicSignature[r : (_Integer | _Rational), p_Integer] :=
    Module[{u},
        If[!PrimeQ[p], Message[Padic::prime, p]; Return[$Failed]];
        If[r == 0, Return[{0, 0}]];
        u = PadicNormalize[r, p];
        padicUnitSignature[Numerator[u], Denominator[u], p]
    ];
PadicSignature[s_PadicRational] := PadicSignature[Normal[s], s[[2]]];
PadicSignature[s_PadicRational, p_Integer] := PadicSignature[Normal[s], p];

Padic[r : (_Integer | _Rational), p_Integer] :=
    Module[{e, u, a, b, n, k, modulus, m},
        If[!PrimeQ[p], Message[Padic::prime, p]; Return[$Failed]];
        If[r == 0, Return[PadicRational[0, p, 0, 0, 0]]];
        e = PadicOrder[r, p];
        u = r p^(-e);
        a = Numerator[u]; b = Denominator[u];
        {n, k} = padicUnitSignature[a, b, p];
        If[k == 0,
            m = a,
            modulus = p^n;
            m = Mod[a PowerMod[b, -1, modulus], modulus]
        ];
        PadicRational[m, p, e, n, k]
    ];

Padic[s_PadicRational] := s;
Padic[s_PadicRational, p_Integer] :=
    If[s[[2]] === p, s, Padic[Normal[s], p]];
SetAttributes[Padic, Listable];

(* Rational reconstruction of a lossy value yields a candidate, not a
   certified recovery of the original rational. This API is retained. *)
Padic[s_PadicRationalN] :=
    With[{r = Normal[s]}, If[MissingQ[r], r, Padic[r, s[[2]]]]];
Padic[s_PadicRationalN, p_Integer] :=
    With[{r = Normal[s]}, If[MissingQ[r], r, Padic[r, p]]];
Padic[e_, ___] := e /; AtomQ[e] && !MatchQ[e, _Integer | _Rational];

(*********** Conversion to Integers and Rationals ************)

(* Lean: PadicExact.decode_finite and modular_decode_roundtrip. *)
PadicRational /: Normal[PadicRational[m_,p_, e_,_,0]] := m p^e
PadicRational /: Normal[PadicRational[m_,p_,e_,n_,k_]] :=
    (p^e QuotientRemainder[m,p^#] . {-p^#/(p^k-1),1})&[n-k]

(******************* Conversion to digits ********************)

PadicDigits[s:(_Integer|_Rational|_PadicRational),p_Integer] :=
    With[{a=Padic[s,p]}, If[a === $Failed,$Failed,PadicDigits[a]]]
PadicDigits[s:PadicRationalN[_,p_,_,_],p_Integer] := PadicDigits[s]
PadicDigits[PadicRationalN[_,p1_,_,_],p2_Integer] :=
    (Message[PadicN::base,p1,p2]; $Failed) /; p1 =!= p2
PadicDigits[PadicRational[0,___]] := {0}
PadicDigits[PadicRational[m_,p_,e_Integer/;e<=0,n_Integer,___]] :=
    IntegerDigits@@{m,p,n}
PadicDigits[s:PadicRational[_,_,e_Integer/;e>0,___]] :=
    Join[PadicDigits[ReplacePart[s,3->0]],ConstantArray[0,Abs[e]]]

(* PadicDigits for lossy PadicRationalN \[LongDash] treat as non-periodic *)
PadicDigits[PadicRationalN[0,___]] := {0}
PadicDigits[PadicRationalN[m_,p_,e_Integer/;e<=0,n_Integer]] :=
    IntegerDigits@@{m,p,n}
PadicDigits[s:PadicRationalN[_,_,e_Integer/;e>0,_]] :=
    Join[PadicDigits[ReplacePart[s,3->0]], ConstantArray[0,Abs[e]]]

(********************** P-adic formatting ********************)

(* Keep digits numeric until after splitting periods and placing the radix
   point. Bases through 36 use A=10,...,Z=35; larger bases use decimal
   digit values with bars, including at the boundary of a repeating block. *)
padicDigitSymbol[d_Integer, p_] :=
    If[p <= 36 && d >= 10, FromCharacterCode[55+d], d];
padicDigitSymbol[d_, _] := d;
padicDigitSeparator[p_] := If[p <= 36, " ", "|"];
padicDigitRow[digits_List, p_] :=
    Row[padicDigitSymbol[#,p]& /@ digits, padicDigitSeparator[p]];
padicFractionalRow[digits_List, p_, e_] :=
    If[p <= 36, padicDigitRow[Insert[digits,".",e-1],p],
        With[{parts = TakeDrop[digits,Length[digits]+e]},
            Row[{padicDigitRow[parts[[1]],p], ".", padicDigitRow[parts[[2]],p]}]]];

(*positive scaled non-periodic expansions*)
PadicRational /: Format[s:PadicRational[_,p_,e_/;0<=e<=4,_,0]] :=
    Subscript[padicDigitRow[PadicDigits[s],p],p]
PadicRational /: Format[s:PadicRational[_,p_,e_/;-4<=e<0,n_,0]] :=
    Subscript[padicFractionalRow[Join[ConstantArray[0,Max[0,-(n+e)]],PadicDigits[s]],p,e],p]

padicPeriodicColor= RGBColor[0.7,0.5,0.3];
(* purely periodic *)
PadicRational /: Format[s:PadicRational[_,p_,0,k_,k_/;k>0]]:=
    Subscript[Style[OverBar[padicDigitRow[#,p]],padicPeriodicColor],p]&[Take[PadicDigits[s],k]]
(* eventually periodic *)
PadicRational /: Format[s:PadicRational[_,p_,0,n_,k_/;k>0]]:=
    Subscript[Row[{Style[OverBar[padicDigitRow[#1,p]],padicPeriodicColor],
        padicDigitRow[#2,p]},padicDigitSeparator[p]],p]&@@TakeDrop[PadicDigits[s],k]/;n>k
(* simply add a scale factor here *)
PadicRational /: Format[s:PadicRational[_,p_,e_Integer/;e!=0,_,_]]:=
    Row[{Format[ReplacePart[s,3->0]],Superscript[p,e]},"\[Times]"]

(* PadicRationalN formatting: shown with ~ to indicate lossy *)
PadicRationalN /: Format[PadicRationalN[0,p_,Infinity,_]] := Subscript[0,p]
PadicRationalN /: Format[PadicRationalN[0,p_,e_Integer,n_Integer]] :=
    Row[{"O(", Superscript[p,e+n], ")"}]
PadicRationalN /: Format[s:PadicRationalN[_,p_,e_/;-4<=e<0,n_]]:=
    Subscript[Row[{"~",padicFractionalRow[Join[ConstantArray[0,Max[0,-(n+e)]],PadicDigits[s]],p,e]}],p]
PadicRationalN /: Format[s:PadicRationalN[_,p_,e_/;0<=e<=4,_]]:=
    Subscript[Row[{"~",padicDigitRow[PadicDigits[s],p]}],p]
PadicRationalN /: Format[s:PadicRationalN[_,p_,e_Integer/;e!=0,_]]:=
    Row[{Format[ReplacePart[s,3->0]],Superscript[p,e]},"\[Times]"]

(******************** P-adic arithmetic **********************)

(* Rebuild from the exact value. This also reduces repeated period
   blocks and fixes valuation, zero, and cycle-rotation edge cases. *)
PadicCanonicalize[s_PadicRational] := Padic[Normal[s], s[[2]]];

(* Keep the exact rational roundtrip, now with number-theoretic period
   construction. It handles carries, valuation changes, denominator
   cancellation, and periods that grow after multiplication. Exact operands
   may have different bases; re-encode their rational result in the smaller.
   Lean: PadicExact.value_add, value_mul, value_power, inverse_correct. *)
padicBinary[op_, a_PadicRational, b_PadicRational] :=
    Padic[op[Normal[a], Normal[b]], Min[a[[2]], b[[2]]]];

PadicRational /: Plus[a_PadicRational, b_PadicRational] :=
    padicBinary[Plus, a, b];
PadicRational /: Times[a_PadicRational, b_PadicRational] :=
    padicBinary[Times, a, b];

(* Negate normalized digits directly: the unit digit becomes p-d, and
   all higher digits become p-1-d. Canonical inputs already have a minimal
   period; only a zero tail or a redundant prefix needs removing. *)
padicTrimNegatedDigits[m_,p_,e_,n_,k_] /; m < p^(n-k) :=
    PadicRational[m,p,e,IntegerLength[m,p],0];
padicTrimNegatedDigits[m_,p_,e_,n_,k_] := Module[{r=m,length=n},
    While[length > k &&
        Mod[Quotient[r,p^(length-k-1)],p] == Quotient[r,p^(length-1)],
        r = Mod[r,p^(length-1)]; length--
    ];
    PadicRational[r,p,e,length,k]
];

PadicRational /: Minus[PadicRational[0,p_,___]] := PadicRational[0,p,0,0,0];
(* Terminating digits acquire a repeating p-1 tail. *)
PadicRational /: Minus[PadicRational[m_,p_,e_,n_,0]] :=
    padicTrimNegatedDigits[p^(n+1)-m,p,e,n+1,1];
(* A nonempty prefix absorbs the exceptional unit-digit complement. *)
PadicRational /: Minus[PadicRational[m_,p_,e_,n_,k_]] /; n > k > 0 :=
    padicTrimNegatedDigits[p^n-m,p,e,n,k];
(* A pure cycle needs one extra digit before complementing. *)
PadicRational /: Minus[PadicRational[m_,p_,e_,k_,k_]] /; k > 0 :=
    padicTrimNegatedDigits[p^(k+1)-m-Mod[m,p] p^k,p,e,k+1,k];
(* Unary -x is represented internally as Times[-1,x]. *)
PadicRational /: Times[-1,a_PadicRational] := Minus[a];

PadicRational /: Plus[a_PadicRational, b : (_Integer | _Rational)] :=
    Padic[Normal[a] + b, a[[2]]];
PadicRational /: Times[a_PadicRational, b : (_Integer | _Rational)] :=
    Padic[Normal[a] b, a[[2]]];

(* Power a reduced unit numerator/denominator using integers only. Negative
   exponents swap the pair and reverse the valuation. Recompute the signature:
   a power can have a longer period than its input. *)
padicPowerUnit[a_,b_,p_,e_,exponent_Integer?Negative] :=
    padicPowerUnit[Sign[a] b,Abs[a],p,-e,-exponent];
padicPowerUnit[a_,b_,p_,e_,exponent_Integer?Positive] :=
    Module[{numerator=a^exponent,denominator=b^exponent,n,k},
        {n,k} = padicUnitSignature[numerator,denominator,p];
        PadicRational[Mod[numerator PowerMod[denominator,-1,p^n],p^n],
            p,e exponent,n,k]
    ];

(* Integer powers also handle Times[a,a], which can evaluate to Power[a,2]. *)
PadicRational /: Power[PadicRational[0,___], exponent_Integer?Negative] :=
    (Message[Padic::zeropow,exponent]; Indeterminate);
PadicRational /: Power[PadicRational[0,___], 0] :=
    (Message[Power::indet,HoldForm[0^0]]; Indeterminate);
PadicRational /: Power[PadicRational[0,p_,___], exponent_Integer?Positive] :=
    PadicRational[0,p,0,0,0];
PadicRational /: Power[PadicRational[_,p_,___], 0] := PadicRational[1,p,0,1,0];
PadicRational /: Power[a_PadicRational, 1] := a;

(* Positive powers of terminating units remain terminating. *)
PadicRational /: Power[PadicRational[m_,p_,e_,_,0], exponent_Integer?Positive] :=
    With[{v=m^exponent}, PadicRational[v,p,e exponent,IntegerLength[v,p],0]];
PadicRational /: Power[PadicRational[m_,p_,e_,_,0], exponent_Integer?Negative] :=
    padicPowerUnit[1,m,p,-e,-exponent];

(* For prefix L and repeating block B, the unit is
   (L (p^k-1) - B p^(n-k))/(p^k-1). Reduce the integer pair before powering;
   no Normal call or intermediate Wolfram Rational is needed. *)
PadicRational /: Power[PadicRational[m_,p_,e_,n_,k_], exponent_Integer] /; k > 0 :=
    Module[{scale=p^(n-k),denominator=p^k-1,block,prefix,numerator,g},
        {block,prefix} = QuotientRemainder[m,scale];
        numerator = prefix denominator - block scale;
        g = GCD[numerator,denominator];
        padicPowerUnit[Quotient[numerator,g],Quotient[denominator,g],p,e,exponent]
    ];

(* Sqrt is internally Power[...,1/2]. A rational root remains periodic;
   an irrational p-adic root retains its defining recipe instead. *)
PadicRational /: Power[s_PadicRational,1/2] := padicExactSqrt[Normal[s],s[[2]]];

(****************** P-adic lossy precision *******************)

(* converting to an approximate representation *)
PadicN::prime = "The base `1` must be a prime integer.";
PadicN::prec = "Relative precision `1` must be a positive integer.";
PadicN::base = "Cannot combine finite-precision p-adics with bases `1` and `2`.";
PadicN::zeropow = "Exact zero cannot be raised to exponent `1`.";
PadicN::precision = "A value known only to O(p^`1`) may be zero; this operation requires a nonzero value.";
PadicN::sqrtprec = "The stored digits do not determine a square-root branch in base `1`; more source precision is required.";

padicNParametersQ[p_, Automatic] := padicNParametersQ[p,1];
padicNParametersQ[p_, n_] := Which[
    !PrimeQ[p], Message[PadicN::prime,p]; False,
    !IntegerQ[n] || n <= 0, Message[PadicN::prec,n]; False,
    True, True];

(* The argument u has valuation zero, so its denominator is invertible. *)
padicNUnitResidue[u_, p_, n_] :=
    Mod[Numerator[u] PowerMod[Denominator[u],-1,p^n],p^n];

(* The least n with p^n > 2 H^2 places both normalized numerator and
   denominator strictly inside the symmetric reconstruction bound.
   IntegerLength computes this exactly, including powers on the boundary. *)
padicNReconstructionPrecision[u_, p_] :=
    IntegerLength[2 Max[Abs[Numerator[u]],Denominator[u]]^2,p];

PadicN[r:(_Integer|_Rational), p_] /; !padicNParametersQ[p,1] := $Failed;
PadicN[r:(_Integer|_Rational), p_?PrimeQ] := PadicLazy[r,p];
(* Successful rules require valid arguments, so more specific zero and
   Automatic patterns cannot bypass this shared diagnostic guard. *)
PadicN[r:(_Integer|_Rational|_PadicRationalN), p_, n_] /;
    !padicNParametersQ[p,n] := $Failed;

PadicN[0, p_?PrimeQ, Automatic] := PadicRationalN[0,p,Infinity,1];
PadicN[0, p_?PrimeQ, n_Integer?Positive] := PadicRationalN[0,p,Infinity,n];
PadicN[r:(_Integer|_Rational), p_?PrimeQ, Automatic] := Module[{e,u,n},
    e = PadicOrder[r,p];
    u = r p^(-e);
    n = padicNReconstructionPrecision[u,p];
    PadicRationalN[padicNUnitResidue[u,p,n],p,e,n]
];
PadicN[r:(_Integer|_Rational), p_?PrimeQ, n_Integer?Positive] := Module[{e,u},
    e = PadicOrder[r,p];
    u = r p^(-e);
    PadicRationalN[padicNUnitResidue[u,p,n],p,e,n]
];
PadicRational /: PadicN[s_PadicRational] := PadicN[Normal[s],s[[2]]];
PadicN[s_PadicRational, p_] := PadicN[Normal[s],p];
PadicN[s_PadicRational, p_, n_] := PadicN[Normal[s],p,n];
PadicN[s_PadicRationalN] := padicNCanonical[s];
PadicN[s:PadicRationalN[_,p_,_,_], p_] := padicNCanonical[s];
PadicN[s_PadicRationalN, p_] := (Message[PadicN::base,s[[2]],p]; $Failed);
PadicN[s:PadicRationalN[_,p_,_,_], p_?PrimeQ, Automatic] := padicNCanonical[s];
PadicN[s:PadicRationalN[_,p_,_,_], p_?PrimeQ, n_Integer?Positive] :=
    padicNTruncate[padicNCanonical[s],n];
PadicN[s_PadicRationalN, p_?PrimeQ, n:(Automatic|_Integer?Positive)] :=
    (Message[PadicN::base,s[[2]],p]; $Failed);

padicNTruncate[s:PadicRationalN[0,___], _] := s;
padicNTruncate[PadicRationalN[m_,p_,e_,n_], requested_] :=
    padicNFromResidue[m,p,e,Min[n,requested]];

(* Rational reconstruction via RATCONVERT. Cancelling a common factor of
   the Euclidean pair can destroy congruence modulo pN, so validate the
   pair before division. Both bounds are strict. Callers supply integers
   pN > 1 and 0 <= m < pN. Retain the residue on failed validation.
   Lean model and proof: Proofs/PadicReconstruction.lean. *)
PadicRationalApprox[m_, pN_] := Module[{a=pN, b=m, s=0, t=1, q},
    While[2 b^2 >= pN,
        q = Quotient[a,b];
        {a,b} = {b,a-q b};
        {s,t} = {t,s-q t}];
    If[t != 0 && 2 b^2 < pN && 2 t^2 < pN &&
        CoprimeQ[b,t] && CoprimeQ[t,pN] && Mod[b-m t,pN] == 0,
        b/t, m]
]

(* converting back to Integer or Rational *)
PadicRationalN /: Normal[PadicRationalN[0,p_,Infinity,n_]] = 0
PadicRationalN /: Normal[PadicRationalN[0,p_,e_,n_]] := Missing["InsufficientPrecision", e+n]
PadicRationalN /: Normal[PadicRationalN[m_,p_,e_,n_]] :=
    PadicRationalApprox[m, p^n] p^e

PadicN[e_Plus,p_Integer,prec_Integer] := PadicN[#,p,prec]&/@e
PadicN[e_Times,p_Integer,prec_Integer] := PadicN[#,p,prec]&/@e
PadicN[x_^n_,p_Integer,prec_Integer] := PadicN[x,p,prec]^n

SetAttributes[PadicN,Listable]
PadicN[e_,__]:=e/;AtomQ[e]

(**************** P-adic N lossy arithmetic ******************)

(* All arithmetic uses residues and bounds, never rational reconstruction. *)
padicNFromResidue[m_, p_, e_, n_] /; n <= 0 || Mod[m,p^n] == 0 :=
  PadicRationalN[0,p,e+n,0];
padicNFromResidue[m_, p_, e_, n_] := Module[{r=Mod[m,p^n],k},
    k = PadicOrder[r, p];
    PadicRationalN[r/p^k,p,e+k,n-k]
  ];
padicNCanonical[s:PadicRationalN[0,_,Infinity,_]] := s;
padicNCanonical[PadicRationalN[m_Integer,p_Integer,e_Integer,n_Integer]] :=
    padicNFromResidue[m,p,e,n];
padicNSameBaseQ[a_,b_] /; a[[2]] === b[[2]] := True;
padicNSameBaseQ[a_,b_] := (Message[PadicN::base,a[[2]],b[[2]]]; False);

(* General rejection rules. More specific shortcuts below require matching
   bases explicitly, so they cannot bypass validation. *)
padicNAdd[x_,y_] /; !padicNSameBaseQ[x,y] := $Failed;
padicNMul[x_,y_] /; !padicNSameBaseQ[x,y] := $Failed;
padicNMixed[op_,a_,b_] /; !padicNSameBaseQ[a,b] := $Failed;

(* Exact zero: retain the other summand, or the exact-zero factor.
   The finite-valuation patterns avoid overlapping two-exact-zero cases. *)
padicNAdd[PadicRationalN[0,p_,Infinity,_], y:PadicRationalN[_,p_,_,_]] :=
    padicNCanonical[y];
padicNAdd[x:PadicRationalN[_,p_,_Integer,_], PadicRationalN[0,p_,Infinity,_]] :=
    padicNCanonical[x];
padicNMul[x:PadicRationalN[0,p_,Infinity,_], PadicRationalN[_,p_,_,_]] := x;
padicNMul[PadicRationalN[_,p_,_Integer,_], y:PadicRationalN[0,p_,Infinity,_]] := y;

padicNAdd[x_,y_] := Module[{a,b,p,e,absolute,ma,mb},
    a = padicNCanonical[x]; b = padicNCanonical[y]; p = a[[2]];
    absolute = Min[a[[3]]+a[[4]],b[[3]]+b[[4]]];
    e = Min[a[[3]],b[[3]]];
    If[absolute <= e, Return[PadicRationalN[0,p,absolute,0]]];
    (* Skip terms beyond the common precision before computing any shift. *)
    ma = If[a[[3]] >= absolute,0,a[[1]] p^(a[[3]]-e)];
    mb = If[b[[3]] >= absolute,0,b[[1]] p^(b[[3]]-e)];
    padicNFromResidue[ma+mb,p,e,absolute-e]
];
padicNMul[x_,y_] := Module[{a,b,p},
    a = padicNCanonical[x]; b = padicNCanonical[y]; p = a[[2]];
    padicNFromResidue[a[[1]] b[[1]],p,a[[3]]+b[[3]],Min[a[[4]],b[[4]]]]
];

(* Scalars are exact: preserve the input's absolute precision under addition
   and relative precision under multiplication, including p-power factors. *)
padicNAddScalar[PadicRationalN[0,_,Infinity,_], r_] := r;
padicNMulScalar[a:PadicRationalN[0,_,Infinity,_], _] := a;

padicNAddScalar[x_,r_] := Module[{a,p,absolute,v,e,m},
    a = padicNCanonical[x]; p = a[[2]];
    If[r == 0, Return[a]];
    absolute = a[[3]]+a[[4]]; v = PadicOrder[r,p];
    If[v >= absolute, Return[a]];
    e = Min[a[[3]],v];
    m = a[[1]] p^(a[[3]]-e) +
        padicNUnitResidue[r p^(-v),p,absolute-v] p^(v-e);
    padicNFromResidue[m,p,e,absolute-e]
];
padicNMulScalar[x_,r_] := Module[{a,p,v},
    a = padicNCanonical[x]; p = a[[2]];
    If[r == 0, Return[PadicRationalN[0,p,Infinity,0]]];
    v = PadicOrder[r,p];
    If[a[[1]] == 0, Return[PadicRationalN[0,p,a[[3]]+v,0]]];
    padicNFromResidue[a[[1]] padicNUnitResidue[r p^(-v),p,a[[4]]],
        p,a[[3]]+v,a[[4]]]
];
padicNMixed[op_,a_,b_] := op[a,Normal[b]];

padicNPower[a:PadicRationalN[0,_,Infinity,_], exponent_Integer?Positive] := a;
padicNPower[PadicRationalN[0,_,Infinity,_], exponent_Integer] /; exponent <= 0 :=
    (Message[PadicN::zeropow,exponent]; Indeterminate);

padicNPower[x_,exponent_] := Module[{a,p,n,k,m},
    a = padicNCanonical[x]; p = a[[2]];
    If[exponent == 0, Return[1]];
    If[a[[1]] == 0,
        If[exponent < 0, Message[PadicN::precision,a[[3]]]; Return[Indeterminate]];
        Return[PadicRationalN[0,p,a[[3]] exponent,0]]];
    k = Abs[exponent];
    n = a[[4]] + PadicOrder[k,p];
    (* Even powers of odd 2-adic units are constant modulo an extra factor 2. *)
    If[p == 2 && a[[4]] == 1 && EvenQ[k], n++];
    m = PowerMod[a[[1]],exponent,p^n];
    PadicRationalN[m,p,a[[3]] exponent,n]
];

PadicRationalN /: Plus[a_PadicRationalN,b_PadicRationalN] := padicNAdd[a,b];
PadicRationalN /: Times[a_PadicRationalN,b_PadicRationalN] := padicNMul[a,b];
PadicRationalN /: Plus[a_PadicRationalN,r:(_Integer|_Rational)] := padicNAddScalar[a,r];
PadicRationalN /: Times[a_PadicRationalN,r:(_Integer|_Rational)] := padicNMulScalar[a,r];
PadicRationalN /: Plus[a_PadicRationalN,b_PadicRational] := padicNMixed[padicNAddScalar,a,b];
PadicRationalN /: Times[a_PadicRationalN,b_PadicRational] := padicNMixed[padicNMulScalar,a,b];
PadicRationalN /: Minus[a_PadicRationalN] := padicNMulScalar[a,-1];
PadicRationalN /: Power[a_PadicRationalN,exponent_Integer] := padicNPower[a,exponent];
PadicRationalN /: Power[a_PadicRationalN,1/2] := padicNSqrt[padicNCanonical[a]];

(****************** Square roots and stable branches ******************)

padicSqrtFailure[p_] := (Message[Padic::sqrt,p]; Indeterminate);
padicSqrtInsufficient[p_,n_] := (Message[PadicN::sqrtprec,p];
    Missing["InsufficientPrecision",<|"Base"->p,"KnownRelativePrecision"->n|>]);

(* Odd primes: select the smaller root modulo p, then lift that same branch.
   Binary units: select the root 1 modulo 4. Input n bits certify n-1 root
   bits, and each exact /2^k below selects the next known binary digit. *)
padicSqrtUnit[m_,2,n_] := Module[{y=1},
    Do[y += Mod[Quotient[m-y^2,2^k],2] 2^(k-1),{k,3,n-1}];
    y
];
padicSqrtUnit[m_,p_,n_] := Module[{roots=PowerModList[m,1/2,p],y,k=1,modulus},
    If[roots === {}, Return[padicSqrtFailure[p]]];
    y = Min[roots];
    While[k < n,
        k = Min[2 k,n]; modulus = p^k;
        y = Mod[y-(y^2-m) PowerMod[2 y,-1,modulus],modulus]
    ];
    y
];

padicNSqrt[s:PadicRationalN[0,_,Infinity,_]] := s;
padicNSqrt[PadicRationalN[0,p_,_,n_]] := padicSqrtInsufficient[p,n];
padicNSqrt[PadicRationalN[_,p_,e_Integer?OddQ,_]] := padicSqrtFailure[p];
padicNSqrt[PadicRationalN[m_,2,_,n_]] /; Mod[m,2^Min[n,3]] =!= 1 :=
    padicSqrtFailure[2];
padicNSqrt[PadicRationalN[_,2,_,n_]] /; n < 3 := padicSqrtInsufficient[2,n];
padicNSqrt[PadicRationalN[m_,p_,e_,n_]] := With[{y=padicSqrtUnit[m,p,n]},
    If[y === Indeterminate,y,PadicRationalN[y,p,e/2,n-If[p==2,1,0]]]];

padicExactSqrt[0,p_] := Padic[0,p];
padicExactSqrt[r_,p_] := Module[{e=PadicOrder[r,p],sample,root,unit,branch,modulus},
    If[OddQ[e], Return[padicSqrtFailure[p]]];
    sample = padicNSqrt[PadicN[r,p,If[p==2,3,1]]];
    If[sample === Indeterminate, Return[sample]];
    root = Sqrt[r];
    If[!MatchQ[root,_Integer|_Rational],
        Return[PadicLazy[Inactive[Power][r,1/2],p]]];
    unit = root p^(-e/2); modulus = If[p==2,4,p];
    branch = If[padicNUnitResidue[unit,p,If[p==2,2,1]] == Mod[sample[[1]],modulus],1,-1];
    Padic[branch root,p]
];

(**************** Lazy sources and late precision ****************)

(* Recipes are immutable and contain exact rational sources, never inferred
   sources reconstructed from finite snapshots. Arithmetic only builds recipes. *)
PadicLazy /: Plus[PadicLazy[a_,p_],PadicLazy[b_,q_]] := padicLazyBinary[Plus,a,p,b,q];
PadicLazy /: Times[PadicLazy[a_,p_],PadicLazy[b_,q_]] := padicLazyBinary[Times,a,p,b,q];
PadicLazy /: Plus[PadicLazy[a_,p_],r:(_Integer|_Rational)] :=
    PadicLazy[Inactive[Plus][a,r],p];
PadicLazy /: Times[PadicLazy[a_,p_],r:(_Integer|_Rational)] :=
    PadicLazy[Inactive[Times][a,r],p];
PadicLazy /: Minus[PadicLazy[a_,p_]] := PadicLazy[Inactive[Minus][a],p];
PadicLazy /: Times[-1,a_PadicLazy] := Minus[a];
PadicLazy /: Power[PadicLazy[a_,p_],k_Integer] := PadicLazy[Inactive[Power][a,k],p];
PadicLazy /: Power[PadicLazy[a_,p_],1/2] := padicLazySqrt[a,p];
PadicLazy /: Plus[a_PadicLazy,b_PadicRational] := a + PadicN[b];
PadicLazy /: Times[a_PadicLazy,b_PadicRational] := a PadicN[b];

(* Memoize metadata only within one request. No global cache or source mutation. *)
SetAttributes[padicLazyCompute,HoldAll];
padicLazyCompute[expr_] := Catch[Block[{padicLazyInfo,padicLazyPolynomial},
    padicLazyInfo[t_,p_] := padicLazyInfo[t,p] = padicLazyInfo0[t,p];
    padicLazyPolynomial[t_] := padicLazyPolynomial[t] = padicLazyPolynomial0[t];
    expr],padicLazyFailure];

(* Metadata {e,A,B}: exact valuation and bounds for the reduced rational unit.
   For root recipes the polynomial certificate bounds any rational candidate;
   Normal additionally certifies that the candidate is the selected branch. *)
padicLazyInfo0[0,_] := {Infinity,0,1};
padicLazyInfo0[r:(_Integer|_Rational),p_] := With[{e=PadicOrder[r,p]},
    With[{u=r p^(-e)}, {e,Abs[Numerator[u]],Denominator[u]}]];
padicLazyInfo0[Inactive[Minus][a_],p_] := padicLazyInfo[a,p];
padicLazyInfo0[t:Inactive[Times][a_,b_],p_] /; !padicLazyHasRootQ[t] :=
    padicLazyProductInfo[padicLazyInfo[a,p],padicLazyInfo[b,p]];
padicLazyProductInfo[{Infinity,_,_},_] := {Infinity,0,1};
padicLazyProductInfo[_,{Infinity,_,_}] := {Infinity,0,1};
padicLazyProductInfo[{e_,a_,b_},{f_,c_,d_}] := {e+f,a c,b d};
padicLazyInfo0[t:Inactive[Power][a_,k_Integer],p_] /; !padicLazyHasRootQ[t] :=
    padicLazyPowerInfo[padicLazyInfo[a,p],k];
padicLazyPowerInfo[{Infinity,_,_},k_] /; k <= 0 :=
    (Message[PadicN::zeropow,k]; Throw[Indeterminate,padicLazyFailure]);
padicLazyPowerInfo[{Infinity,_,_},k_Integer?Positive] := {Infinity,0,1};
padicLazyPowerInfo[{e_,a_,b_},k_Integer?NonNegative] := {e k,a^k,b^k};
padicLazyPowerInfo[{e_,a_,b_},k_Integer?Negative] := {e k,b^(-k),a^(-k)};
padicLazyInfo0[t:Inactive[Plus][a_,b_],p_] /; !padicLazyHasRootQ[t] :=
    padicLazySumInfo[padicLazyInfo[a,p],padicLazyInfo[b,p],a,b,p];
padicLazySumInfo[{Infinity,_,_},info_,_,_,_] := info;
padicLazySumInfo[info_,{Infinity,_,_},_,_,_] := info;
padicLazySumInfo[{e_,a_,b_},{f_,c_,d_},left_,right_,p_] :=
    Module[{v=Min[e,f],bound,n,s},
        bound = a d p^(e-v) + c b p^(f-v);
        n = IntegerLength[bound,p];
        s = padicNAdd[padicLazyEvaluate[left,p,v+n],padicLazyEvaluate[right,p,v+n]];
        (* p^n exceeds the numerator bound: a zero residue certifies exact zero. *)
        If[s[[1]] == 0, {Infinity,0,1},
            {s[[3]],Quotient[bound,p^(s[[3]]-v)],b d}]
    ];

(* Evaluate to absolute precision A. A source divisible by p^A contributes
   an uncertain zero. No intermediate value goes through Normal. *)
padicLazyEvaluate[0,p_,_] := PadicRationalN[0,p,Infinity,0];
padicLazyEvaluate[r:(_Integer|_Rational),p_,absolute_] := With[{e=PadicOrder[r,p]},
    If[e >= absolute, PadicRationalN[0,p,absolute,0], PadicN[r,p,absolute-e]]];
padicLazyEvaluate[Inactive[Plus][a_,b_],p_,absolute_] :=
    padicNAdd[padicLazyEvaluate[a,p,absolute],padicLazyEvaluate[b,p,absolute]];
padicLazyEvaluate[Inactive[Minus][a_],p_,absolute_] :=
    padicNMulScalar[padicLazyEvaluate[a,p,absolute],-1];
padicLazyEvaluate[t:Inactive[Times][a_,b_],p_,absolute_] :=
    With[{e=First[padicLazyInfo[a,p]],f=First[padicLazyInfo[b,p]]},
        Which[e === Infinity || f === Infinity, PadicRationalN[0,p,Infinity,0],
            e+f >= absolute, PadicRationalN[0,p,absolute,0],
            True, padicNMul[padicLazyEvaluate[a,p,absolute-f],
                padicLazyEvaluate[b,p,absolute-e]]]];
padicLazyEvaluate[t:Inactive[Power][a_,k_Integer],p_,absolute_] :=
    With[{v=First[padicLazyPowerInfo[padicLazyInfo[a,p],k]]},
        Which[v === Infinity, PadicRationalN[0,p,Infinity,0],
            v >= absolute, PadicRationalN[0,p,absolute,0],
            k == 0, PadicN[1,p,absolute],
            True, padicNPower[padicLazyEvaluate[a,p,
                First[padicLazyInfo[a,p]]+absolute-v],k]]];

padicLazySnapshot[tree_,p_,n_] := padicLazyCompute[padicLazySnapshot0[tree,p,n]];
padicLazySnapshot0[tree_,p_,Automatic] := With[{info=padicLazyInfo[tree,p]},
    padicLazySnapshot0[tree,p,
        If[First[info] === Infinity,1,IntegerLength[2 Max[Rest[info]]^2,p]]]];
padicLazySnapshot0[tree_,p_,n_Integer?Positive] := With[{e=First[padicLazyInfo[tree,p]]},
    If[e === Infinity, PadicRationalN[0,p,Infinity,n],
        padicNTruncate[padicLazyEvaluate[tree,p,e+n],n]]];

padicLazyReconstruct[tree_,p_] := padicLazyCompute[Module[{info,s,r},
    info = padicLazyInfo[tree,p];
    If[First[info] === Infinity, Return[0]];
    s = padicLazySnapshot0[tree,p,Automatic];
    r = PadicRationalApprox[s[[1]],p^s[[4]]];
    (* Rational recipes have propagated source bounds. Root recipes additionally
       need a local-branch equality certificate. Never accept a residue fallback
       as proof that an irrational source was actually rational. *)
    If[Abs[Numerator[r]] <= info[[2]] && Denominator[r] <= info[[3]] &&
        CoprimeQ[Denominator[r],p] &&
        Mod[Numerator[r]-s[[1]] Denominator[r],p^s[[4]]] == 0,
        If[!padicLazyHasRootQ[tree] || padicLazyRationalRootQ[tree,p,r,info[[1]]],
            r p^s[[3]],Missing["NotRational"]],
        If[padicLazyHasRootQ[tree],Missing["NotRational"],
            Failure["ReconstructionFailed",<|"Base"->p|>]]]
]];

PadicN[s_PadicLazy] := s;
PadicN[s_PadicLazy,p_] /; !padicNParametersQ[p,1] := $Failed;
PadicN[PadicLazy[t_,q_],p_?PrimeQ] /; p === q || !padicLazyHasRootQ[t] := PadicLazy[t,p];
PadicN[PadicLazy[_,q_],p_?PrimeQ] := (Message[PadicN::base,q,p]; $Failed);
PadicN[s_PadicLazy,p_,n_] /; !padicNParametersQ[p,n] := $Failed;
PadicN[PadicLazy[t_,q_],p_?PrimeQ,n:(Automatic|_Integer?Positive)] /;
    p === q || !padicLazyHasRootQ[t] :=
    padicLazySnapshot[t,p,n];
PadicN[PadicLazy[_,q_],p_?PrimeQ,n:(Automatic|_Integer?Positive)] :=
    (Message[PadicN::base,q,p]; $Failed);
PadicLazy /: Normal[PadicLazy[t_,p_]] := padicLazyReconstruct[t,p];
Padic[s:PadicLazy[_,p_]] := With[{r=Normal[s]},If[MissingQ[r],r,Padic[r,p]]];
Padic[s_PadicLazy,p_] := With[{r=Normal[s]},If[MissingQ[r],r,Padic[r,p]]];
PadicLazy /: PadicOrder[PadicLazy[t_,p_]] := padicLazyCompute[First[padicLazyInfo[t,p]]];
PadicLazy /: PadicOrder[s_PadicLazy,p_?PrimeQ] :=
    With[{a=PadicN[s,p]},If[a === $Failed,$Failed,PadicOrder[a]]];
PadicLazy /: PadicAbs[s_PadicLazy] := s[[2]]^(-PadicOrder[s]);
PadicLazy /: PadicAbs[s_PadicLazy,p_?PrimeQ] :=
    With[{e=PadicOrder[s,p]},If[e === $Failed,$Failed,p^(-e)]];
PadicLazy /: PadicCanonicalize[s_PadicLazy] := s;
PadicLazy /: PadicNormalize[s_PadicLazy] := With[{e=PadicOrder[s]},
    If[e === Infinity,s,s s[[2]]^(-e)]];

(* A finite operand remains a precision boundary, even beside a lazy source. *)
padicLazyFinite[op_,s_PadicRationalN,p_,t_] /; s[[2]] =!= p :=
    (Message[PadicN::base,s[[2]],p]; $Failed);
padicLazyFinite[Plus,PadicRationalN[0,p_,Infinity,_],p_,t_] := PadicLazy[t,p];
padicLazyFinite[Times,s:PadicRationalN[0,p_,Infinity,_],p_,_] := s;
padicLazyFinite[Plus,s:PadicRationalN[_,p_,_,_],p_,t_] := padicLazyCompute[
    padicNAdd[s,padicLazyEvaluate[t,p,s[[3]]+s[[4]]]]];
padicLazyFinite[Times,s:PadicRationalN[_,p_,_,_],p_,t_] :=
    padicLazyCompute[padicNMul[s,padicLazySnapshot0[t,p,Max[1,s[[4]]]]]];
PadicLazy /: Plus[s_PadicRationalN,PadicLazy[t_,p_]] := padicLazyFinite[Plus,s,p,t];
PadicLazy /: Times[s_PadicRationalN,PadicLazy[t_,p_]] := padicLazyFinite[Times,s,p,t];

(* Printing requests a preview, but InterpretationBox retains the source recipe.
   Sources use at most ten digits (or their smaller reconstruction precision). *)
padicLazyPreview[PadicLazy[0,p_]] := PadicRationalN[0,p,Infinity,1];
padicLazyPreview[PadicLazy[r:(_Integer|_Rational),p_]] :=
    PadicN[r,p,Min[10,padicNReconstructionPrecision[r p^(-PadicOrder[r,p]),p]]];
padicLazyPreview[PadicLazy[t_,p_]] := padicLazySnapshot[t,p,10];
PadicLazy /: MakeBoxes[s_PadicLazy,form:(StandardForm|TraditionalForm)] :=
    With[{boxes=ToBoxes[padicLazyPreview[s],form]}, InterpretationBox[boxes,s]];
PadicLazy /: PadicDigits[s_PadicLazy] := PadicDigits[padicLazyPreview[s]];
PadicLazy /: PadicDigits[s_PadicLazy,p_?PrimeQ] :=
    With[{a=PadicN[s,p]},If[a === $Failed,$Failed,PadicDigits[a]]];

(**************** Refinable algebraic square-root recipes ****************)

padicLazyHasRootQ[t_] := !FreeQ[t,Inactive[Power][_,1/2]];
padicLazyBinary[op_,a_,p_,b_,q_] /;
    p =!= q && (padicLazyHasRootQ[a] || padicLazyHasRootQ[b]) :=
    (Message[PadicN::base,p,q]; $Failed);
padicLazyBinary[op_,a_,p_,b_,q_] := PadicLazy[Inactive[op][a,b],Min[p,q]];

padicLazySqrt[a_,p_] := padicLazyCompute[With[{t=Inactive[Power][a,1/2]},
    padicLazyInfo[t,p]; PadicLazy[t,p]]];

(* Request the extra binary input bit before taking a root. Existence is
   checked even when the requested absolute precision contains only zero. *)
padicLazyEvaluate[Inactive[Power][a_,1/2],p_,absolute_] :=
    Module[{e=First[padicLazyInfo[a,p]],n,s,root},
        If[e === Infinity, Return[PadicRationalN[0,p,Infinity,0]]];
        If[OddQ[e], Throw[padicSqrtFailure[p],padicLazyFailure]];
        n = Max[If[p==2,3,1],absolute-e/2+If[p==2,1,0]];
        s = padicLazyEvaluate[a,p,e+n];
        root = padicNSqrt[s];
        If[root === Indeterminate || MissingQ[root], Throw[root,padicLazyFailure]];
        If[absolute <= e/2,PadicRationalN[0,p,absolute,0],
            padicNTruncate[root,absolute-e/2]]
    ];

(* Algebraic recipes need a zero/valuation certificate, not a guessed rational
   height. Build a primitive square-free annihilating polynomial. Resultants
   allow all conjugate combinations, so no real/complex branch assumptions
   enter this certificate. The modular evaluator selects the actual p-adic one. *)
padicPolynomialNormalize[f_] := Module[{z=padicPolynomialVariable,g,coefficients},
    g = Expand[Numerator[Together[f]]];
    g = Expand[Cancel[g/PolynomialGCD[g,D[g,z]]]];
    coefficients = CoefficientList[g,z];
    g *= LCM@@(Denominator /@ coefficients);
    g = Expand[g/(GCD@@CoefficientList[g,z])];
    Sign[Last[CoefficientList[g,z]]] g
];
padicPolynomialNonzeroCoefficients[f_] := With[{c=CoefficientList[f,padicPolynomialVariable]},
    Drop[c,Length[TakeWhile[c,#==0&]]]];
padicPolynomialValuationBound[f_,p_] := With[{c=padicPolynomialNonzeroCoefficients[f]},
    If[Length[c] == 1,0,Max[0,PadicOrder[First[c],p]]]];

padicLazyPolynomial0[r:(_Integer|_Rational)] :=
    Denominator[r] padicPolynomialVariable-Numerator[r];
padicLazyPolynomial0[Inactive[Minus][a_]] := padicPolynomialNormalize[
    padicLazyPolynomial[a] /. padicPolynomialVariable -> -padicPolynomialVariable];
padicLazyPolynomial0[Inactive[Power][a_,1/2]] := padicPolynomialNormalize[
    padicLazyPolynomial[a] /. padicPolynomialVariable -> padicPolynomialVariable^2];
padicLazyPolynomial0[Inactive[Plus][a_,b_]] := Module[{z=padicPolynomialVariable,v=Unique["root$"],f,g},
    f = padicLazyPolynomial[a] /. z -> v;
    g = padicLazyPolynomial[b] /. z -> z-v;
    padicPolynomialNormalize[Resultant[f,g,v]]
];
padicLazyPolynomial0[Inactive[Times][a_,b_]] :=
    Module[{z=padicPolynomialVariable,v=Unique["root$"],f,c,d,g},
        f = padicLazyPolynomial[a] /. z -> v;
        c = CoefficientList[padicLazyPolynomial[b],z]; d = Length[c]-1;
        g = Sum[c[[j+1]] z^j v^(d-j),{j,0,d}];
        padicPolynomialNormalize[Resultant[f,g,v]]
    ];
padicLazyPolynomial0[Inactive[Power][_,0]] := padicPolynomialVariable-1;
padicLazyPolynomial0[Inactive[Power][a_,k_Integer]] :=
    Module[{z=padicPolynomialVariable,v=Unique["root$"],f,g},
        f = padicLazyPolynomial[a] /. z -> v;
        g = If[k>0,z-v^k,z v^(-k)-1];
        padicPolynomialNormalize[Resultant[f,g,v]]
    ];

(* If c0 + c1*x + ... has integral coefficients and c0!=0, a nonzero
   p-adic root cannot have valuation greater than max(0,v_p(c0)). Remove
   zero-root factors first. A zero snapshot beyond this bound proves exact
   zero; otherwise it gives the exact valuation, without real radical evaluation.
   The rational-root theorem supplies bounds for any rational candidate. *)
padicLazyInfo0[t_,p_] /; padicLazyHasRootQ[t] :=
    Module[{children,f,c,s,e,unit},
        children = If[MatchQ[t,Inactive[Power][_,_]],{First[t]},List@@t];
        Scan[padicLazyInfo[#,p]&,children];
        If[MatchQ[t,Inactive[Power][_,_Integer]],
            padicLazyPowerInfo[padicLazyInfo[First[t],p],Last[t]]];
        f = padicLazyPolynomial[t];
        c = padicPolynomialNonzeroCoefficients[f];
        If[Length[c] == 1, Return[{Infinity,0,1}]];
        s = padicLazyEvaluate[t,p,padicPolynomialValuationBound[f,p]+1];
        If[s[[1]] == 0, Return[{Infinity,0,1}]];
        e = s[[3]];
        unit = padicPolynomialNormalize[f /. padicPolynomialVariable -> p^e padicPolynomialVariable];
        c = padicPolynomialNonzeroCoefficients[unit];
        {e,Abs[First[c]],Abs[Last[c]]}
    ];

(* A candidate must be a polynomial root AND match this particular local
   branch. A shifted annihilator bounds every nonzero candidate difference,
   certifying equality after enough matching modular digits. *)
padicLazyRationalRootQ[t_,p_,r_,e_] := Module[{f,shift,n,s},
    f = padicPolynomialNormalize[padicLazyPolynomial[t] /.
        padicPolynomialVariable -> p^e padicPolynomialVariable];
    If[(f /. padicPolynomialVariable -> r) =!= 0, Return[False]];
    shift = padicPolynomialNormalize[f /. padicPolynomialVariable -> padicPolynomialVariable+r];
    If[Length[padicPolynomialNonzeroCoefficients[shift]] == 1, Return[True]];
    n = padicPolynomialValuationBound[shift,p]+1;
    s = padicLazySnapshot0[t,p,n];
    Mod[Numerator[r]-s[[1]] Denominator[r],p^s[[4]]] == 0
];

(******************* P-adic Visualization ********************)

padicVertices[p_, depth_] :=
    Flatten[Table[If[n == 0, {{}}, Tuples[Range[0, p - 1], n]], {n, 0, depth}], 1];

padicEdges[p_, depth_] :=
    Module[{verts = padicVertices[p, depth], d = Range[0, p - 1]},
        Join[
            UndirectedEdge[{}, {#}] & /@ d,
            Flatten[Table[
                UndirectedEdge[v, Append[v, k]],
                {v, Select[verts, 1 <= Length[#] < depth &]}, {k, d}
            ], 1]
        ]];

edgeDigit[UndirectedEdge[a_, b_]] := Last[Last[SortBy[{a, b}, Length]]];

digitColorMap[p_, custom_] :=
    If[AssociationQ[custom], custom,
    If[ListQ[custom] && Length[custom] >= p,
        AssociationThread[Range[0, p - 1], Take[custom, p]],
        AssociationThread[Range[0, p - 1],
            Table[Hue[d / p, 0.85, 0.92], {d, 0, p - 1}]]
    ]];
 
(* Normalize RayDigits to a list of rays *)
(* Accepts:
     None                  -> {}
     {2,0,1}               -> {{2,0,1}}  (single)
     {{2,0,1},{1,1}}       -> as-is      (multi)
     PadicRational[...]    -> digits from expansion
     PadicRationalN[...]   -> reconstructed via Padic, then digits
     {PadicRational[...], {2,0,1}} -> mixed
*)

(* convert a PadicRational to a digit list *)
(* digits are root-outward = least significant first *)
padicRationalToRay[pr_PadicRational, depth_] :=
    Module[{m = pr[[1]], p = pr[[2]], n = pr[[4]], k = pr[[5]],
            raw, extended},
        raw = Reverse[IntegerDigits[m, p, n]];
        If[k > 0 && Length[raw] < depth,
            extended = Join[raw,
                Flatten[ConstantArray[raw[[-k ;;]],
                    Ceiling[(depth - Length[raw]) / k]]]];
            Take[extended, depth],
            PadRight[raw, depth, If[k > 0, raw[[-k ;;]], {0}]]
        ]
    ]

(* convert a PadicRationalN to a ray via reconstruction *)
padicRationalToRay[prn_PadicRationalN, depth_] :=
    padicRationalToRay[Padic[Normal[prn], prn[[2]]], depth]

padicRationalToRay[s_PadicLazy,depth_] := With[{a=PadicN[s,s[[2]],depth]},
    Reverse[IntegerDigits[a[[1]],s[[2]],depth]]];

normalizeRays[None] := {}
normalizeRays[pr_PadicRational] := {pr}
normalizeRays[prn_PadicRationalN] := {prn}
normalizeRays[s_PadicLazy] := {s}
normalizeRays[r_List] :=
    Which[
        r === {}, {},
        MatchQ[r, {__Integer}], {r},
        True, r
    ]

(* resolve a single ray spec to a digit list *)
resolveRay[digits_List, _] := digits
resolveRay[pr_PadicRational, depth_] := padicRationalToRay[pr, depth]
resolveRay[prn_PadicRationalN, depth_] := padicRationalToRay[prn, depth]
resolveRay[s_PadicLazy,depth_] := padicRationalToRay[s,depth]

(* build ray vertices and edges for one ray *)
singleRayData[digits_List, depth_] :=
    Module[{rayVerts, rayEdges},
        rayVerts = Join[{{}},
            Table[Take[digits, k], {k, 1, Min[depth, Length[digits]]}]];
        rayEdges = If[Length[rayVerts] >= 2,
            UndirectedEdge @@@ Partition[rayVerts, 2, 1], {}];
        {rayVerts, rayEdges}
    ]

(* build ray vertices and edges for one ray *)
buildSectors[graph_, p_, colors_, baseOpacity_, maxDepth_] :=
    Module[{coords, rootPos, r, primitives = {},
            parents, children, childCoords, childAngles,
            order, sortedAngles, sortedDigits, mids},

        coords  = AssociationThread[VertexList[graph], GraphEmbedding[graph]];
        rootPos = coords[{}];
        r = 1.02 Max[Norm[# - rootPos] & /@ Values[coords]];

        Do[
            parents = If[k == 1, {{}}, Tuples[Range[0, p - 1], k - 1]];
            Do[
                children    = Table[Append[parent, d], {d, 0, p - 1}];
                childCoords = Lookup[coords, children];
                If[MemberQ[childCoords, _Missing], Continue[]];
                childAngles = ArcTan @@ (# - rootPos) & /@ childCoords;
                order       = Ordering[childAngles];
                sortedAngles = childAngles[[order]];
                sortedDigits = Last /@ children[[order]];
                mids = Table[
                    Module[{a1 = sortedAngles[[i]],
                            a2 = sortedAngles[[Mod[i, p] + 1]]},
                        If[a2 < a1, a2 += 2 Pi];
                        Mod[(a1 + a2) / 2, 2 Pi, -Pi]],
                    {i, p}];
                mids = Sort[mids];
                Do[
                    Module[{digit = sortedDigits[[i]], a1, a2},
                        a1 = mids[[i]];
                        a2 = If[i < p, mids[[i + 1]], mids[[1]] + 2 Pi];
                        AppendTo[primitives,
                            {Directive[colors[digit], Opacity[baseOpacity / k]],
                             Disk[rootPos, r, {a1, a2}]}]],
                    {i, p}],
                {parent, parents}],
            {k, 1, maxDepth}];
        primitives
    ];

(* Cantor boundary (single dust ring) *)
(*                                                    *)
(* One ring. The tree's deepest leaves projected      *)
(* radially outward as small dots. The clustering     *)
(* and gaps emerge naturally from the tree geometry.  *)
(* Color by first digit = sector color.               *)
(*                                                    *)
(* The tree tells the story inside.                   *)
(* The ring shows where the story ends:               *)
(* clusters with gaps. Not a circle.                  *)

buildCantorBoundary[graph_, p_, colors_, dustRadius_, pointSize_, rays_] :=
    Module[{coords, rootPos, rMax, rDust, primitives = {},
            leaves, guideCircle, rayPrims = {}},

        coords  = AssociationThread[VertexList[graph], GraphEmbedding[graph]];
        rootPos = coords[{}];
        rMax    = Max[Norm[# - rootPos] & /@ Values[coords]];
        rDust   = rMax * dustRadius;

        guideCircle = {
            Directive[GrayLevel[0.45], Opacity[0.15], AbsoluteThickness[0.5]],
            Circle[rootPos, rDust]};

        leaves = Select[VertexList[graph],
            ListQ[#] && Length[#] == Max[Length /@ Select[VertexList[graph], ListQ]] &];

        (* Color by LAST digit: within each sector, adjacent dots
           have different colors, revealing the sub-clustering.
           First-digit coloring makes three solid arcs \[LongDash] useless.
           Last-digit coloring makes the fractal structure visible
           as color jumps between neighboring dots. *)
        Do[
            Module[{angle, pt, col},
                angle = ArcTan @@ (coords[v] - rootPos);
                pt    = rootPos + rDust {Cos[angle], Sin[angle]};
                col   = colors[Last[v]];
                AppendTo[primitives,
                    {col, AbsolutePointSize[pointSize], Point[pt]}]],
            {v, leaves}];

        Do[
            Module[{leafV, leafCoord, angle, pt},
                leafV = Take[ray, Min[Length[ray],
                    Max[Length /@ Select[VertexList[graph], ListQ]]]];
                leafCoord = Lookup[coords, Key[leafV], None];
                If[leafCoord =!= None,
                    angle = ArcTan @@ (leafCoord - rootPos);
                    pt    = rootPos + rDust {Cos[angle], Sin[angle]};
                    AppendTo[rayPrims,
                        {White, AbsolutePointSize[pointSize + 5], Point[pt],
                         colors[ray[[1]]], AbsolutePointSize[pointSize + 2],
                         Point[pt]}]]],
            {ray, rays}];

        Join[{guideCircle}, primitives, rayPrims]
    ];

(* compute max safe depth for a given p under edge budget *)
maxSafeDepth[p_, maxEdges_: 3000] :=
    Module[{d = 1},
        While[p (p^(d + 1) - 1) / (p - 1) <= maxEdges, d++];
        d];

(* extract base p from a ray spec; return 0 if plain digit list *)
rayBase[pr_PadicRational]  := pr[[2]]
rayBase[prn_PadicRationalN] := prn[[2]]
rayBase[_List] := 0
rayBase[s_PadicLazy] := s[[2]]
rayBase[_] := 0

(* reconcile rays to a common base: use smallest p, re-Padic the rest *)
reconcileRays[rays_, targetP_] :=
    Map[
        Which[
            ListQ[#], #,
            Head[#] === PadicRational && #[[2]] === targetP, #,
            Head[#] === PadicRational, Padic[Normal[#], targetP],
            Head[#] === PadicRationalN && #[[2]] === targetP, #,
            Head[#] === PadicRationalN, Padic[Normal[#], targetP],
            Head[#] === PadicLazy, PadicN[#,targetP],
            True, #] &,
        rays]

Options[PadicDigitTree] = {
    RayDigits             -> None,
    Layout                -> "Hyperbolic",
    VertexLabelMode       -> "None",
    EdgeLabelMode         -> "Ray",
    DigitColors           -> Automatic,
    SectorBackground      -> False,
    SectorBackgroundDepth -> 1,
    SectorOpacity         -> 0.07,
    CantorBoundary        -> False,
    CantorDustRadius      -> 1.12,
    CantorPointSize       -> 2,
    ImageSize             -> 900,
    Background            -> None
};

(* Calling pattern 1: p only \[LongDash] auto depth *)
PadicDigitTree::base = "The tree base `1` must be an integer greater than 1.";
PadicDigitTree::depth = "The requested depth `1` in base `3` would produce more than 10000 edges; using depth `2` instead.";
PadicDigitTree[p_Integer, opts : OptionsPattern[]] :=
    If[p > 1, PadicDigitTree[p, maxSafeDepth[p], opts],
        Message[PadicDigitTree::base,p]; $Failed]

(* Calling pattern 2: full explicit *)
PadicDigitTree[p_Integer, depth_Integer?Positive, opts : OptionsPattern[]] :=
Module[
    {d, verts, edges, rays, rayDataList,
     allRayVerts, allRayEdges,
     normalV, normalE, colors, layout, graphLayout,
     vLbl, eLbl, labelStyle, edgeLblStyle,
     graph, overlays = {}, maxEdges = 10000},

    If[p <= 1, Message[PadicDigitTree::base,p]; Return[$Failed]];
    (* safeguard: clamp depth so total edges ~ p*(p^d - 1)/(p-1) < maxEdges *)
    d = depth;
    While[d > 1 && p (p^d - 1) / (p - 1) > maxEdges, d--];
    If[d < depth, Message[PadicDigitTree::depth, depth, d, p]];

    verts  = padicVertices[p, d];
    edges  = padicEdges[p, d];
    colors = digitColorMap[p, OptionValue[DigitColors]];

    layout = OptionValue[Layout];
    graphLayout = Switch[layout,
        "Hyperbolic",
            {"HyperbolicRadialEmbedding", "RootVertex" -> {}},
        "Tree" | "TopDown",
            {"LayeredDigraphEmbedding", "RootVertex" -> {},
             "Orientation" -> Top},
        _,
            {"HyperbolicRadialEmbedding", "RootVertex" -> {}}
    ];

    rays = normalizeRays[OptionValue[RayDigits]];
    (* reconcile mixed bases: re-Padic everything to p *)
    rays = reconcileRays[rays, p];
    rays = resolveRay[#, d] & /@ rays;
    rayDataList = singleRayData[#, d] & /@ rays;

    allRayVerts = DeleteDuplicates[Join @@ (First /@ rayDataList)];
    allRayEdges = DeleteDuplicates[Join @@ (Last  /@ rayDataList)];

    normalV = Complement[verts, allRayVerts, {{}}];
    normalE = Complement[edges, allRayEdges];

    labelStyle   = Directive[White, 11, Bold];
    edgeLblStyle = Directive[White, 12, Bold];

    vLbl = Switch[OptionValue[VertexLabelMode],
        "FirstLayer",
            Join[{{} -> Placed[Style["\[Bullet]", labelStyle], Center]},
                ({#} -> Placed[Style[ToString[#], labelStyle], Center]) & /@
                    Range[0, p - 1]],
        "Ray",
            (# -> Placed[Style[
                If[# === {}, "\[Bullet]", StringJoin[ToString /@ #]],
                labelStyle], Center]) & /@ allRayVerts,
        "All",
            (# -> Placed[Style[
                If[# === {}, "\[Bullet]", StringJoin[ToString /@ #]],
                labelStyle], Center]) & /@ verts,
        _, None];

    eLbl = Module[{sel},
        sel = Switch[OptionValue[EdgeLabelMode],
            "FirstLevel", Select[edges, MemberQ[List @@ #, {}] &],
            "Ray",        allRayEdges,
            "All",        edges,
            _,            {}];
        If[sel === {}, None,
            (# -> Placed[
                Framed[Style[ToString @ edgeDigit[#], edgeLblStyle,
                    colors @ edgeDigit[#]],
                    Background -> RGBColor[.07, .08, .10, .72],
                    FrameStyle -> None, RoundingRadius -> 3,
                    FrameMargins -> Tiny], .35]) & /@ sel]];

    graph = TreeGraph[verts, edges,
        GraphLayout  -> graphLayout,
        VertexLabels -> vLbl,
        EdgeLabels   -> eLbl,
        VertexSize   -> Join[
            {{} -> .22},
            Thread[normalV -> .018],
            Thread[Complement[allRayVerts, {{}}] -> .10]],
        VertexStyle -> Join[
            {{} -> RGBColor[.45, .70, 1.]},
            Thread[normalV -> GrayLevel[.72]],
            Thread[Complement[allRayVerts, {{}}] -> RGBColor[.96, .97, 1.]]],
        EdgeStyle -> Join[
            (# -> Directive[colors @ edgeDigit[#], Opacity[.28],
                AbsoluteThickness[1]]) & /@ normalE,
            (# -> Directive[colors @ edgeDigit[#],
                AbsoluteThickness[4.2]]) & /@ allRayEdges],
        ImageSize        -> OptionValue[ImageSize],
        Background       -> OptionValue[Background],
        ImagePadding     -> 25,
        PlotRangePadding -> Scaled[.03]];

    If[TrueQ[OptionValue[SectorBackground]] && layout === "Hyperbolic",
        AppendTo[overlays,
            buildSectors[graph, p, colors,
                OptionValue[SectorOpacity],
                OptionValue[SectorBackgroundDepth]]]];

    If[TrueQ[OptionValue[CantorBoundary]] && layout === "Hyperbolic",
        AppendTo[overlays,
            buildCantorBoundary[graph, p, colors,
                OptionValue[CantorDustRadius],
                OptionValue[CantorPointSize],
                rays]]];

    If[overlays === {},
        graph,
        Show[Graphics[overlays], graph]]
]

End[] (* End `Private` *)

EndPackage[]
