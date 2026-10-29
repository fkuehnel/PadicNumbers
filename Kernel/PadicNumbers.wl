(* ::Package:: *)

(* Exact and Approximate p-adic arithmetic.
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

PadicDigitTree::usage = "PadicDigitTree[p,depth] draws a p-branching digit tree for integer bases 2 through 7 and positive integer depth. Larger bases emit PadicDigitTree::colors and return $Failed without constructing a graph. Automatic and explicit depths share a 3000-edge (3001-vertex) limit; oversized explicit depths are reduced with PadicDigitTree::depth before construction. Prime p gives the p-adic interpretation. RayDigits highlights paths specified in lowest-place-first order. Object rays currently use normalized unit digits; finite snapshot rays use a reconstructed rational candidate, while lazy rays request the required digits directly. See README.md for options and limitations.";
RayDigits::usage = "RayDigits is an option for PadicDigitTree specifying None, one list of lowest-place-first digits, a list of paths, or exact, lazy, or finite p-adic objects to highlight.";
Layout::usage = "Layout is an option for PadicDigitTree: \"Hyperbolic\" (default), \"TopDown\", or \"Tree\".";
VertexLabelMode::usage = "VertexLabelMode is an option for PadicDigitTree: \"None\" (default), \"FirstLayer\", \"Ray\", or \"All\".";
EdgeLabelMode::usage = "EdgeLabelMode is an option for PadicDigitTree: \"Ray\" (default), \"None\", \"FirstLevel\", or \"All\".";
DigitColors::usage = "DigitColors is an option for PadicDigitTree specifying Automatic, an association from digit integers to colors, or a list containing at least p colors.";
SectorBackground::usage = "SectorBackground is an option for PadicDigitTree enabling shaded sectors in the hyperbolic layout; the default is False.";
SectorBackgroundDepth::usage = "SectorBackgroundDepth is an option for PadicDigitTree specifying a nonnegative integer number of sector levels to shade, capped at the actual tree depth; the default is 1. Other values disable sector shading.";
SectorOpacity::usage = "SectorOpacity is an option for PadicDigitTree specifying the base sector opacity, reduced at deeper levels; the default is 0.07.";
CantorBoundary::usage = "CantorBoundary is an option for PadicDigitTree enabling a digit-boundary overlay in the hyperbolic layout; the default is False.";
CantorDustRadius::usage = "CantorDustRadius is an option for PadicDigitTree specifying the radius of the boundary overlay; the default is 1.12.";
CantorPointSize::usage = "CantorPointSize is an option for PadicDigitTree specifying the boundary dot size; the default is 2.";

Begin["`Private`"]

(******************* P-adic Order and Value ******************)

PadicOrder[n_Integer,p_Integer/;p>1] := IntegerExponent[n,p]
PadicOrder[r_Rational,p_Integer/;p>1] :=
    IntegerExponent[Numerator[r],p]-IntegerExponent[Denominator[r],p]

PadicAbs[n:(_Integer|_Rational),p_Integer/;p>1] :=
    p^(-PadicOrder[n,p])
PadicNormalize[n:(_Integer|_Rational),p_Integer/;p>1] :=
    n*PadicAbs[n,p]

(* PadicRational upvalues *)

PadicRational /: PadicOrder[PadicRational[0,_,___]] := Infinity
PadicRational /: PadicOrder[PadicRational[_,_,e_,___]] := e
PadicRational /: PadicOrder[s:PadicRational[_,p_,___],p_] :=
    PadicOrder[s]

PadicRational /: PadicAbs[s:PadicRational[_,p_,_,___]] :=
    p^(-PadicOrder[s])
PadicRational /: PadicAbs[s:PadicRational[_,p_,_,___],p_] :=
    PadicAbs[s]

PadicRational /: PadicNormalize[PadicRational[m_,p_,_,n_,k_]] :=
    PadicRational[m,p,0,n,k]

(* cross-base PadicOrder and PadicAbs *)
PadicRational /: PadicOrder[
    s:PadicRational[_,p1_,_,___],p2_Integer/;p2>1] :=
    PadicOrder[Normal[s],p2] /; p1 != p2
PadicRational /: PadicAbs[
    s:PadicRational[_,p1_,_,___],p2_Integer/;p2>1] :=
    PadicAbs[Normal[s],p2] /; p1 != p2

(* PadicRationalN upvalues -- lossy representation *)

PadicRationalN /: PadicOrder[PadicRationalN[0,_,e_,n_]] :=
    If[e === Infinity, Infinity, Interval[{e+n, Infinity}]]
PadicRationalN /: PadicOrder[PadicRationalN[_,_,e_,_]] := e
PadicRationalN /: PadicOrder[s:PadicRationalN[_,p_,_,_],p_] :=
    PadicOrder[s]

PadicRationalN /: PadicAbs[s:PadicRationalN[_,p_,_,_]] :=
    p^(-PadicOrder[s])
PadicRationalN /: PadicAbs[s:PadicRationalN[_,p_,_,_],p_] :=
    PadicAbs[s]

PadicRationalN /: PadicNormalize[s:PadicRationalN[0,___]] := s
PadicRationalN /: PadicNormalize[PadicRationalN[m_,p_,_,n_]] :=
    PadicRationalN[m,p,0,n]

(* Canonicalize the residue while preserving absolute precision e+n. *)
PadicRationalN /: PadicCanonicalize[s_PadicRationalN] :=
    padicNCanonical[s]

(**************** Exact signatures and construction ****************)

Padic::prime =
    "Base `1` must be a prime integer greater than 1.";
Padic::zeropow =
    "Cannot raise zero to exponent `1`; zero has no multiplicative inverse.";
Padic::sqrt =
    "The value has no square root in the `1`-adic field.";

(* Helpers receive a valid prime p and a reduced unit a/b, or zero.
   MultiplicativeOrder determines the period without enumerating its digits. *)
padicPeriod[a_Integer,1,_Integer] /; a < 0 := 1;
padicPeriod[_Integer,1,_Integer] := 0;
padicPeriod[_Integer,b_Integer,p_Integer] := MultiplicativeOrder[p,b];

padicUnitSignature[a_Integer,1,p_Integer] /; a > 0 :=
    {IntegerLength[a,p],0};
padicUnitSignature[a_Integer,b_Integer,p_Integer] :=
    Module[{t=a,j=0,inv=PowerMod[b,-1,p],k=padicPeriod[a,b,p]},
        (* Walk only the prefix until -b <= t <= 0.
           For a nonzero unit, t cannot be zero here. *)
        (* Lean: PadicExact.loop_terminates and modular_decode_roundtrip. *)
        While[t > 0 || t < -b,
            t = Quotient[t-b Mod[t inv,p],p];
            j++
        ];
        {j+k,k}
    ];

PadicPeriodLength[r:(_Integer|_Rational),p_Integer] /; p > 1 && PrimeQ[p] :=
    With[{u=PadicNormalize[r,p]},
        padicPeriod[Numerator[u],Denominator[u],p]];
PadicPeriodLength[_Integer|_Rational,p_Integer] :=
    (Message[Padic::prime,p]; $Failed);
PadicPeriodLength[s_PadicRational] :=
    PadicPeriodLength[Normal[s], s[[2]]];
PadicPeriodLength[s_PadicRational, p_Integer] :=
    PadicPeriodLength[Normal[s], p];

PadicSignature[r:(_Integer|_Rational),p_Integer] /; p > 1 && PrimeQ[p] :=
    With[{u=PadicNormalize[r,p]},
        padicUnitSignature[Numerator[u],Denominator[u],p]];
PadicSignature[_Integer|_Rational,p_Integer] :=
    (Message[Padic::prime,p]; $Failed);
PadicSignature[s_PadicRational] := PadicSignature[Normal[s], s[[2]]];
PadicSignature[s_PadicRational, p_Integer] := PadicSignature[Normal[s], p];

(* Construct from a reduced nonzero unit a/b and its valuation e. *)
padicFromUnit[a_Integer,1,p_Integer,e_] /; a > 0 :=
    PadicRational[a,p,e,IntegerLength[a,p],0];
padicFromUnit[a_Integer,b_Integer,p_Integer,e_] :=
    Module[{n,k,q},
        {n,k} = padicUnitSignature[a,b,p];
        q = p^n;
        PadicRational[Mod[a PowerMod[b,-1,q],q],p,e,n,k]
    ];

Padic[0,p_Integer] /; p > 1 && PrimeQ[p] := PadicRational[0,p,0,0,0];
Padic[r:(_Integer|_Rational),p_Integer] /; p > 1 && PrimeQ[p] :=
    With[{e=PadicOrder[r,p]},
        With[{u=r p^(-e)},
            padicFromUnit[Numerator[u],Denominator[u],p,e]]];
Padic[_Integer|_Rational,p_Integer] :=
    (Message[Padic::prime,p]; $Failed);

Padic[s_PadicRational] := s;
Padic[s:PadicRational[_,p_,___],p_Integer] := s;
Padic[s_PadicRational, p_Integer] :=
    Padic[Normal[s],p];
SetAttributes[Padic, Listable];

(* Rational reconstruction of a lossy value yields a candidate, not a
   certified recovery of the original rational. This API is retained. *)
padicFromReconstruction[r_Missing,_] := r;
padicFromReconstruction[r:(_Integer|_Rational),p_] := Padic[r,p];
Padic[s_PadicRationalN] := Padic[s,s[[2]]];
Padic[s_PadicRationalN, p_Integer] :=
    padicFromReconstruction[Normal[s],p];
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
PadicDigits[PadicRational[m_,p_,e_Integer,n_Integer,___]] :=
    PadRight[IntegerDigits[m,p,n],n+Max[0,e]]

PadicDigits[PadicRationalN[0,___]] := {0}
PadicDigits[PadicRationalN[m_,p_,e_Integer,n_Integer]] :=
    PadRight[IntegerDigits[m,p,n],n+Max[0,e]]

(********************** P-adic formatting ********************)

(* Keep digits numeric until after splitting periods and placing the radix
   point. Bases through 36 use A=10,...,Z=35; larger bases use decimal
   digit values with bars, including at the boundary of a repeating block. *)

padicDigitSymbol[d_Integer,p_] /; p <= 36 && d >= 10 :=
    FromCharacterCode[55+d];
padicDigitSymbol[d_,_] := d;

padicDigitSeparator[p_] /; p <= 36 := " ";
padicDigitSeparator[_] := "|";

padicDigitRow[digits_List,p_] :=
    Row[padicDigitSymbol[#,p]& /@ digits,padicDigitSeparator[p]];

(* Small bases separate every displayed item with spaces. Large bases
   separate digits with bars, but place the radix point between runs. *)
padicFractionalRow[digits_List,p_,e_] /; p <= 36 :=
    padicDigitRow[Insert[digits,".",e-1],p];
padicFractionalRow[digits_List,p_,e_] :=
    With[{parts=TakeDrop[digits,Length[digits]+e]},
        Row[{padicDigitRow[parts[[1]],p],".",
            padicDigitRow[parts[[2]],p]}]];

(* Shared inline rendering for exact terminating and finite expansions.
   PadicDigits already appends zeros for nonnegative valuations. *)
padicInlineRow[s_,p_,e_,_] /; e >= 0 :=
    padicDigitRow[PadicDigits[s],p];
padicInlineRow[s_,p_,e_,n_] /; e < 0 :=
    padicFractionalRow[PadLeft[PadicDigits[s],Max[n,-e]],p,e];

padicPeriodicColor = RGBColor[0.7,0.5,0.3];

padicPeriodicRow[digits_List,p_] :=
    Style[OverBar[padicDigitRow[digits,p]],padicPeriodicColor];

(* Render valuation-zero objects directly, without calling Format.
   Pure periods have no trailing row or separator. Mixed periods are
   split while digits are still numeric. *)
padicUnitDisplay[s:PadicRational[_,p_,0,_,0]] :=
    Subscript[padicDigitRow[PadicDigits[s],p],p];
padicUnitDisplay[s:PadicRational[_,p_,0,k_,k_]] /; k > 0 :=
    Subscript[padicPeriodicRow[PadicDigits[s],p],p];
padicUnitDisplay[s:PadicRational[_,p_,0,n_,k_]] /; n > k > 0 :=
    With[{parts=TakeDrop[PadicDigits[s],k]},
        Subscript[
            Row[{padicPeriodicRow[parts[[1]],p],
                padicDigitRow[parts[[2]],p]},
                padicDigitSeparator[p]],
            p]];

padicUnitDisplay[PadicRationalN[0,p_,0,n_Integer]] :=
    Row[{"O(",Superscript[p,n],")"}];
padicUnitDisplay[s:PadicRationalN[_,p_,0,_]] :=
    Subscript[Row[{"~",padicDigitRow[PadicDigits[s],p]}],p];

(* Preserve ordinary display for an unsupported unit representation. *)
padicUnitDisplay[s_] := s;

padicScaledRow[unitDisplay_,p_,e_] :=
    Row[{unitDisplay,Superscript[p,e]},"\[Times]"];

(* Exact terminating expansions: inline valuations from -4 through 4. *)
PadicRational /: Format[
    s:PadicRational[_,p_,e_/;-4 <= e <= 4,n_,0]] :=
    Subscript[padicInlineRow[s,p,e,n],p];

(* Exact periodic expansions: inline only at valuation zero. *)
PadicRational /: Format[
    s:PadicRational[_,_,0,k_,k_] /; k > 0] :=
    padicUnitDisplay[s];
PadicRational /: Format[
    s:PadicRational[_,_,0,n_,k_] /; n > k > 0] :=
    padicUnitDisplay[s];

(* Remaining nonzero valuations: render the unit, then attach p^e. *)
PadicRational /: Format[
    s:PadicRational[_,p_,e_Integer/;e != 0,_,_]] :=
    padicScaledRow[padicUnitDisplay[ReplacePart[s,3->0]],p,e];

(* Finite expansions: distinguish exact zero, uncertain zero, and
   nonzero values. The tilde marks the finite digit display as lossy. *)
PadicRationalN /: Format[PadicRationalN[0,p_,Infinity,_]] :=
    Subscript[0,p];
PadicRationalN /: Format[PadicRationalN[0,p_,e_Integer,n_Integer]] :=
    Row[{"O(",Superscript[p,e+n],")"}];

PadicRationalN /: Format[
    s:PadicRationalN[_,p_,e_/;-4 <= e <= 4,n_]] :=
    Subscript[Row[{"~",padicInlineRow[s,p,e,n]}],p];

PadicRationalN /: Format[
    s:PadicRationalN[_,p_,e_Integer/;e != 0,_]] :=
    padicScaledRow[padicUnitDisplay[ReplacePart[s,3->0]],p,e];

(******************** P-adic arithmetic **********************)

(* Rebuild from the exact value to normalize valuation, zero, repeated
   period blocks, and cycle rotation. *)
PadicCanonicalize[s_PadicRational] :=
    Padic[Normal[s],s[[2]]];

(* Addition and multiplication decode, operate on exact rationals, and
   re-encode canonically. For different bases, use the smaller base.
   Mathematical model: PadicExact.value_add and value_mul.
   These references do not verify Wolfram evaluation or dispatch. *)
padicBinary[op_,a_PadicRational,b_PadicRational] :=
    Padic[op[Normal[a],Normal[b]],Min[a[[2]],b[[2]]]];

PadicRational /: Plus[a_PadicRational,b_PadicRational] :=
    padicBinary[Plus,a,b];
PadicRational /: Times[a_PadicRational,b_PadicRational] :=
    padicBinary[Times,a,b];

PadicRational /: Plus[a_PadicRational,b:(_Integer|_Rational)] :=
    Padic[Normal[a]+b,a[[2]]];
PadicRational /: Times[a_PadicRational,b:(_Integer|_Rational)] :=
    Padic[Normal[a] b,a[[2]]];

(* Negation works directly on normalized digits: the unit digit becomes
   p-d, and higher digits become p-1-d. Canonical inputs already have a
   minimal period; only a zero repeating block or redundant prefix
   needs removing. *)

(* A zero repeating block leaves a terminating expansion. *)
padicTrimNegatedDigits[m_,p_,e_,n_,k_] /; m < p^(n-k) :=
    PadicRational[m,p,e,IntegerLength[m,p],0];

(* Remove prefix digits that continue the repeating block. *)
padicTrimNegatedDigits[m_,p_,e_,n_,k_] :=
    Module[{r=m,length=n},
        While[length > k &&
            Mod[Quotient[r,p^(length-k-1)],p] ==
                Quotient[r,p^(length-1)],
            r = Mod[r,p^(length-1)];
            length--
        ];
        PadicRational[r,p,e,length,k]
    ];

PadicRational /: Minus[PadicRational[0,p_,___]] :=
    PadicRational[0,p,0,0,0];

(* Terminating digits acquire a repeating p-1 tail. *)
PadicRational /: Minus[PadicRational[m_,p_,e_,n_,0]] :=
    padicTrimNegatedDigits[p^(n+1)-m,p,e,n+1,1];

(* A nonempty prefix absorbs the exceptional unit-digit complement. *)
PadicRational /: Minus[PadicRational[m_,p_,e_,n_,k_]] /; n > k > 0 :=
    padicTrimNegatedDigits[p^n-m,p,e,n,k];

(* A pure cycle needs one extra digit before complementing. *)
PadicRational /: Minus[PadicRational[m_,p_,e_,k_,k_]] /; k > 0 :=
    padicTrimNegatedDigits[
        p^(k+1)-m-Mod[m,p] p^k,p,e,k+1,k];

(* Ordinary unary -x is represented internally as Times[-1,x]. *)
PadicRational /: Times[-1,a_PadicRational] :=
    Minus[a];

(* Power a reduced nonzero unit a/b using integers only.
   Negative exponents invert the pair with a positive denominator.
   padicFromUnit recomputes the signature and encodes the powered unit;
   neither branch calls Normal or constructs an intermediate Rational. *)
padicPowerUnit[a_,b_,p_,e_,exponent_Integer?Negative] :=
    padicFromUnit[
        (Sign[a] b)^(-exponent),Abs[a]^(-exponent),
        p,e exponent];

padicPowerUnit[a_,b_,p_,e_,exponent_Integer?Positive] :=
    padicFromUnit[a^exponent,b^exponent,p,e exponent];

(* Zero has distinct negative-, zero-, and positive-power behavior. *)
PadicRational /: Power[
    PadicRational[0,___],exponent_Integer?Negative] :=
    (Message[Padic::zeropow,exponent]; Indeterminate);

PadicRational /: Power[PadicRational[0,___],0] :=
    (Message[Power::indet,HoldForm[0^0]]; Indeterminate);

PadicRational /: Power[
    PadicRational[0,p_,___],exponent_Integer?Positive] :=
    PadicRational[0,p,0,0,0];

(* Identity powers. The zero-specific rule above handles 0^0. *)
PadicRational /: Power[PadicRational[_,p_,___],0] :=
    PadicRational[1,p,0,1,0];
PadicRational /: Power[a_PadicRational,1] :=
    a;

(* Positive powers of terminating units remain terminating.
   Compute the powered significand once. *)
PadicRational /: Power[
    PadicRational[m_,p_,e_,_,0],exponent_Integer?Positive] :=
    With[{v=m^exponent},
        PadicRational[v,p,e exponent,IntegerLength[v,p],0]];

(* A negative power of a terminating unit powers its reciprocal. *)
PadicRational /: Power[
    PadicRational[m_,p_,e_,_,0],exponent_Integer?Negative] :=
    padicPowerUnit[1,m,p,-e,-exponent];

(* For prefix L and repeating block B, the unit is
       (L (p^k-1) - B p^(n-k))/(p^k-1).
   Reduce this integer pair before powering. The resulting period can
   grow, shrink, or disappear, so the unit encoder recomputes it.
   Integer powers also handle Times[a,a], which can become Power[a,2]. *)
PadicRational /: Power[
    PadicRational[m_,p_,e_,n_,k_],exponent_Integer] /; k > 0 :=
    Module[
        {scale=p^(n-k),denominator=p^k-1,
         block,prefix,numerator,g},
        {block,prefix} = QuotientRemainder[m,scale];
        numerator = prefix denominator - block scale;
        g = GCD[numerator,denominator];
        padicPowerUnit[
            Quotient[numerator,g],Quotient[denominator,g],
            p,e,exponent]
    ];

(* Sqrt is internally Power[...,1/2]. A rational root remains exact;
   an irrational p-adic root retains its defining lazy recipe. *)
PadicRational /: Power[s_PadicRational,1/2] :=
    padicExactSqrt[Normal[s],s[[2]]];

(****************** P-adic lossy precision *******************)

PadicN::prime = "The base `1` must be a prime integer.";
PadicN::prec = "Relative precision `1` must be a positive integer.";
PadicN::base = "Cannot combine finite-precision p-adics with bases `1` and `2`.";
PadicN::zeropow = "Exact zero cannot be raised to exponent `1`.";
PadicN::precision = "A value known only to O(p^`1`) may be zero; this operation requires a nonzero value.";
PadicN::sqrtprec = "The stored digits do not determine a square-root branch in base `1`; more source precision is required.";

(* PrimeQ also accepts negative primes. Package bases must be positive. *)
padicNPrimeQ[p_Integer?Positive] := PrimeQ[p];
padicNPrimeQ[_] := False;

(* Validate the base before precision, including Automatic and zero inputs.
   Compute primality once within this diagnostic helper. *)
padicNParametersQ[p_,n_] :=
    padicNParameterResult[padicNPrimeQ[p],p,n];
padicNParameterResult[False,p_,_] :=
    (Message[PadicN::prime,p]; False);
padicNParameterResult[True,_,Automatic] := True;
padicNParameterResult[True,_,n_Integer?Positive] := True;
padicNParameterResult[True,_,n_] :=
    (Message[PadicN::prec,n]; False);

(* The unit u has valuation zero. Integer units need no modular inverse;
   rational units have a denominator coprime to p. *)
padicNUnitResidue[u_Integer,p_,n_] := Mod[u,p^n];
padicNUnitResidue[u_,p_,n_] :=
    With[{modulus=p^n},
        Mod[Numerator[u] PowerMod[Denominator[u],-1,modulus],modulus]];

(* The least n with p^n > 2 H^2 places both normalized numerator and
   denominator strictly inside the symmetric reconstruction bound.
   IntegerLength handles powers on the boundary exactly. *)
padicNReconstructionPrecision[u_,p_] :=
    IntegerLength[2 Max[Abs[Numerator[u]],Denominator[u]]^2,p];

padicNRequestedPrecision[u_,p_,Automatic] :=
    padicNReconstructionPrecision[u,p];
padicNRequestedPrecision[_,_,n_Integer?Positive] := n;

(* Two arguments retain the rational source for lazy evaluation. *)
PadicN[r:(_Integer|_Rational),p_] /; !padicNParametersQ[p,1] := $Failed;
PadicN[r:(_Integer|_Rational),p_?padicNPrimeQ] := PadicLazy[r,p];

(* Successful eager rules also require valid arguments, so more specific
   zero and Automatic patterns cannot bypass diagnostic validation. *)
PadicN[r:(_Integer|_Rational|_PadicRationalN),p_,n_] /;
    !padicNParametersQ[p,n] := $Failed;

PadicN[0,p_?padicNPrimeQ,Automatic] := PadicRationalN[0,p,Infinity,1];
PadicN[0,p_?padicNPrimeQ,n_Integer?Positive] := PadicRationalN[0,p,Infinity,n];

(* Normalize once, select relative precision, and encode the unit directly.
   Zero is handled above before computing its infinite valuation. *)
PadicN[r:(_Integer|_Rational),p_?padicNPrimeQ,n:(Automatic|_Integer?Positive)] :=
    Module[{e,u,digits},
        e = PadicOrder[r,p];
        u = r p^(-e);
        digits = padicNRequestedPrecision[u,p,n];
        PadicRationalN[padicNUnitResidue[u,p,digits],p,e,digits]
    ];

(* Exact inputs retain their known source, including across bases. *)
PadicRational /: PadicN[s_PadicRational] := PadicN[Normal[s],s[[2]]];
PadicN[s_PadicRational,p_] := PadicN[Normal[s],p];
PadicN[s_PadicRational,p_,n_] := PadicN[Normal[s],p,n];

(* Existing finite snapshots cannot regain digits or change base.
   Canonicalize before considering an unchanged-precision shortcut. *)
PadicN[s_PadicRationalN] := padicNCanonical[s];
PadicN[s:PadicRationalN[_,p_,_,_],p_] := padicNCanonical[s];
PadicN[s_PadicRationalN,p_] :=
    (Message[PadicN::base,s[[2]],p]; $Failed);
PadicN[s:PadicRationalN[_,p_,_,_],p_?padicNPrimeQ,Automatic] :=
    padicNCanonical[s];
PadicN[s:PadicRationalN[_,p_,_,_],p_?padicNPrimeQ,n_Integer?Positive] :=
    padicNTruncate[padicNCanonical[s],n];
PadicN[s_PadicRationalN,p_?padicNPrimeQ,n:(Automatic|_Integer?Positive)] :=
    (Message[PadicN::base,s[[2]],p]; $Failed);

(* Callers supply canonical snapshots. Preserve both kinds of zero and
   return unchanged snapshots directly when no digits can be discarded. *)
padicNTruncate[s:PadicRationalN[0,___],_] := s;
padicNTruncate[s:PadicRationalN[_,_,_,n_],requested_] /; requested >= n := s;
padicNTruncate[PadicRationalN[m_,p_,e_,n_],requested_] :=
    padicNFromResidue[m,p,e,Min[n,requested]];

(* Validate the Euclidean candidate before division. Cancelling a common
   factor could destroy its congruence. Failed validation retains m. *)
padicNReconstructionResult[m_,modulus_,b_,t_] /;
    t != 0 && 2 b^2 < modulus && 2 t^2 < modulus &&
    CoprimeQ[b,t] && CoprimeQ[t,modulus] && Mod[b-m t,modulus] == 0 := b/t;
padicNReconstructionResult[m_,_,_,_] := m;

(* RATCONVERT: callers supply integers pN > 1 and 0 <= m < pN.
   Both reconstruction bounds are strict. The Euclidean loop runs once;
   its final pair is passed to the guarded result selector.
   Lean model and proof: Proofs/PadicReconstruction.lean. *)
PadicRationalApprox[m_,pN_] :=
    Module[{a=pN,b=m,s=0,t=1,q},
        While[2 b^2 >= pN,
            q = Quotient[a,b];
            {a,b} = {b,a-q b};
            {s,t} = {t,s-q t}
        ];
        padicNReconstructionResult[m,pN,b,t]
    ];

(* Normal reconstructs a candidate from finite data, not a certified source.
   Exact zero and uncertain zero remain distinct. *)
PadicRationalN /: Normal[PadicRationalN[0,_,Infinity,_]] := 0;
PadicRationalN /: Normal[PadicRationalN[0,_,e_,n_]] :=
    Missing["InsufficientPrecision",e+n];
PadicRationalN /: Normal[PadicRationalN[m_,p_,e_,n_]] :=
    PadicRationalApprox[m,p^n] p^e;

(* Preserve the existing symbolic traversal and atomic passthrough. *)
PadicN[e_Plus,p_Integer,prec_Integer] := PadicN[#,p,prec]& /@ e;
PadicN[e_Times,p_Integer,prec_Integer] := PadicN[#,p,prec]& /@ e;
PadicN[x_^n_,p_Integer,prec_Integer] := PadicN[x,p,prec]^n;

SetAttributes[PadicN,Listable];
PadicN[e_,__] := e /; AtomQ[e];

(**************** P-adic N lossy arithmetic ******************)

(* All arithmetic uses residues and bounds, never rational reconstruction. *)
padicNFromResidue[_,p_,e_,n_] /; n <= 0 := PadicRationalN[0,p,e+n,0];
padicNFromResidue[m_,p_,e_,n_] := padicNReducedResidue[Mod[m,p^n],p,e,n];
padicNReducedResidue[0,p_,e_,n_] := PadicRationalN[0,p,e+n,0];
padicNReducedResidue[r_,p_,e_,n_] := With[{k=PadicOrder[r,p]},
    PadicRationalN[r/p^k,p,e+k,n-k]];
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

(* Skip terms beyond the common precision before computing any shift.
   If neither term is known, the residue constructor retains the bound. *)
padicNAlignedResidue[PadicRationalN[_,_,e_,_],_,absolute_] /; e >= absolute := 0;
padicNAlignedResidue[PadicRationalN[m_,p_,e_,_],origin_,_] := m p^(e-origin);

padicNAdd[x_,y_] := Module[{a=padicNCanonical[x],b=padicNCanonical[y],p,e,absolute},
    p = a[[2]];
    absolute = Min[a[[3]]+a[[4]],b[[3]]+b[[4]]];
    e = Min[a[[3]],b[[3]]];
    padicNFromResidue[padicNAlignedResidue[a,e,absolute]+padicNAlignedResidue[b,e,absolute],
        p,e,absolute-e]
];
padicNMul[x_,y_] := Module[{a,b,p},
    a = padicNCanonical[x]; b = padicNCanonical[y]; p = a[[2]];
    padicNFromResidue[a[[1]] b[[1]],p,a[[3]]+b[[3]],Min[a[[4]],b[[4]]]]
];

(* Scalars are exact: preserve the input's absolute precision under addition
   and relative precision under multiplication, including p-power factors. *)
padicNAddScalar[PadicRationalN[0,_,Infinity,_], r_] := r;
padicNMulScalar[a:PadicRationalN[0,_,Infinity,_], _] := a;

(* Canonicalize and compute the scalar valuation once, before dispatch.
   The addition cutoff includes r=0, whose valuation is Infinity. *)
padicNAddScalar[x_,r_] := With[{a=padicNCanonical[x]},
    padicNAddScalarAtOrder[a,r,PadicOrder[r,a[[2]]]]];
padicNAddScalarAtOrder[a:PadicRationalN[_,_,e_,n_],_,v_] /; v >= e+n := a;
padicNAddScalarAtOrder[PadicRationalN[m_,p_,e_,n_],r_,v_] :=
    With[{origin=Min[e,v],absolute=e+n},
        padicNFromResidue[m p^(e-origin) +
            padicNUnitResidue[r p^(-v),p,absolute-v] p^(v-origin),
            p,origin,absolute-origin]];

(* Restrict the scalar-zero rule to finite valuations so an exact-zero
   input retains its original marker, even when the scalar is also zero. *)
padicNMulScalar[PadicRationalN[_,p_,_Integer,_],0] := PadicRationalN[0,p,Infinity,0];
padicNMulScalar[x_,r_] := With[{a=padicNCanonical[x]},
    padicNMulScalarAtOrder[a,r,PadicOrder[r,a[[2]]]]];
padicNMulScalarAtOrder[PadicRationalN[0,p_,e_,_],_,v_] := PadicRationalN[0,p,e+v,0];
padicNMulScalarAtOrder[PadicRationalN[m_,p_,e_,n_],r_,v_] :=
    padicNFromResidue[m padicNUnitResidue[r p^(-v),p,n],p,e+v,n];
padicNMixed[op_,a_,b_] := op[a,Normal[b]];

padicNPower[a:PadicRationalN[0,_,Infinity,_], exponent_Integer?Positive] := a;
padicNPower[PadicRationalN[0,_,Infinity,_], exponent_Integer] /; exponent <= 0 :=
    (Message[PadicN::zeropow,exponent]; Indeterminate);

padicNPower[x_,exponent_] := padicNPowerCanonical[padicNCanonical[x],exponent];
padicNPowerCanonical[_,0] := 1;
padicNPowerCanonical[PadicRationalN[0,_,e_,_],exponent_] /; exponent < 0 :=
    (Message[PadicN::precision,e]; Indeterminate);
padicNPowerCanonical[PadicRationalN[0,p_,e_,_],exponent_] /; exponent > 0 :=
    PadicRationalN[0,p,e exponent,0];
padicNPowerCanonical[PadicRationalN[m_,p_,e_,n_],exponent_] :=
    With[{precision=padicNPowerPrecision[p,n,exponent]},
        PadicRationalN[PowerMod[m,exponent,p^precision],p,e exponent,precision]];

(* Even powers of odd 2-adic units are constant modulo an extra factor 2. *)
padicNPowerPrecision[2,1,exponent_?EvenQ] := 2+PadicOrder[Abs[exponent],2];
padicNPowerPrecision[p_,n_,exponent_] := n+PadicOrder[Abs[exponent],p];

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
padicSqrtUnit[m_,p_,n_] := padicSqrtLift[PowerModList[m,1/2,p],m,p,n];
padicSqrtLift[{},_,p_,_] := padicSqrtFailure[p];
padicSqrtLift[roots_,m_,p_,n_] := Module[{y=Min[roots],k=1,modulus},
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
padicNSqrt[PadicRationalN[m_,p_,e_,n_]] :=
    padicNSqrtResult[padicSqrtUnit[m,p,n],p,e,n];
padicNSqrtResult[Indeterminate,_,_,_] := Indeterminate;
padicNSqrtResult[y_,p_,e_,n_] := PadicRationalN[y,p,e/2,padicSqrtPrecision[p,n]];
padicSqrtPrecision[2,n_] := n-1;
padicSqrtPrecision[_,n_] := n;

(* The smallest sample that certifies existence also fixes the branch:
   two root bits for p=2, one root digit for odd primes. *)
padicSqrtSeedPrecision[2] := 3;
padicSqrtSeedPrecision[_] := 1;
padicExactSqrt[0,p_] := Padic[0,p];
padicExactSqrt[r_,p_] :=
    padicExactSqrtFromSample[r,p,padicNSqrt[PadicN[r,p,padicSqrtSeedPrecision[p]]]];
padicExactSqrtFromSample[_,_,Indeterminate] := Indeterminate;
padicExactSqrtFromSample[r_,p_,sample_] := padicExactSqrtCandidate[Sqrt[r],r,p,sample];

(* The sample already carries the root valuation and branch modulus.
   Compare the rational candidate once; its negation is the other branch. *)
padicExactSqrtCandidate[root:(_Integer|_Rational),_,p_,PadicRationalN[m_,p_,e_,n_]] /;
    padicNUnitResidue[root p^(-e),p,n] == m := Padic[root,p];
padicExactSqrtCandidate[root:(_Integer|_Rational),_,p_,_PadicRationalN] := Padic[-root,p];
padicExactSqrtCandidate[_,r_,p_,_] := PadicLazy[Inactive[Power][r,1/2],p];

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
        padicLazySumBounds[s,bound,v,b d,p]
    ];
(* p^n exceeds the numerator bound: a zero residue certifies exact zero. *)
padicLazySumBounds[PadicRationalN[0,_,_,_],_,_,_,_] := {Infinity,0,1};
padicLazySumBounds[PadicRationalN[_,_,e_,_],bound_,v_,denominator_,p_] :=
    {e,Quotient[bound,p^(e-v)],denominator};

(* Evaluate to absolute precision A. A source divisible by p^A contributes
   an uncertain zero. No intermediate value goes through Normal. *)
padicLazyEvaluate[0,p_,_] := PadicRationalN[0,p,Infinity,0];
padicLazyEvaluate[r:(_Integer|_Rational),p_,absolute_] :=
    padicLazyEvaluateRational[r,p,absolute,PadicOrder[r,p]];
padicLazyEvaluateRational[_,p_,absolute_,e_] /; e >= absolute :=
    PadicRationalN[0,p,absolute,0];
padicLazyEvaluateRational[r_,p_,absolute_,e_] := PadicN[r,p,absolute-e];
padicLazyEvaluate[Inactive[Plus][a_,b_],p_,absolute_] :=
    padicNAdd[padicLazyEvaluate[a,p,absolute],padicLazyEvaluate[b,p,absolute]];
padicLazyEvaluate[Inactive[Minus][a_],p_,absolute_] :=
    padicNMulScalar[padicLazyEvaluate[a,p,absolute],-1];
padicLazyEvaluate[Inactive[Times][a_,b_],p_,absolute_] :=
    padicLazyEvaluateProduct[a,b,p,absolute,{First[padicLazyInfo[a,p]],First[padicLazyInfo[b,p]]}];
padicLazyEvaluateProduct[_,_,p_,_,{Infinity,_}|{_,Infinity}] := PadicRationalN[0,p,Infinity,0];
padicLazyEvaluateProduct[_,_,p_,absolute_,{e_,f_}] /; e+f >= absolute :=
    PadicRationalN[0,p,absolute,0];
padicLazyEvaluateProduct[a_,b_,p_,absolute_,{e_,f_}] :=
    padicNMul[padicLazyEvaluate[a,p,absolute-f],padicLazyEvaluate[b,p,absolute-e]];

(* Validate the source and power before any precision or exponent shortcut.
   The zeroth-power rule applies only after the absolute-precision cutoff. *)
padicLazyEvaluate[Inactive[Power][a_,k_Integer],p_,absolute_] :=
    padicLazyEvaluatePower[a,k,p,absolute,First[padicLazyPowerInfo[padicLazyInfo[a,p],k]]];
padicLazyEvaluatePower[_,_,p_,_,Infinity] := PadicRationalN[0,p,Infinity,0];
padicLazyEvaluatePower[_,_,p_,absolute_,v_] /; v >= absolute := PadicRationalN[0,p,absolute,0];
padicLazyEvaluatePower[_,0,p_,absolute_,_] /; absolute > 0 := PadicN[1,p,absolute];
padicLazyEvaluatePower[a_,k_,p_,absolute_,v_] :=
    padicNPower[padicLazyEvaluate[a,p,First[padicLazyInfo[a,p]]+absolute-v],k];

padicLazySnapshot[tree_,p_,n_] := padicLazyCompute[padicLazySnapshot0[tree,p,n]];
padicLazySnapshot0[tree_,p_,Automatic] :=
    padicLazySnapshot0[tree,p,padicLazySnapshotPrecision[padicLazyInfo[tree,p],p]];
padicLazySnapshotPrecision[{Infinity,_,_},_] := 1;
padicLazySnapshotPrecision[{_,a_,b_},p_] := IntegerLength[2 Max[a,b]^2,p];
padicLazySnapshot0[tree_,p_,n_Integer?Positive] :=
    padicLazySnapshotAtOrder[tree,p,n,First[padicLazyInfo[tree,p]]];
padicLazySnapshotAtOrder[_,p_,n_,Infinity] := PadicRationalN[0,p,Infinity,n];
padicLazySnapshotAtOrder[tree_,p_,n_,e_] := padicNTruncate[padicLazyEvaluate[tree,p,e+n],n];

padicLazyReconstruct[tree_,p_] :=
    padicLazyCompute[padicLazyReconstructWithInfo[tree,p,padicLazyInfo[tree,p]]];
padicLazyReconstructWithInfo[_,_,{Infinity,_,_}] := 0;
padicLazyReconstructWithInfo[tree_,p_,info_] := With[{s=padicLazySnapshot0[tree,p,Automatic]},
    padicLazyReconstructionResult[tree,p,info,s,PadicRationalApprox[s[[1]],p^s[[4]]]]];

(* Rational recipes have propagated source bounds. Root recipes additionally
   need a local-branch equality certificate. A residue fallback alone cannot
   certify rationality; failed reconstruction keeps the two outcomes distinct. *)
padicLazyReconstructionResult[tree_,p_,{v_,a_,b_},PadicRationalN[m_,p_,e_,n_],r_] /;
    Abs[Numerator[r]] <= a && Denominator[r] <= b && CoprimeQ[Denominator[r],p] &&
    Mod[Numerator[r]-m Denominator[r],p^n] == 0 :=
    padicLazyCertifiedRational[r p^e,!padicLazyHasRootQ[tree] || padicLazyRationalRootQ[tree,p,r,v]];
padicLazyReconstructionResult[tree_,_,_,_,_] /; padicLazyHasRootQ[tree] := Missing["NotRational"];
padicLazyReconstructionResult[_,p_,_,_,_] := Failure["ReconstructionFailed",<|"Base"->p|>];
padicLazyCertifiedRational[r_,True] := r;
padicLazyCertifiedRational[_,False] := Missing["NotRational"];

PadicN[s_PadicLazy] := s;
PadicN[s_PadicLazy,p_] /; !padicNParametersQ[p,1] := $Failed;
PadicN[PadicLazy[t_,q_],p_?padicNPrimeQ] /; p === q || !padicLazyHasRootQ[t] := PadicLazy[t,p];
PadicN[PadicLazy[_,q_],p_?padicNPrimeQ] := (Message[PadicN::base,q,p]; $Failed);
PadicN[s_PadicLazy,p_,n_] /; !padicNParametersQ[p,n] := $Failed;
PadicN[PadicLazy[t_,q_],p_?padicNPrimeQ,n:(Automatic|_Integer?Positive)] /;
    p === q || !padicLazyHasRootQ[t] :=
    padicLazySnapshot[t,p,n];
PadicN[PadicLazy[_,q_],p_?padicNPrimeQ,n:(Automatic|_Integer?Positive)] :=
    (Message[PadicN::base,q,p]; $Failed);
PadicLazy /: Normal[PadicLazy[t_,p_]] := padicLazyReconstruct[t,p];
Padic[s:PadicLazy[_,p_]] := padicLazyExactResult[Normal[s],p];
Padic[s_PadicLazy,p_] := padicLazyExactResult[Normal[s],p];
padicLazyExactResult[r_Missing,_] := r;
padicLazyExactResult[r_,p_] := Padic[r,p];

(* Inspection propagates failed base conversion before applying the operation. *)
padicLazyInspect[_,$Failed] := $Failed;
padicLazyInspect[op_,value_] := op[value];
PadicLazy /: PadicOrder[PadicLazy[t_,p_]] := padicLazyCompute[First[padicLazyInfo[t,p]]];
PadicLazy /: PadicOrder[s_PadicLazy,p_?padicNPrimeQ] :=
    padicLazyInspect[PadicOrder,PadicN[s,p]];
PadicLazy /: PadicAbs[s_PadicLazy] := s[[2]]^(-PadicOrder[s]);
PadicLazy /: PadicAbs[s_PadicLazy,p_?padicNPrimeQ] :=
    padicLazyInspect[p^(-#)&,PadicOrder[s,p]];
PadicLazy /: PadicCanonicalize[s_PadicLazy] := s;
PadicLazy /: PadicNormalize[s_PadicLazy] := padicLazyNormalizeAtOrder[s,PadicOrder[s]];
padicLazyNormalizeAtOrder[s_,Infinity] := s;
padicLazyNormalizeAtOrder[s:PadicLazy[_,p_],e_] := s p^(-e);

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
PadicLazy /: PadicDigits[s_PadicLazy,p_?padicNPrimeQ] :=
    padicLazyInspect[PadicDigits,PadicN[s,p]];

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
    padicLazyEvaluateSqrt[a,p,absolute,First[padicLazyInfo[a,p]]];
padicLazyEvaluateSqrt[_,p_,_,Infinity] := PadicRationalN[0,p,Infinity,0];
padicLazyEvaluateSqrt[_,p_,_,e_Integer?OddQ] := Throw[padicSqrtFailure[p],padicLazyFailure];
padicLazyEvaluateSqrt[a_,p_,absolute_,e_] :=
    With[{n=padicLazySqrtInputPrecision[p,absolute-e/2]},
        padicLazySqrtResult[padicNSqrt[padicLazyEvaluate[a,p,e+n]],p,absolute,e/2]];
padicLazySqrtInputPrecision[2,n_] := Max[3,n+1];
padicLazySqrtInputPrecision[_,n_] := Max[1,n];
padicLazySqrtResult[root:(Indeterminate|_Missing),_,_,_] := Throw[root,padicLazyFailure];
padicLazySqrtResult[_PadicRationalN,p_,absolute_,e_] /; absolute <= e :=
    PadicRationalN[0,p,absolute,0];
padicLazySqrtResult[root_,_,absolute_,e_] := padicNTruncate[root,absolute-e];

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
padicPolynomialValuationBound[f_,p_] :=
    padicPolynomialCoefficientBound[padicPolynomialNonzeroCoefficients[f],p];
padicPolynomialCoefficientBound[{_},_] := 0;
padicPolynomialCoefficientBound[c_,p_] := Max[0,PadicOrder[First[c],p]];

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
        g = padicPolynomialPowerRelation[z,v,k];
        padicPolynomialNormalize[Resultant[f,g,v]]
    ];
padicPolynomialPowerRelation[z_,v_,k_Integer?Positive] := z-v^k;
padicPolynomialPowerRelation[z_,v_,k_Integer?Negative] := z v^(-k)-1;

(* If c0 + c1*x + ... has integral coefficients and c0!=0, a nonzero
   p-adic root cannot have valuation greater than max(0,v_p(c0)). Remove
   zero-root factors first. A zero snapshot beyond this bound proves exact
   zero; otherwise it gives the exact valuation, without real radical evaluation.
   The rational-root theorem supplies bounds for any rational candidate. *)
padicLazyInfo0[t_,p_] /; padicLazyHasRootQ[t] := (
    padicLazyValidateChildren[t,p];
    With[{f=padicLazyPolynomial[t]},
        padicLazyAlgebraicInfo[t,p,f,padicPolynomialNonzeroCoefficients[f]]]
);

(* Validate children before polynomial shortcuts, including a zeroth power.
   Integer powers also reject zero to a nonpositive exponent. *)
padicLazyValidateChildren[Inactive[Power][a_,k_Integer],p_] :=
    padicLazyPowerInfo[padicLazyInfo[a,p],k];
padicLazyValidateChildren[Inactive[Power][a_,_],p_] := padicLazyInfo[a,p];
padicLazyValidateChildren[t_,p_] := Scan[padicLazyInfo[#,p]&,List@@t];

(* Reuse the stripped coefficients for both the zero test and valuation bound. *)
padicLazyAlgebraicInfo[_,_,_,{_}] := {Infinity,0,1};
padicLazyAlgebraicInfo[t_,p_,f_,c_] :=
    padicLazyAlgebraicBounds[padicLazyEvaluate[t,p,padicPolynomialCoefficientBound[c,p]+1],p,f];
padicLazyAlgebraicBounds[PadicRationalN[0,_,_,_],_,_] := {Infinity,0,1};
padicLazyAlgebraicBounds[PadicRationalN[_,_,e_,_],p_,f_] :=
    With[{unit=padicPolynomialNormalize[f /. padicPolynomialVariable -> p^e padicPolynomialVariable]},
        With[{c=padicPolynomialNonzeroCoefficients[unit]}, {e,Abs[First[c]],Abs[Last[c]]}]];

(* A candidate must be a polynomial root AND match this particular local
   branch. A shifted annihilator bounds every nonzero candidate difference,
   certifying equality after enough matching modular digits. *)
padicLazyRationalRootQ[t_,p_,r_,e_] :=
    padicLazyRationalRootPolynomialQ[t,p,r,padicPolynomialNormalize[padicLazyPolynomial[t] /.
        padicPolynomialVariable -> p^e padicPolynomialVariable]];
padicLazyRationalRootPolynomialQ[_,_,r_,f_] /; (f /. padicPolynomialVariable -> r) =!= 0 := False;
padicLazyRationalRootPolynomialQ[t_,p_,r_,f_] :=
    With[{shift=padicPolynomialNormalize[f /. padicPolynomialVariable -> padicPolynomialVariable+r]},
        padicLazyRationalRootBranchQ[t,p,r,padicPolynomialNonzeroCoefficients[shift]]];
padicLazyRationalRootBranchQ[_,_,_,{_}] := True;
padicLazyRationalRootBranchQ[t_,p_,r_,c_] :=
    With[{s=padicLazySnapshot0[t,p,padicPolynomialCoefficientBound[c,p]+1]},
        Mod[Numerator[r]-s[[1]] Denominator[r],p^s[[4]]] == 0];

(******************* P-adic Visualization ********************)

(* A tree with E edges has E+1 vertices. Both public calling forms use
   the same budget, checked before allocating tuples or constructing a graph. *)
padicTreeMaxEdges = 3000;
maxSafeDepth[p_, maxEdges_:padicTreeMaxEdges] := Module[{depth=0,edges=0,next=p},
    While[next <= maxEdges, depth++; edges=next; next=p (edges+1)];
    depth
];
padicTreeDepth[p_,depth_] := padicTreeBoundDepth[p,depth,maxSafeDepth[p,padicTreeMaxEdges]];
padicTreeBoundDepth[p_,depth_,limit_] /; depth > limit :=
    (Message[PadicDigitTree::depth,depth,limit,p,padicTreeMaxEdges]; limit);
padicTreeBoundDepth[_,depth_,_] := depth;

(* Tuples[...,0] already supplies the root. Each nonroot vertex has one
   parent, so edges can be derived without generating the vertices again. *)
padicVertices[p_,depth_] := Flatten[Table[Tuples[Range[0,p-1],n],{n,0,depth}],1];
padicEdges[vertices_List] := (UndirectedEdge[Most[#],#]& /@ Rest[vertices]);
edgeDigit[UndirectedEdge[a_,b_]] /; Length[a] > Length[b] := Last[a];
edgeDigit[UndirectedEdge[_,b_]] := Last[b];

digitColorMap[_,custom_Association] := custom;
digitColorMap[p_,custom_List] /; Length[custom] >= p := AssociationThread[Range[0,p-1],Take[custom,p]];
digitColorMap[p_,_] := AssociationThread[Range[0,p-1],Table[Hue[d/p,0.85,0.92],{d,0,p-1}]];

(* Rays run root-outward through normalized unit digits. Finite snapshots
   retain the existing reconstruction-based preview; it is not a certified
   continuation of their unknown source. Lazy rays request digits directly. *)
padicRationalToRay[PadicRational[m_,p_,_,n_,k_],depth_] :=
    padicExtendRay[Reverse[IntegerDigits[m,p,n]],k,depth];
padicExtendRay[raw_,0,depth_] := PadRight[raw,depth,0];
padicExtendRay[raw_,k_,depth_] := PadRight[raw,depth,Take[raw,-k]];
padicRationalToRay[s_PadicRationalN,depth_] := resolveRay[Padic[s],depth];
padicRationalToRay[s_PadicLazy,depth_] := padicTreeSnapshotRay[PadicN[s,s[[2]],depth],depth];
padicTreeSnapshotRay[PadicRationalN[m_,p_,_,_],depth_] := Reverse[IntegerDigits[m,p,depth]];
padicTreeSnapshotRay[_,_] := $Failed;

normalizeRays[None] := {};
normalizeRays[{}] := {};
normalizeRays[r:{__Integer}] := {r};
normalizeRays[r_List] := r;
normalizeRays[r_] := {r};
resolveRay[digits_List,_] := digits;
resolveRay[s:(_PadicRational|_PadicRationalN|_PadicLazy),depth_] := padicRationalToRay[s,depth];
resolveRay[_,_] := $Failed;

reconcileRays[rays_,p_] := reconcileRay[#,p]& /@ rays;
reconcileRay[s:PadicRational[_,p_,___],p_] := s;
reconcileRay[s:PadicRationalN[_,p_,___],p_] := s;
reconcileRay[s:(_PadicRational|_PadicRationalN),p_] := Padic[Normal[s],p];
reconcileRay[s_PadicLazy,p_] := PadicN[s,p];
reconcileRay[s_,_] := s;

padicTreeRaysQ[rays_List,p_] := AllTrue[rays,
    Function[ray,ListQ[ray] && AllTrue[ray,IntegerQ[#] && 0 <= # < p&]]];
padicTreeCheckedRays[rays_,p_] /; padicTreeRaysQ[rays,p] := rays;
padicTreeCheckedRays[_,p_] := (Message[PadicDigitTree::rays,p-1]; Throw[$Failed,padicTreeFailure]);
singleRayData[digits_List,depth_] := With[
    {vertices=Table[Take[digits,k],{k,0,Min[depth,Length[digits]]}]},
    {vertices,UndirectedEdge @@@ Partition[vertices,2,1]}];

(* Overlay geometry is bounded by the existing graph, including when a
   requested sector depth is much larger than the tree. List vertices are
   association keys, so coordinate lookups must use Key explicitly. *)
padicTreeCoordinates[graph_] := AssociationThread[VertexList[graph],GraphEmbedding[graph]];
padicSectorDepth[n_Integer?NonNegative,depth_] := Min[n,depth];
padicSectorDepth[_,_] := 0;
buildSectors[graph_,p_,colors_,opacity_,maxDepth_] := Module[{coords,root,radius,parents,depth},
    coords=padicTreeCoordinates[graph]; root=coords[{}];
    radius=1.02 Max[Norm[#-root]& /@ Values[coords]];
    depth=padicSectorDepth[maxDepth,Max[Length /@ VertexList[graph]]];
    parents=Select[VertexList[graph],Length[#] < depth&];
    Flatten[padicSectorChildren[#,p,coords,root,radius,colors,opacity]& /@ parents,1]
];
padicSectorChildren[parent_,p_,coords_,root_,radius_,colors_,opacity_] :=
    With[{children=Append[parent,#]& /@ Range[0,p-1]},
        padicSectorPrimitives[Lookup[coords,Key /@ children],Last /@ children,
            root,radius,colors,opacity/(Length[parent]+1)]];
padicSectorPrimitives[points_,_,_,_,_,_] /; !FreeQ[points,_Missing] := {};
padicSectorPrimitives[points_,digits_,root_,radius_,colors_,opacity_] :=
    Module[{angles,order,sorted,extended},
        angles=ArcTan @@ (#-root)& /@ points; order=Ordering[angles]; sorted=angles[[order]];
        extended=Join[{Last[sorted]-2 Pi},sorted,{First[sorted]+2 Pi}];
        Table[{Directive[colors[digits[[order[[i]]]]],Opacity[opacity]],
            Disk[root,radius,{(extended[[i]]+extended[[i+1]])/2,
                (extended[[i+1]]+extended[[i+2]])/2}]},{i,Length[digits]}]
    ];

(* Project deepest leaves onto one dust ring, colored by their last digit.
   Highlight valid nonempty rays by their first digit. *)
padicBoundaryPoint[point_,root_,radius_] := With[{angle=ArcTan @@ (point-root)},
    root+radius {Cos[angle],Sin[angle]}];
padicBoundaryRay[{},_,_,_,_,_,_] := {};
padicBoundaryRay[ray_,depth_,coords_,root_,radius_,colors_,size_] :=
    padicBoundaryHighlight[Lookup[coords,Key[Take[ray,Min[Length[ray],depth]]],Missing["Vertex"]],
        First[ray],root,radius,colors,size];
padicBoundaryHighlight[_Missing,_,_,_,_,_] := {};
padicBoundaryHighlight[coord_,digit_,root_,radius_,colors_,size_] :=
    With[{point=Point[padicBoundaryPoint[coord,root,radius]]},
        {White,AbsolutePointSize[size+5],point,colors[digit],AbsolutePointSize[size+2],point}];
buildCantorBoundary[graph_,p_,colors_,dustRadius_,pointSize_,rays_] :=
    Module[{coords,root,radius,depth,leaves,guide,dots,highlights},
        coords=padicTreeCoordinates[graph]; root=coords[{}];
        radius=dustRadius Max[Norm[#-root]& /@ Values[coords]];
        depth=Max[Length /@ VertexList[graph]];
        leaves=Select[VertexList[graph],Length[#] == depth&];
        guide={Directive[GrayLevel[0.45],Opacity[0.15],AbsoluteThickness[0.5]],Circle[root,radius]};
        dots=({colors[Last[#]],AbsolutePointSize[pointSize],
            Point[padicBoundaryPoint[coords[#],root,radius]]}& /@ leaves);
        highlights=padicBoundaryRay[#,depth,coords,root,radius,colors,pointSize]& /@ rays;
        Join[{guide},dots,highlights]
    ];

padicTreeLayout["Tree"|"TopDown"] :=
    {"LayeredDigraphEmbedding","RootVertex"->{},"Orientation"->Top};
padicTreeLayout[_] := {"HyperbolicRadialEmbedding","RootVertex"->{}};
padicTreeVertexText[{}] := "\[Bullet]";
padicTreeVertexText[v_] := StringJoin[ToString /@ v];
padicTreeVertexLabel[v_,style_] := v -> Placed[Style[padicTreeVertexText[v],style],Center];
padicTreeVertexLabels["FirstLayer",p_,_,_,style_] :=
    padicTreeVertexLabel[#,style]& /@ Join[{{}},List /@ Range[0,p-1]];
padicTreeVertexLabels["Ray",_,_,rays_,style_] := padicTreeVertexLabel[#,style]& /@ rays;
padicTreeVertexLabels["All",_,vertices_,_,style_] := padicTreeVertexLabel[#,style]& /@ vertices;
padicTreeVertexLabels[_,_,_,_,_] := None;
padicTreeLabelEdges["FirstLevel",edges_,_] := Select[edges,MemberQ[List@@#,{}]&];
padicTreeLabelEdges["Ray",_,rays_] := rays;
padicTreeLabelEdges["All",edges_,_] := edges;
padicTreeLabelEdges[_,_,_] := {};
padicTreeEdgeLabels[{},_,_] := None;
padicTreeEdgeLabels[edges_,style_,colors_] :=
    (# -> Placed[Framed[Style[ToString[edgeDigit[#]],style,colors[edgeDigit[#]]],
        Background->RGBColor[.07,.08,.10,.72],FrameStyle->None,RoundingRadius->3,
        FrameMargins->Tiny],.35])& /@ edges;
padicTreeSectorOverlay[True,"Hyperbolic",graph_,p_,colors_,opacity_,depth_] :=
    buildSectors[graph,p,colors,opacity,depth];
padicTreeSectorOverlay[_,_,_,_,_,_,_] := {};
padicTreeBoundaryOverlay[True,"Hyperbolic",graph_,p_,colors_,radius_,size_,rays_] :=
    buildCantorBoundary[graph,p,colors,radius,size,rays];
padicTreeBoundaryOverlay[_,_,_,_,_,_,_,_] := {};
padicTreeWithOverlays[graph_,{}] := graph;
padicTreeWithOverlays[graph_,overlays_] := Show[Graphics[overlays],graph];

Options[PadicDigitTree] = {
    RayDigits->None, Layout->"Hyperbolic", VertexLabelMode->"None", EdgeLabelMode->"Ray",
    DigitColors->Automatic, SectorBackground->False, SectorBackgroundDepth->1,
    SectorOpacity->0.07, CantorBoundary->False, CantorDustRadius->1.12,
    CantorPointSize->2, ImageSize->900, Background->None
};

PadicDigitTree::base = "The tree base `1` must be an integer greater than 1.";
PadicDigitTree::colors = "No tree graph is shown for base `1`: digit trees support at most 7 colors (bases 2 through 7).";
PadicDigitTree::depth = "Depth `1` in base `3` exceeds the `4`-edge tree limit; using depth `2` instead.";
PadicDigitTree::deptharg = "The tree depth `1` must be a positive integer.";
PadicDigitTree::rays = "RayDigits must resolve to lists of integer digits from 0 through `1`. No tree graph is shown for an invalid or unavailable ray.";

(* Diagnostic rules and successful rules are disjoint: no specific shortcut
   can bypass the base or depth restrictions. Composite branching bases remain
   available for explicit digit paths; p-adic objects require prime bases. *)
PadicDigitTree[p_,opts:OptionsPattern[]] /; !IntegerQ[p] || p <= 1 :=
    (Message[PadicDigitTree::base,p]; $Failed);
PadicDigitTree[p_Integer,opts:OptionsPattern[]] /; p > 7 :=
    (Message[PadicDigitTree::colors,p]; $Failed);
PadicDigitTree[p_Integer,opts:OptionsPattern[]] /; 2 <= p <= 7 :=
    PadicDigitTree[p,maxSafeDepth[p,padicTreeMaxEdges],opts];
PadicDigitTree[p_,depth_,opts:OptionsPattern[]] /; !IntegerQ[p] || p <= 1 :=
    (Message[PadicDigitTree::base,p]; $Failed);
PadicDigitTree[p_Integer,depth_,opts:OptionsPattern[]] /; p > 7 :=
    (Message[PadicDigitTree::colors,p]; $Failed);
PadicDigitTree[p_Integer,depth_,opts:OptionsPattern[]] /;
    2 <= p <= 7 && (!IntegerQ[depth] || depth <= 0) :=
    (Message[PadicDigitTree::deptharg,depth]; $Failed);
PadicDigitTree[p_Integer,depth_Integer?Positive,opts:OptionsPattern[]] /; 2 <= p <= 7 :=
    padicTreeBuild[p,padicTreeDepth[p,depth],opts];

Options[padicTreeBuild] = Options[PadicDigitTree];
padicTreeBuild[p_,d_,OptionsPattern[]] := Catch[Module[
    {verts,edges,rays,rayData,rayVerts,rayEdges,normalV,normalE,colors,layout,
     graph,vLbl,eLbl,overlays},
    verts=padicVertices[p,d]; edges=padicEdges[verts];
    colors=digitColorMap[p,OptionValue[DigitColors]]; layout=OptionValue[Layout];
    rays=resolveRay[#,d]& /@ reconcileRays[normalizeRays[OptionValue[RayDigits]],p];
    rays=padicTreeCheckedRays[rays,p];
    rayData=singleRayData[#,d]& /@ rays;
    rayVerts=DeleteDuplicates[Join@@(First /@ rayData)];
    rayEdges=DeleteDuplicates[Join@@(Last /@ rayData)];
    normalV=Complement[verts,rayVerts,{{}}]; normalE=Complement[edges,rayEdges];
    vLbl=padicTreeVertexLabels[OptionValue[VertexLabelMode],p,verts,rayVerts,Directive[White,11,Bold]];
    eLbl=padicTreeEdgeLabels[padicTreeLabelEdges[OptionValue[EdgeLabelMode],edges,rayEdges],
        Directive[White,12,Bold],colors];
    graph=TreeGraph[verts,edges,GraphLayout->padicTreeLayout[layout],VertexLabels->vLbl,EdgeLabels->eLbl,
        VertexSize->Join[{{}->.22},Thread[normalV->.018],Thread[Complement[rayVerts,{{}}]->.10]],
        VertexStyle->Join[{{}->RGBColor[.45,.70,1.]},Thread[normalV->GrayLevel[.72]],
            Thread[Complement[rayVerts,{{}}]->RGBColor[.96,.97,1.]]],
        EdgeStyle->Join[(# -> Directive[colors[edgeDigit[#]],Opacity[.28],AbsoluteThickness[1]])& /@ normalE,
            (# -> Directive[colors[edgeDigit[#]],AbsoluteThickness[4.2]])& /@ rayEdges],
        ImageSize->OptionValue[ImageSize],Background->OptionValue[Background],
        ImagePadding->25,PlotRangePadding->Scaled[.03]];
    overlays=Join[
        padicTreeSectorOverlay[OptionValue[SectorBackground],layout,graph,p,colors,
            OptionValue[SectorOpacity],OptionValue[SectorBackgroundDepth]],
        padicTreeBoundaryOverlay[OptionValue[CantorBoundary],layout,graph,p,colors,
            OptionValue[CantorDustRadius],OptionValue[CantorPointSize],rays]];
    padicTreeWithOverlays[graph,overlays]
],padicTreeFailure];

End[] (* End `Private` *)

EndPackage[]
