(* ::Package:: *)

BeginPackage["PadicNumbers`"]

(* Declare package's public symbols here. *)

PadicOrder
PadicAbs
PadicNormalize
PadicSignature
PadicCanonicalize

Padic
PadicN
PadicRational
PadicRationalN
PadicDigits

PadicDigitTree

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
PadicRational /: PadicOrder[PadicRational[_,p_,e_,___]] := e
PadicRational /: PadicOrder[PadicRational[_,p_,e_,___], p_] := e
PadicRational /: PadicAbs[PadicRational[0,p_,___]] := 0
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

PadicRationalN /: PadicOrder[PadicRationalN[0, p_, ___]] := Infinity
PadicRationalN /: PadicOrder[PadicRationalN[_,_,e_,_]] := e
PadicRationalN /: PadicOrder[PadicRationalN[_,p_,e_,_], p_] := e
PadicRationalN /: PadicAbs[PadicRationalN[0,p_,___]] := 0
PadicRationalN /: PadicAbs[PadicRationalN[_,p_,e_,_]] := p^(-e)
PadicRationalN /: PadicAbs[PadicRationalN[_,p_,e_,_], p_] := p^(-e)
PadicRationalN /: PadicNormalize[PadicRationalN[m_,p_,e_,N_]] :=
    PadicRationalN[m,p,0,N]

(* PadicCanonicalize is a no-op for lossy: no period to reduce *)
PadicRationalN /: PadicCanonicalize[s_PadicRationalN] := s

(* Helper functions to find the p-adic periodicity for rational numbers *)

(* use extended Euclidean algorithm to solve Bezout's identity: x d + y p == 1 *)
ExpandToPowerOf[p_Integer/;p>1] := Function[{r},
    ({#[[2]] r, 0}+QuotientRemainder[#[[1]] Numerator[r],p])&[
        ExtendedGCD[Denominator[r],p][[2]]]]

PadicSignature[0, p_Integer/;p>1] := {0, 0}
PadicSignature[n_Integer?Positive,p_Integer/;p>1] := {IntegerLength[n, p], 0}
PadicSignature[n_Integer?Negative,p_Integer/;p>1] := {IntegerLength[-n, p] + 1, 1}
PadicSignature[r_Rational,p_Integer/;p>1] :=
    With[{rr=PadicNormalize[r,p]},
        With[{trail=NestWhileList[First@*ExpandToPowerOf[p], rr, UnsameQ[##] &, All]},
            With[{s=FirstPosition[Most[trail], Last[trail]][[1]]},
                {Length[trail]-1, Length[trail]-s}]]]

(******************** Negation of P-adics ********************)

PadicRational /: Minus[s:PadicRational[0,___]] := s
PadicRational /: Minus[PadicRational[1,p_,e_,1,0]] :=
    PadicRational[p-1,p,e,1,1]
PadicRational /: Minus[PadicRational[m_,p_,e_,n_,0]] :=
    PadicRational[Mod[-m,p^(n+1)],p,e,n+1,1]
(* reduction to non-periodic (positive integer) expansion *)
PadicRational /: Minus[PadicRational[m_,p_,e_,n_,1]] :=
    PadicRational[Mod[-m,p^(n-1)],p,e,n-1,0] /; n>1 && Quotient[m,p^(n-1)] == p-1
(* a really simple roundtrip otherwise *)
PadicRational /: Minus[s_PadicRational] := Padic[-Normal[s], s[[2]]]

(******************* Conversion to P-adics *******************)

(* trivial *)
Padic[0,p_Integer/;p>1] := PadicRational[0,p,0,0,0]
(* case 1: negative integers *)
Padic[n_Integer/;n<0,p_Integer/;p>1] := Minus[Padic[-n,p]]
(* all other cases combined *)
Padic[r:(_Integer?Positive | _Rational),p_Integer/;p>1] :=
    With[{e=PadicOrder[r,p], rr=PadicNormalize[r,p]},
        Replace[PadicSignature[rr, p], {n_, k_} :>
            PadicRational[
                Mod[Numerator[rr] PowerMod[Denominator[rr], -1, p^n], p^n],
                p, e, n, k]]]
(* in case we change the basis *)
PadicRational /: Padic[(s:PadicRational[_,p1_,__]),p2_Integer/;p2>1] :=
    Padic[Normal[s],p2] /; p1 != p2

SetAttributes[Padic,Listable]

Padic[e_Plus,p_Integer,n_Integer] := Padic[#,p,n]& /@ e
Padic[e_Times,p_Integer,n_Integer] := Padic[#,p,n]& /@ e
Padic[x_^m_,p_Integer,n_Integer] := Padic[x,p,n]^m

(* recover from PadicRationalN via Normal roundtrip *)
Padic[s_PadicRationalN] := Padic[Normal[s], s[[2]]]
Padic[s_PadicRationalN, p_Integer/;p>1] := Padic[Normal[s], p]

(* drop Padic when applied to an atom *)
Padic[e_,___] := e /; AtomQ[e]

(*********** Conversion to Integers and Rationals ************)

PadicRational /: Normal[PadicRational[m_,p_, e_,_,0]] := m p^e
PadicRational /: Normal[PadicRational[m_,p_,e_,n_,k_]] :=
    (p^e QuotientRemainder[m,p^#] . {-p^#/(p^k-1),1})&[n-k]

(******************* Conversion to digits ********************)

PadicDigits[s_,p_Integer/;p>0] := PadicDigits[Padic[s,p]]
PadicDigits[PadicRational[0,___]] := {0}
PadicDigits[PadicRational[m_,p_,e_Integer/;e<=0,n_Integer,___]] :=
    IntegerDigits@@{m,p,n}
PadicDigits[s:PadicRational[_,_,e_Integer/;e>0,___]] :=
    Join[PadicDigits[ReplacePart[s,3->0]],Table[0,Abs[e]]]

(* PadicDigits for lossy PadicRationalN \[LongDash] treat as non-periodic *)
PadicDigits[PadicRationalN[0,___]] := {0}
PadicDigits[PadicRationalN[m_,p_,e_Integer/;e<=0,n_Integer]] :=
    IntegerDigits@@{m,p,n}
PadicDigits[s:PadicRationalN[_,_,e_Integer/;e>0,_]] :=
    Join[PadicDigits[ReplacePart[s,3->0]], Table[0,Abs[e]]]

(********************** P-adic formatting ********************)

(*positive scaled non-periodic expansions*)
PadicRational /: Format[s:PadicRational[_,p_,e_/;0<=e<=4,_,0]] :=
    Subscript[Row[PadicDigits[s]," "],p]
PadicRational /: Format[s:PadicRational[_,p_,e_/;-4<=e<0,n_,0]] :=
  Subscript[Row[Insert[Join[Table[0, -(n+e)], PadicDigits[s]],".", e-1]," "],p]

padicPeriodicColor= RGBColor[0.7,0.5,0.3];
(* purely periodic *)
PadicRational /: Format[s:PadicRational[_,p_,0,k_,k_/;k>0]]:=
    Subscript[Style[OverBar[Row[#1," "]],padicPeriodicColor],p]&[Take[PadicDigits[s],k]]
(* eventually periodic *)
PadicRational /: Format[s:PadicRational[_,p_,0,n_,k_/;k>0]]:=
    Subscript[Row[{Style[OverBar[Row[#1," "]],padicPeriodicColor],Row[#2," "]}," "],p]&@@TakeDrop[PadicDigits[s],k]/;n>k
(* simply add a scale factor here *)
PadicRational /: Format[s:PadicRational[_,p_,e_Integer/;e!=0,_,_]]:=
    Row[{Format[ReplacePart[s,3->0]],Superscript[p,e]},"\[Times]"]

(* PadicRationalN formatting: shown with ~ to indicate lossy *)
PadicRationalN /: Format[s:PadicRationalN[_,p_,e_/;-4<=e<0,n_]]:=
    Subscript[Row[{"~",Row[Insert[Join[Table[0,-(n+e)],PadicDigits[s]],".",e-1]," "]}],p]
PadicRationalN /: Format[s:PadicRationalN[_,p_,e_/;0<=e<=4,_]]:=
    Subscript[Row[{"~",Row[PadicDigits[s]," "]}],p]
PadicRationalN /: Format[s:PadicRationalN[_,p_,e_Integer/;e!=0,_]]:=
    Row[{Format[ReplacePart[s,3->0]],Superscript[p,e]},"\[Times]"]

(******************** P-adic arithmetic **********************)

(* Canonicalization: remove non-periodic digits that are
   continuations of the periodic cycle, minimizing the significand *)
PadicCanonicalize[s : PadicRational[m_, p_, e_, n_, k_]] := s /; n <= k
PadicCanonicalize[PadicRational[m_, p_, e_, n_, k_]] :=
    With[{j = n - k},
        If[Mod[Quotient[m, p^(j - 1)], p] == Mod[Quotient[m, p^(n - 1)], p],
            PadicCanonicalize[PadicRational[
                Quotient[m, p^j] * p^(j - 1) + Mod[m, p^(j - 1)], p, e, n - 1, k]],
            PadicRational[m, p, e, n, k]]]

PadicRational /: PadicRational[0,p,__] * (b_PadicRational|b_Integer|b_Rational) :=
    PadicRational[0,p,0,0,0]
PadicRational /: PadicRational[a_,p_,e1_,n1_,k1_] * PadicRational[b_,p_,e2_,n2_,0] :=
    PadicCanonicalize[PadicRational[Mod[a*b,p^#1],p,e1+e2,#1,#2]&@@{n1+n2,k1}]

(* the round trip is the safest way for now *)
PadicRational /: (a : PadicRational[_, p_, __]) + (b_PadicRational) :=
    Padic[Normal[a] + Normal[b], p]
PadicRational /: (a : PadicRational[_, p_, __]) * (b_PadicRational) :=
    Padic[Normal[a] * Normal[b], p]
PadicRational /: Power[a : PadicRational[_, p_, 0, n_, 0], -1] :=
    Padic[1/Normal[a], p]
PadicRational /: Power[a_PadicRational, -1] :=
    Padic[1/Normal[a], a[[2]]]

(* Mixed arithmetic with integers/rationals *)
PadicRational /: a_PadicRational * (-1) := Minus[a]
PadicRational /: (a : PadicRational[_, p_, __]) + (b_Integer | b_Rational) :=
    Padic[Normal[a] + b, p]
PadicRational /: (a : PadicRational[_, p_, __]) * (b_Integer | b_Rational) :=
    Padic[Normal[a] * b, p]

(****************** P-adic lossy precision *******************)

(* converting to a lossy representation *)
PadicRational /: PadicN[PadicRational[m_,p_,e_,N_,k_]] :=
    PadicRationalN[m,p,e,N]
PadicN[r_Integer|r_Rational, p_Integer/;p>1] := PadicN[r,p,8]
PadicN[n_Integer, p_Integer/;p>1, N_Integer/;N>0] :=
    PadicRationalN[Mod[#1,p^N],p,#2,N]&[PadicNormalize[n,p], PadicOrder[n,p]]
PadicN[r_Rational, p_Integer/;p>1, N_Integer/;N>0] :=
    PadicRationalN[Mod[Numerator[#1] PowerMod[Denominator[#1],-1,p^N],p^N],p,#2,N]&[
        PadicNormalize[r,p], PadicOrder[r,p]]

(* rational reconstruction via RATCONVERT *)
PadicRationalApprox[m_, pN_] :=
    If[Abs[#[[2]]] < Sqrt[pN/2], #[[1]]/#[[2]], m]&[
        NestWhile[
            Function[{v,w}, {w, v - Floor[v[[1]]/w[[1]]] w}] @@ #&,
            {{pN, 0}, {m, 1}},
            (#[[2,1]] > Sqrt[pN/2])&
        ][[2]]]

(* converting back to Integer or Rational *)
PadicRationalN /: Normal[PadicRationalN[m_,p_,e_,N_]] :=
    PadicRationalApprox[m, p^N] p^e

(* utility functions *)
PadicRationalN /: PadicOrder[PadicRationalN[_,_,e_,_]] := e
PadicRationalN /: Minus[PadicRationalN[m_,p_,e_,N_]] :=
    PadicRationalN[Mod[-m, p^N], p, e, N]

PadicN[e_Plus,p_Integer,N_Integer] := PadicN[#,p,N]&/@e
PadicN[e_Times,p_Integer,N_Integer] := PadicN[#,p,N]&/@e
PadicN[x_^n_,p_Integer,N_Integer] := PadicN[x,p,N]^n

SetAttributes[PadicN,Listable]
PadicN[e_,__]:=e/;AtomQ[e]

(**************** P-adic N lossy arithmetic ******************)

(* lossy addition *)
PadicRationalN/:(x:PadicRationalN[a_,p_,e_,N_])+(y:PadicRationalN[b_,p_,e_,N_]):=
    Block[{sum=a+b,k,n},
        k=PadicOrder[sum,p];
        n=N-k;
        PadicRationalN[Mod[sum/p^k,p^n],p,e+k,n]]

(* lossy efficient multiplication *)
PadicRationalN /: (x:PadicRationalN[a_,p_,e1_,N1_]) * (y:PadicRationalN[b_,p_,e2_,N2_]) :=
    Block[{prod=a*b,k,n},
        k=PadicOrder[prod,p];
        n=Min[N1,N2];
        PadicRationalN[Mod[prod/p^k,p^n],p,e1+e2+k,n]]

(* P-adic inversion via Hensel lifting \[LongDash] for units (e=0, non-periodic) *)
PadicRational /: Power[PadicRational[m_,p_,0,n_,0],-1] :=
    Block[{y,target=n},
        y=PowerMod[m,-1,p];
        Do[y=Mod[y*(2-m*y),p^Min[2^i,target]],{i,1,Ceiling[Log2[target]]}];
        PadicRational[Mod[y,p^n],p,0,n,0]]

(* General case: factor out p^e *)
PadicRational /: Power[PadicRational[m_,p_,e_,n_,k_],-1] :=
    Power[PadicRational[m,p,0,n,k],-1] /.
        PadicRational[m2_,p,0,n2_,k2_] :> PadicRational[m2,p,-e,n2,k2]

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

normalizeRays[None] := {}
normalizeRays[pr_PadicRational] := {pr}
normalizeRays[prn_PadicRationalN] := {prn}
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
PadicDigitTree[p_Integer?Positive, opts : OptionsPattern[]] :=
    PadicDigitTree[p, maxSafeDepth[p], opts]

(* Calling pattern 2: full explicit *)
PadicDigitTree[p_Integer?Positive, depth_Integer?Positive, opts : OptionsPattern[]] :=
Module[
    {d, verts, edges, rays, rayDataList,
     allRayVerts, allRayEdges,
     normalV, normalE, colors, layout, graphLayout,
     vLbl, eLbl, labelStyle, edgeLblStyle,
     graph, overlays = {}, maxEdges = 10000},

    (* safeguard: clamp depth so total edges ~ p*(p^d - 1)/(p-1) < maxEdges *)
    d = depth;
    While[d > 1 && p (p^d - 1) / (p - 1) > maxEdges, d--];
    If[d < depth,
        Print[Style[
            StringForm["PadicDigitTree: depth clamped from `` to `` (`` would produce >10k edges)",
                depth, d, p], Italic, Gray]]];

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
