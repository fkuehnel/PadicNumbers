(* ::Package:: *)

BeginPackage["PadicNumbers`"]

(* Declare package's public symbols here. *)

PadicOrder
PadicAbs
PadicNormalize
PadicSignature
PadicCanonicalize

Padic
PadicRational
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

(* we don't require p as a second argument when doing p-adic 
   order or value of a p-adic number. *)

PadicRational /: PadicOrder[PadicRational[0,p_,___]] := Infinity
PadicRational /: PadicOrder[PadicRational[_,p_,e_,___]] := e
PadicRational /: PadicOrder[PadicRational[_,p_,e_,___], p_] := e
PadicRational /: PadicAbs[PadicRational[0,p_,___]] := 0
PadicRational /: PadicAbs[PadicRational[_,p_,e_,___]] := p^(-e)
PadicRational /: PadicAbs[PadicRational[_,p_,e_,___], p_] := p^(-e)
PadicRational /: PadicNormalize[PadicRational[m_, p_, e_, n_, k_]] := 
  PadicRational[m, p, 0, n, k]

(* We also can find PadicOrder and PadicValue regarding to 
   another base. *)
PadicRational /: PadicOrder[s:PadicRational[_,p1_,e_,___],
    p2_Integer/;p2>1] := PadicOrder[s//Normal,p2] /; p1 != p2
PadicRational /: PadicAbs[s:PadicRational[_,p1_,e_,___],
	p2_Integer/;p2>1] := PadicAbs[s//Normal,p2] /; p1 != p2

(* Helper functions to find the p-adic periodicity for rational numbers *)

(* use extended Euclidian algorithm to solve B\[EAcute]zouts identity: x d + y p == 1 *)
ExpandToPowerOf[p_Integer/;p>1] := Function[{r},
    ({#[[2]] r, 0}+QuotientRemainder[#[[1]] Numerator[r],p])&[
        ExtendedGCD[Denominator[r],p][[2]]]]

PadicSignature[0, p_Integer /; p > 1] := {0, 0}
PadicSignature[n_Integer?Positive,p_Integer/;p>1] := {IntegerLength[Abs[n], p], 0}
PadicSignature[n_Integer?Negative, p_Integer /; p > 1] := {IntegerLength[-n, p] + 1, 1}
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
    PadicRational[Mod[-m,p^(n-1)],p,e,n-1,0] /; Quotient[m,p^(n-1)] == p-1
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

(* drop padic when applied to an atom *)
Padic[e_,___] := e /; AtomQ[e]

(*********** Conversion to Integers and Rationals ************)

PadicRational /: Normal[PadicRational[m_,p_, e_,_,0]] := m p^e
PadicRational /: Normal[PadicRational[m_,p_,e_,n_,k_]] :=
	(p^e QuotientRemainder[m,p^#] . {-p^#/(p^k-1),1})&[n-k]

(******************* Conversion to digits ********************)

PadicDigits[s_,p_Integer/;p>0]:=PadicDigits[Padic[s,p]]
PadicDigits[PadicRational[0,___]]:={0}
PadicDigits[PadicRational[m_,p_,e_Integer/;e<=0,N_Integer,___]]:=
	IntegerDigits@@{m,p,N}
PadicDigits[s:PadicRational[_,_,e_Integer/;e>0,___]]:=
	Join[PadicDigits[ReplacePart[s,3->0]],Table[0,Abs[e]]]

(********************** P-adic formatting ********************)

(*positive scaled non-periodic expansions*)
PadicRational/:Format[s:PadicRational[_,p_,e_/;0<=e<=4,_,0]]:=
	Subscript[Row[PadicDigits[s]," "],p]
(*negative scaled non-periodic expansions*)
PadicRational/:Format[s:PadicRational[_,p_,e_/;-4<=e<0,n_,0]]:=
	Subscript[Row[Insert[Join[Table[0,-(n+e)],PadicDigits[s]],".",e-1]," "],p]
padicPeriodicColor=RGBColor[0.7,0.5,0.3];
(*purely periodic*)
PadicRational/:Format[s:PadicRational[_,p_,0,k_,k_/;k>0]]:=
	Subscript[Style[OverBar[Row[#1," "]],padicPeriodicColor],p]&[Take[PadicDigits[s],k]]
(*eventually periodic*)
PadicRational/:Format[s:PadicRational[_,p_,0,n_,k_/;k>0]]:=
	Subscript[Row[{Style[OverBar[Row[#1," "]],padicPeriodicColor],Row[#2," "]}," "],p]&@@TakeDrop[PadicDigits[s],k]/;n>k
(*simply add a scale factor here*)
PadicRational/:Format[s:PadicRational[_,p_,e_Integer/;e!=0,_,_]]:=
	Row[{Format[ReplacePart[s,3->0]],Superscript[p,e]},"\[Times]"]

(******************** P-adic arithmetic **********************)

(* P-adic multiplication optimizations *)

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
  Which[
    AssociationQ[custom], custom,
    ListQ[custom] && Length[custom] >= p,
      AssociationThread[Range[0, p - 1], Take[custom, p]],
    p == 3,
      <|0 -> RGBColor[.92, .22, .22],
        1 -> RGBColor[.15, .78, .30],
        2 -> RGBColor[.18, .48, 1.]|>,
    True,
      AssociationThread[Range[0, p - 1],
        ColorData["BrightBands"] /@
          Rescale[Range[0, p - 1], {0, Max[1, p - 1]}, {.08, .92}]]
  ];

(* \[HorizontalLine]\[HorizontalLine] Recursive sector builder \[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine]\[HorizontalLine] *)
(* Uses an Association for robust coordinate lookup. *)
(* At each level k, subdivides each parent's angular *)
(* range among p children.  Opacity decays with k.   *)
(* In the Poincar\[EAcute] disk, geodesics through the       *)
(* center are Euclidean diameters, so angular wedges  *)
(* from the root are genuine hyperbolic sectors.      *)

buildSectors[graph_, p_, colors_, baseOpacity_, maxDepth_] :=
  Module[{coords, rootPos, r, primitives = {},
          parents, children, childCoords, childAngles,
          order, sortedAngles, sortedDigits, mids},

    (* Association lookup: vertex -> {x,y} *)
    coords  = AssociationThread[VertexList[graph], GraphEmbedding[graph]];
    rootPos = coords[{}];
    r = 1.02 Max[Norm[# - rootPos] & /@ Values[coords]];

    Do[
      parents = If[k == 1, {{}}, Tuples[Range[0, p - 1], k - 1]];

      Do[
        children   = Table[Append[parent, d], {d, 0, p - 1}];
        childCoords = Lookup[coords, children];

        (* Skip if any child vertex is missing from embedding *)
        If[MemberQ[childCoords, _Missing], Continue[]];

        childAngles = ArcTan @@ (# - rootPos) & /@ childCoords;
        order       = Ordering[childAngles];
        sortedAngles = childAngles[[order]];
        sortedDigits = Last /@ children[[order]];

        (* Sector boundaries at midpoints between adjacent siblings *)
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

(* main function *)

Options[PadicDigitTree] = {
  RayDigits             -> None,
  VertexLabelMode       -> "None",
  EdgeLabelMode         -> "Ray",
  DigitColors           -> Automatic,
  SectorBackground      -> False,
  SectorBackgroundDepth -> 1,
  SectorOpacity         -> 0.07,
  ImageSize             -> 900,
  Background            -> None
};

PadicDigitTree[p_Integer?Positive, depth_Integer?Positive, opts : OptionsPattern[]] :=
Module[
  {verts, edges, ray, rayEdges, colors, vLbl, eLbl,
   normalV, normalE, labelStyle, edgeLblStyle, graph, sectorGfx},

  verts  = padicVertices[p, depth];
  edges  = padicEdges[p, depth];
  colors = digitColorMap[p, OptionValue[DigitColors]];

  (* Ray path *)
  ray = If[OptionValue[RayDigits] === None, {},
    Join[{{}}, Table[Take[OptionValue[RayDigits], k],
      {k, Min[depth, Length @ OptionValue[RayDigits]]}]]];
  rayEdges = If[Length[ray] >= 2,
    UndirectedEdge @@@ Partition[ray, 2, 1], {}];
  normalV = Complement[verts, ray, {{}}];
  normalE = Complement[edges, rayEdges];

  (* Labels *)
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
        labelStyle], Center]) & /@ ray,
    "All",
      (# -> Placed[Style[
        If[# === {}, "\[Bullet]", StringJoin[ToString /@ #]],
        labelStyle], Center]) & /@ verts,
    _, None];

  eLbl = Module[{sel},
    sel = Switch[OptionValue[EdgeLabelMode],
      "FirstLevel", Select[edges, MemberQ[List @@ #, {}] &],
      "Ray",        rayEdges,
      "All",        edges,
      _,            {}];
    If[sel === {}, None,
      (# -> Placed[
        Framed[Style[ToString @ edgeDigit[#], edgeLblStyle,
          colors @ edgeDigit[#]],
          Background -> RGBColor[.07, .08, .10, .72],
          FrameStyle -> None, RoundingRadius -> 3,
          FrameMargins -> Tiny], .35]) & /@ sel]];

  (* Base graph *)
  graph = TreeGraph[verts, edges,
    GraphLayout  -> {"HyperbolicRadialEmbedding", "RootVertex" -> {}},
    VertexLabels -> vLbl,
    EdgeLabels   -> eLbl,
    VertexSize   -> Join[
      {{} -> .22},
      Thread[normalV -> .018],
      Thread[Complement[ray, {{}}] -> .10]],
    VertexStyle -> Join[
      {{} -> RGBColor[.45, .70, 1.]},
      Thread[normalV -> GrayLevel[.72]],
      Thread[Complement[ray, {{}}] -> RGBColor[.96, .97, 1.]]],
    EdgeStyle -> Join[
      (# -> Directive[colors @ edgeDigit[#], Opacity[.28],
        AbsoluteThickness[1]]) & /@ normalE,
      (# -> Directive[colors @ edgeDigit[#],
        AbsoluteThickness[4.2]]) & /@ rayEdges],
    ImageSize        -> OptionValue[ImageSize],
    Background       -> OptionValue[Background],
    ImagePadding     -> 25,
    PlotRangePadding -> Scaled[.03]];

  (* Overlay sectors if requested *)
  If[TrueQ[OptionValue[SectorBackground]],
    sectorGfx = buildSectors[graph, p, colors,
      OptionValue[SectorOpacity],
      OptionValue[SectorBackgroundDepth]];
    Show[Graphics[sectorGfx], graph],
    graph]
]


End[] (* End `Private` *)

EndPackage[]
