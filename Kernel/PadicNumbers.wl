(* ::Package:: *)

BeginPackage["PadicNumbers`"]

(* Declare package's public symbols here. *)

PadicOrder
PadicAbs
PadicNormalize
PadicSignature

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
        
PadicSignature[n_Integer?Positive,p_Integer/;p>1] := {IntegerLength[Abs[n], p], 0}
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
		With[{{n,k}=PadicSignature[rr,p]},
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

(******************** P-adic arithmetic **********************)

(* P-adic multiplication *)
NormalizeMantissa[s:PadicRational[a_/;a>0,p_,e_,n_,0]] := ReplacePart[s,4->
    n+1-Length[NestWhile[Append[QuotientRemainder[#[[2]],p^#[[3]]],#[[3]]-1]&,{0,a,n-2},#[[1]]==0&]]]

PadicRational /: (a:PadicRational[0,__]) * (b_PadicRational|b_Integer|b_Rational) := a
PadicRational /: PadicRational[a_,p_,e1_,n1_,k1_] * PadicRational[b_,p_,e2_,n2_,0] :=
    NormalizeMantissa[PadicRational[Mod[a*b,p^(#1+#2)],p,e1+e2,#1+#2,#2]&@@{n1+n2,k1}]

(* Multiplying an integer or rational to a p-adic number *)
PadicRational /: a_PadicRational * (-1) := Minus[a]
PadicRational /: (a:PadicRational[_,p_,__]) * (b_Integer/;b>=0) := a * Padic[b,p]
PadicRational /: a_PadicRational * (b_Integer/;b<0) := Minus[a * (-b)]
PadicRational /: (a:PadicRational[_,p_,__]) * b_Rational := a * Padic[b,p]

(* P-adic addition, a bit more complicated *)

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

(******************* P-adic Visualization ********************)


End[] (* End `Private` *)

EndPackage[]
