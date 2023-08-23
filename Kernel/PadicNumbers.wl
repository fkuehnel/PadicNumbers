BeginPackage["PadicNumbers`"]

(* Declare your package's public symbols here. *)

PadicDegree
PadicNorm
PadicOrder
PadicNormalize

Padic
PadicDigits
PadicN

Begin["`Private`"]

(****************** P-adic order and valuation *****************)

PadicDegree[0,p_Integer/;p > 1] := 0
PadicDegree[n_Integer, p_Integer/;p > 1] := Floor[Log[p, Abs[n]]]
PadicRational /: PadicDegree[PadicRational[m_,p_,e_,__]] := PadicDegree[m, p]

PadicNorm[0,p_Integer/;p>1] := 0
PadicNorm[n_Integer/;n!=0,p_Integer/;p>1] :=
    1/GCD[n,p^PadicDegree[n,p]]
(* Mathematica ensures that rational numbers have no common 
   factors between numerator and denominator.  *)
PadicNorm[r_Rational,p_Integer/;p>1] :=
    PadicNorm[Numerator[r],p]/PadicNorm[Denominator[r],p]

PadicOrder[0,p_] := Infinity
PadicOrder[n_Integer | n_Rational,p_Integer/;p>1] :=
    Round[-Log[p,PadicNorm[n,p]]]

PadicNormalize[n_Integer | n_Rational,p_Integer/;p>1] := n PadicNorm[n,p]
(* This is exceptional, doesn't happen unless with have
   arithmetic operations *)
PadicNormalize[s:PadicRational[m_,p_,e_,n_,___]] := s /; Mod[m,p] == 0

(* We don't require p as a second argument when doing p-adic 
   order or value of a p-adic number. *)
PadicRational /: PadicOrder[PadicRational[0,p_,___]] := Infinity
PadicRational /: PadicOrder[PadicRational[_,p_,e_,___]] := e
PadicRational /: PadicOrder[PadicRational[_,p_,e_,___], p_] := e

(* We also can find PadicOrder and PadicValue regarding to 
   another base *)
PadicRational /: PadicOrder[s:PadicRational[_,p1_,e_,___],
    p2_Integer/;p2>1] := PadicOrder[s//Normal,p2]

PadicRational /: PadicNorm[s:PadicRational[_,p_,e_,___]] := p^(-PadicOrder[s])

(* Helper functions to find the P-adic periodicity for rational numbers *)
ExpandToPowerOf[p_Integer/;p>1] := Function[{r},
    ({#[[2]] r, 0}+QuotientRemainder[#[[1]] Numerator[r],p])&[
        ExtendedGCD[Denominator[r],p][[2]]]]

FindExponent[d_Integer,p_Integer/;p>1] :=
    NestWhile[
        Append[QuotientRemainder[p^(#[[3]] + 1) - 1,d], #[[3]] + 1]&,
            {0,d,0}, MatchQ[#,{_,n_Integer/;n>0,_}]&]            

FindPeriodicity[r_Rational/;-1<=r<0,p_Integer/;p>1] :=
    Drop[FindExponent[Denominator[r],p],1] /; PadicNorm[r,p] == 1

FindPeriodicity[r_Rational/;0<r<1,p_Integer/;p>1] :=
    {1, 0} + FindPeriodicity[-r,p] /; PadicNorm[r,p] == 1

(* This is really just a backup *)
FindPeriodicity[r_Rational,p_Integer/;p>1] :=
    Composition[{Count[#,{{_,_},1}],
        Count[#,{{_,_},n_Integer/;n>1}]}&,Tally][
            Drop[NestList[ExpandToPowerOf[p][#[[1]]]&,
                {r,0},1000],1]] /; PadicNorm[r,p] == 1

FindPeriodicity[r_Rational,p_Integer/;p>1] :=
    FindPeriodicity[PadicNormalize[r,p],p] /; PadicNorm[r,p] != 1

(************Conversion to Integers and Rationals*************)

PadicRational /: Normal[PadicRational[m_,p_,e_,_,0]] := m p^e
PadicRational /: Normal[PadicRational[m_,p_,e_,n_,k_/;k>0]] :=
    (p^e QuotientRemainder[m,p^#].{-p^#/(p^k - 1),1})&[n - k]

(*********************Negation of P-adics*********************)

PadicRational /: Minus[s:PadicRational[0,___]] := s
PadicRational /: Minus[PadicRational[1,p_,e_,1,0]] :=
    PadicRational[p-1,p,e,1,1]
PadicRational /: Minus[PadicRational[m_,p_,e_,n_,0]] :=
    PadicRational[Mod[-m,p^(n + 1)],p,e,n + 1,1]

(* reduction to non-periodic (positive integer) expansion *)
PadicRational /: Minus[PadicRational[m_,p_,e_,n_,1]] :=
    PadicRational[Mod[-m,p^(n-1)],p,e,n-1,0] /; Quotient[m,p^j] == p-1
(* case 2b, purely periodic expansion *)
PadicRational /: Minus[PadicRational[m_,p_,e_,k_,k_/;k>0]] :=
    PadicRational[Mod[-m,p^(k+1)],p,e,k+1,k]
(* case 3b, eventually periodic expansion *)
PadicRational /: Minus[s:PadicRational[m_,p_,e_,n_,k_/;k>0]] :=
    PadicRational[Mod[-m,p^n],p,e,n,k] /; n > k

(********************Conversion to P-adics********************)

(* case 0 *)
Padic[0,p_Integer/;p>1] := PadicRational[0,p,0,0,0]
Padic[n_Integer/;n>0,p_Integer/;p>1] :=
    PadicRational[n,p,0,PadicDegree[n,p]+1,0] /; PadicNorm[n,p] == 1
(* case 1 *)
Padic[n_Integer/;n<0,p_Integer/;p>1] := Minus[Padic[-n,p]]
(* combined cases 2a, 2b, 3a and 3b *)
Padic[r_Rational,p_Integer/;p>1] := (PadicRational[
      Mod[Numerator[r] PowerMod[Denominator[r],-1,p^(#1+#2)],
          p^(#1+#2)],p,0,#1+#2, #2]&)@@FindPeriodicity[r,p] /; PadicNorm[r,p] == 1
(* Case 4: Rational or Tnteger has a left/right shift in p-adic expansion *)
Padic[r_Integer | r_Rational,p_Integer/;p>1] :=
    ReplacePart[Padic[PadicNormalize[r,p],p],3->PadicOrder[r,p]] /; PadicNorm[r,p] != 1

(* Just the case we change the basis *)
PadicRational /: Padic[(s:PadicRational[m_,p1_,__]),p2_Integer/;p2>1] :=
    Padic[s//Normal,p2] /; p1 != p2

SetAttributes[Padic,Listable]

Padic[e_Plus,p_Integer,n_Integer] := Padic[#,p,n]& /@ e
Padic[e_Times,p_Integer,n_Integer] := Padic[#,p,n]& /@ e
Padic[x_^m_,p_Integer,n_Integer] := Padic[x,p,n]^m

(*Drop the Padic when applied to an atom.*)
Padic[e_,___] := e /; AtomQ[e]

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

(********************Conversion to digits*********************)

PadicDigits[s_,p_Integer/;p>0] := PadicDigits[Padic[s,p]]
PadicDigits[PadicRational[0,___]] := {0}
PadicDigits[PadicRational[m_,p_,e_/;e<=0,n_,___]] :=
    IntegerDigits@@{m,p,n}
PadicDigits[s:PadicRational[_,_,e_/;e>0,___]] :=
    Join[PadicDigits[ReplacePart[s,3->0]],Table[0,Abs[e]]]

(**********************P-adics formatting*********************)

(* positive scaled non-periodic expansions *)
PadicRational /: Format[s:PadicRational[_,p_,e_/;0<=e<=4,_,0]] :=
    Subscript[Row[PadicDigits[s]," "],p]

(* negative scaled non-periodic expansions *)
PadicRational /: Format[s:PadicRational[_,p_,e_/;-4<=e<0,n_,0]] :=
    Row[Insert[Join[Table[0,-(n + e)],PadicDigits[s]],Subscript[".",p],e - 1]," "]

(* purely & eventually periodic expansions, let's keep it simple *)
PadicRational /: Format[s:PadicRational[_,p_,0,k_,k_/;k>0]] :=
    Subscript[OverBar[Row[#1," "]],p]&[Take[PadicDigits[s],k]]
PadicRational /: Format[s:PadicRational[_,p_,0,n_,k_/;k>0]] :=
    Subscript[Row[{OverBar[Row[#1," "]],Row[#2," "]}," "],p]&@@
        TakeDrop[PadicDigits[s],k] /; n > k

(* simply add a scale factor here *)
PadicRational /: Format[s:PadicRational[_,p_,e_/;e!=0,_,_]] :=
    Row[{Format[ReplacePart[s,3->0]],Superscript[p,e]},"\[Times]"]

(****************P-adic rational approximation****************)

PadicRational /: PadicN[PadicRational[m_,p_,e_,n_,k_]] :=
    PadicRationalN[m,p,e,n]

PadicRationalApprox[c_,pk_] := If[#[[2]] < Sqrt[pk/2], #[[1]]/#[[2]], c]&[
    NestWhile[Function[{v,w}, {w,v - Floor[v[[1]]/w[[1]]] w}]@@#&,
        {{pk,0},{c,1}},(#[[2,1]] > Sqrt[pk/2])&][[2]]]

PadicRationalN /: Normal[PadicRationalN[m_,p_,e_,n_]] :=
    PadicRationalApprox[m,p^n] p^e

PadicRationalN /: Minus[PadicRationalN[m_,p_,e_,n_]] :=
    PadicRationalN[Mod[-m,p^n],p,e,n]

PadicN[r_Integer | r_Rational,p_Integer/;p>1] := PadicN[r,p,8]
PadicN[n_Integer, p_Integer/;p>1,N_Integer/;N>0] :=
    PadicRationalN[Mod[#1, p^N],p,#2,N]&[PadicNormalize[n,p],PadicOrder[n,p]]
PadicN[r_Rational,p_Integer/;p>1,N_Integer/;N>0] :=
  PadicRationalN[Mod[Numerator[#1] PowerMod[Denominator[#1],-1,p^N], p^N],
      p,#2,N]&[PadicNormalize[r,p],PadicOrder[r,p]]

(*p-adic ADDITION*)
PadicRationalN /: (x:PadicRationalN[a_, p_, e_, N_]) + (y:PadicRationalN[b_, p_, e_, N_]) :=
    Block[{n = N + PadicOrder[a + b, p] - Min[PadicOrder[x], PadicOrder[y]]},
        PadicRationalN[Mod[a + b, p^n], p, e, n]]

End[] (* End `Private` *)

EndPackage[]
