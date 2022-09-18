makePostage[stampA_Integer, stampB_Integer, postage_Integer] := 
    Module[{a, b}, Catch[For[a = 0, a <= Floor[postage/stampA], a++, 
       For[b = 0, b <= Floor[postage/stampB], b++, 
        If[stampA*a + stampB*b == postage, Throw[{a, b}]]]]]]
 
postageBasis[stampA_Integer, stampB_Integer, minpostage_Integer] := 
    Module[{small, postageList = {}, postage, R}, 
     small = Min[stampA, stampB]; Check[For[postage = minpostage, 
         postage <= minpostage + small - 1, postage++, 
         R = makePostage[stampA, stampB, postage]; If[R =!= Null, 
           AppendTo[postageList, postage -> R], Message[postageBasis::fail, 
            stampA, stampB, postage]]]; postageList, Null]]
 
postageBasis /: postageBasis::fail = 
     "Cannot form postage of `3` using stamps of amounts `1` and `2`."
 
recurseS[S_List] := Module[{x, y, T = S}, 
     Do[T = Union[T, {x + y}], {x, S}, {y, S}]; T]
 
buildStrings[S_List, A_List] := Module[{T = S, w, x}, 
     Do[T = Union[T, {StringJoin[w, x]}], {w, S}, {x, A}]; T]
 
allStrings[A_List, n_Integer] := Module[{S = {""}, i}, 
     For[i = 1, i <= n, i++, S = buildStrings[S, A]]; S]
 
power1[_Integer, 0, _Integer] := 1
 
power1[b_Integer, n_Integer, m_Integer] /; n > 0 := 
    Mod[b*power1[b, n - 1, m], m]
 
power2[_Integer, 0, _Integer] := 1
 
power2[b_Integer, n_Integer, m_Integer] /; n > 0 && EvenQ[n] := 
    Mod[power2[b, n/2, m]^2, m]
 
power2[b_Integer, n_Integer, m_Integer] /; n > 0 && OddQ[n] := 
    Mod[Mod[power2[b, Floor[n/2], m]^2, m]*b, m]
 
factorialR[n_Integer] /; n >= 0 := Module[{}, If[n == 0, 1, 
      n*factorialR[n - 1]]]
 
factorialI[n_Integer] /; n >= 0 := Module[{f, i}, 
     f = 1; For[i = 1, i <= n, i++, f = f*i]; f]
 
mergeSort[L:{__Integer}] := Module[{m, L1, L2}, If[Length[L] > 1, 
      m = Floor[Length[L]/2]; L1 = L[[1 ;; m]]; L2 = L[[m + 1 ;; All]]; 
       merge[mergeSort[L1], mergeSort[L2]], L]]
 
merge[l1:{__Integer}, l2:{__Integer}] := Module[{L, L1, L2}, 
     L = {}; L1 = l1; L2 = l2; While[L1 =!= {} && L2 =!= {}, 
       If[L1[[1]] < L2[[1]], AppendTo[L, L1[[1]]]; L1 = Delete[L1, 1], 
         AppendTo[L, L2[[1]]]; L2 = Delete[L2, 1]]; Which[L1 === {}, 
         L = Join[L, L2]; L2 = {}, L2 === {}, L = Join[L, L1]; L1 = {}]]; L]
 
mergeSortVerbose[L:{__Integer}] := Module[{m, L1, L2}, 
     Print["mergeSort called on ", L]; If[Length[L] > 1, 
       m = Echo[Floor[Length[L]/2], "m= "]; L1 = Echo[L[[1 ;; m]], "L1= "]; 
        L2 = Echo[L[[m + 1 ;; All]], "L2= "]; merge[mergeSortVerbose[L1], 
         mergeSortVerbose[L2]], Print["length=1"]; L]]
 
buildWFFs[S_List] := Module[{T = S, f, g, o}, 
     Do[T = Union[T, {StringJoin["(-", f, ")"]}], {f, S}]; 
      Do[T = Union[T, {StringJoin["(", f, o, g, ")"]}], {f, S}, {g, S}, 
       {o, {"+", "-", "*", "/"}}]; T]
 
allWFFs[m_Integer] := Module[{S, i}, S = {"x", "y", "z"}; 
      For[i = 1, i <= m, i++, S = buildWFFs[S]]; S]
 
testWFF3[s_String] := StringCount[s, {"x", "y", "z", "+", "-", "*", "/"}] <= 3
 
checkFib5[n_Integer] := Module[{F}, F = Fibonacci[n]; 
      If[Divisible[F, 5] &&  !Divisible[n, 5], Print["Fn="*F, 
        " is not divisible by 5, but n=", n, " is"]]; 
      If[Divisible[n, 5] &&  !Divisible[F, 5], Print["Fn="*F, 
        " is divisible by 5, but n=", n, " is not"]]; ]
