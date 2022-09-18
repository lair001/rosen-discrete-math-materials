makePostage[stampA_Integer, stampB_Integer, postage_Integer] := 
    Module[{a, b}, Catch[For[a = 0, a <= Floor[postage/stampA], a++, 
       For[b = 0, b <= Floor[postage/stampB], b++, 
        If[stampA*a + stampB*b == postage, Throw[{a, b}]]]]]]
 
subsetSumCount[S:{__Integer}, target_Integer] := 
    Length[Select[Subsets[S], Plus @@ #1 < target & ]]
 
addBit[L_List] := Module[{}, If[L[[{-2, -1}]] == {1, 1}, {Append[L, 0]}, 
      {Append[L, 0], Append[L, 1]}]]
 
findBitStrings[n_Integer] := Module[{S, s, T = {}}, 
     If[n == 2, {{0, 0}, {0, 1}, {1, 0}, {1, 1}}, S = findBitStrings[n - 1]; 
       Do[T = Join[T, addBit[s]], {s, S}]; T]]
 
findSubSum[L:{__Integer}, T_Integer] := Module[{A, i, j, a = 0, p}, 
     A = Table[a = a + L[[i]], {i, Length[L]}]; 
      Catch[For[i = 1, i <= Length[L], i++, If[MemberQ[A, A[[i]] + T], 
         j = Position[A, A[[i]] + T][[1,1]]; Throw[{i, j, L[[i ;; j]]}]]]]]
 
findIncreasing[S:{__Integer}] := Module[{piles = {}, pointers, step, 
      whichpile, p, iList}, For[step = 1, step <= Length[S], step++, 
       whichpile = Catch[For[p = 1, p <= Length[piles], p++, 
            If[S[[step]] < piles[[p]], Throw[p]]]; Throw[Null]]; 
        If[whichpile === Null, AppendTo[piles, S[[step]]], 
         piles[[whichpile]] = S[[step]]]; Which[whichpile === 1 || 
          Length[piles] == 1, pointers[S[[step]]] = Null, whichpile === Null, 
         pointers[S[[step]]] = piles[[-2]], True, pointers[S[[step]]] = 
          piles[[whichpile - 1]]]]; iList = {piles[[-1]]}; 
      While[pointers[iList[[1]]] =!= Null, PrependTo[iList, 
        pointers[iList[[1]]]]]; iList]
 
numPerm[n_Integer, r_Integer] /; 0 <= r <= n := n!/(n - r)!
 
CPEqualQ[L1_List, L2_List] := Module[{i, Ltest = L2}, 
     If[L1 == Ltest, Return[True]]; For[i = 1, i <= Length[Ltest] - 1, i++, 
       Ltest = RotateLeft[Ltest]; If[L1 == Ltest, Return[True]]]; 
      Return[False]]
 
circularPermutations[S_List, r_Integer] := Module[{allP, allCP, isnew, p}, 
     allP = Permutations[S, {r}]; allCP = {allP[[1]]}; 
      allP = Delete[allP, 1]; While[allP != {}, 
       isnew = Catch[Do[If[CPEqualQ[allP[[1]], p], Throw[False]], 
            {p, allCP}]; Throw[True]]; If[isnew, AppendTo[allCP, allP[[1]]]]; 
        allP = Delete[allP, 1]]; allCP]
 
binomialF[n_Integer, k_Integer] /; 0 <= k <= n := n!/(k!*(n - k)!)
 
binomialR[n_Integer, k_Integer] /; 0 <= k <= n := 
    Module[{}, Which[k == 0, binomialR[n, k] = 1, 2*k > n, 
      binomialR[n, k] = binomialR[n, n - k], True, binomialR[n, k] = 
       binomialR[n - 1, k - 1] + binomialR[n - 1, k]]]
 
CRep[n_Integer, r_Integer] /; n > 0 && r >= 0 := Binomial[n + r - 1, r]
 
myMultinomial[n_Integer, L__Integer] := Module[{discard, denomList, denom}, 
     discard = n - (Plus[L]); denomList = {L, discard}!; 
      denom = Times @@ denomList; n!/denom]
 
makeStirling2[n_Integer, k_Integer] /; n > 0 && k > 0 := 
    Module[{A, k1boxes, kboxes, B, new, i}, 
     Which[k == 1, A = {{Range[n]}}, k > n, A = {}, True, 
       A = {}; k1boxes = makeStirling2[n - 1, k - 1]; 
        Do[new = Union[B, {{n}}]; AppendTo[A, new], {B, k1boxes}]; 
        kboxes = makeStirling2[n - 1, k]; Do[For[i = 1, i <= k, i++, 
          new = ReplacePart[B, i -> Append[B[[i]], n]]; AppendTo[A, new]], 
         {B, kboxes}]]; A]
 
myPartitionsP[_, 1] := 1
 
myPartitionsP[0, _] := 1
 
myPartitionsP[n_, k_] /; n < 0 || k < 1 := 0
 
myPartitionsP[n_Integer, k_Integer] /; n > 0 && k > 1 := 
    myPartitionsP[n, k - 1] + myPartitionsP[n - k, k]
 
interchange[L_List, i_Integer, j_Integer] /; 
     Inequality[0, Less, i, LessEqual, Length[L]] && 
      Inequality[0, Less, j, LessEqual, Length[L]] := 
    Module[{l = L, temp}, temp = l[[i]]; l[[i]] = l[[j]]; l[[j]] = temp; l]
 
nextPermutation[A_List] /; Sort[A] == Range[Length[A]] := 
    Module[{a = A, n = Length[A], i, j, k, r, s}, 
     If[a == Reverse[Range[n]], Return[Null]]; j = n - 1; 
      While[a[[j]] > a[[j + 1]], j = j - 1]; k = n; While[a[[j]] > a[[k]], 
       k = k - 1]; a = interchange[a, j, k]; r = n; s = j + 1; 
      While[r > s, a = interchange[a, r, s]; r = r - 1; s = s + 1]; a]
 
permuteList[L_List] := Module[{perm}, perm = Range[Length[L]]; 
      Reap[While[perm =!= Null, Sow[L[[perm]]]; perm = nextPermutation[
            perm]]][[2,1]]]
 
subsetsRepetition[n_Integer, r_Integer] /; n > 0 && r > 0 := 
    Module[{L, i}, L = Range[n]; DeleteDuplicates[
       Subsets[Join @@ Table[ConstantArray[i, r], {i, L}], {r}]]]
 
playoffWonQ[L_List, n_Integer] := Count[L, 1] == n || Count[L, 2] == n
 
allPlayoffs[n_Integer] := Module[{outcomes = {}, S = {{1}, {2}}, p, p1, p2}, 
     While[S != {}, p = S[[1]]; S = Delete[S, 1]; p1 = Append[p, 1]; 
        p2 = Append[p, 2]; If[playoffWonQ[p1, n], AppendTo[outcomes, p1], 
         AppendTo[S, p1]]; If[playoffWonQ[p2, n], AppendTo[outcomes, p2], 
         AppendTo[S, p2]]; ]; outcomes]
