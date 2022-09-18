subsetQ[B_, A_] := Module[{i}, Catch[Do[If[ !MemberQ[B, i], Throw[False]], 
        {i, A}]; Throw[True]]]
 
selfSize := Module[{mainSet, powerSet, S}, mainSet = Range[5]; 
      powerSet = Subsets[mainSet]; Do[If[MemberQ[S, Length[S]], Print[S]], 
       {S, powerSet}]]
 
powerSet[set_] := Module[{bitS}, bitS = Table[0, {Length[set]}]; 
      While[bitS =!= Null, Print[bitToSubset[bitS, set]]; 
        bitS = nextBitS[bitS]; ]]
 
bitToSubset[bitS_, set_] := Extract[set, Position[bitS, 1]]
 
nextBitS[lastBitS_] := Module[{newBitS, i}, newBitS = lastBitS; 
      Catch[For[i = 1, i <= Length[lastBitS], i++, If[newBitS[[i]] == 1, 
          newBitS[[i]] = 0, newBitS[[i]] = 1; Throw[newBitS]]]; Throw[Null]]]
 
getVarsSets[S_] := Union[Cases[S, Except[U, _Symbol], Infinity]]
 
Attributes[printHold] = {HoldAll}
 
printHold[x_] := Module[{y}, Switch[Hold[x][[1,0]], Hold, y = x, Symbol, 
       y = Extract[OwnValues[x], {1, 2}, Hold], _, y = Hold[x]]; Print[y]]
 
Attributes[holdArgument] = {HoldAll}
 
holdArgument[x_] := Switch[Hold[x][[1,0]], Hold, x, Symbol, 
     Extract[OwnValues[x], {1, 2}, Hold], _, Hold[x]]
 
Attributes[membershipTable] = {HoldAll}
 
membershipTable[LS_, RS_] := Module[{L = holdArgument[LS], 
      R = holdArgument[RS], vars, numvars, cartesian, setList, rownum, 
      currentTuple, i, universe, ruleList}, vars = getVarsSets[{L, R}]; 
      numvars = Length[vars]; cartesian = Tuples[{0, 1}, numvars]; 
      setList = Table[{}, numvars]; For[rownum = 1, rownum <= 2^numvars, 
       rownum++, currentTuple = cartesian[[rownum]]; For[i = 1, i <= numvars, 
         i++, If[currentTuple[[i]] == 1, AppendTo[setList[[i]], rownum]]]]; 
      universe = Range[2^numvars]; ruleList = MapThread[Rule, 
        {vars, setList}]; AppendTo[ruleList, U -> universe]; 
      Union[ReleaseHold[L /. ruleList]] == Union[ReleaseHold[R /. ruleList]]]
 
fuzzyMemberQ[set_, object_] := Lookup[set, object, 0]
 
fuzzyIntersection[A_, B_] := Module[{keys, membership}, 
     keys = Intersection[Keys[A], Keys[B]]; membership = 
       Table[Min[fuzzyMemberQ[A, i], fuzzyMemberQ[B, i]], {i, keys}]; 
      AssociationThread[keys -> membership]]
 
bitToRoster[bitstring_, universe_] := Module[{S = {}, i}, 
     For[i = 1, i <= Length[universe], i++, If[bitstring[[i]] != 0, 
        AppendTo[S, {universe[[i]], bitstring[[i]]}]]]; S]
 
rosterToBit[roster_, universe_] := Module[{B, e, position}, 
     B = Table[0, {Length[universe]}]; 
      Do[position = Position[universe, e[[1]]][[1,1]]; 
        B[[position]] = e[[2]], {e, roster}]; B]
 
rosterToFuzzy[roster_] := Association @@ Apply[Rule, roster, {1}]
 
fuzzyToRoster[fuzzy_] := Apply[List, Normal[fuzzy], {1}]
 
posIntQ[x_] := IntegerQ[x] && Positive[x]
 
intShift[L:{__Integer}] := Module[{result = 0, i}, 
     For[i = 1, i <= Length[L], i++, result = result + L[[i]]*10^(i - 1)]; 
      result]
 
domain[f_Association] := Union[Keys[f]]
 
range[f_Association] := Union[Values[f]]
 
surjectiveQ[f_Association, codomain_List] := range[f] == Union[codomain]
 
injectiveQ[f_Association] := Length[range[f]] == Length[f]
 
geometricSequence[a_, r_, n_] := Module[{S = {}, i}, 
     Do[AppendTo[S, a*r^i], {i, 0, n}]; S]
 
geometricSequence2[a_, r_, n_] := Module[{i}, 
     Reap[Do[Sow[a*r^i], {i, 0, n}]][[2,1]]]
 
geometricSequence3[a_, r_, n_] := Module[{i, seq}, 
     Reap[Do[Sow[a*r^i, seq], {i, 0, n}], _, Set]; seq]
 
fib[1] = 0
 
fib[2] = 1
 
fib[n_] := fib[n - 1] + fib[n - 2]
 
fib2[1] = 0
 
fib2[2] = 1
 
fib2[n_] := fib2[n] = fib2[n - 1] + fib2[n - 2]
 
listRationals[max_] := Module[{L = {}, n, p, q}, 
     For[n = 2, n <= max, n++, For[q = 1, q <= n - 1, q++, 
        p = n - q; If[FreeQ[L, p/q], AppendTo[L, p/q]]]]; L]
 
locateRational[r_Rational] /; r > 0 := Module[{stage, L, i}, 
     stage = Numerator[r] + Denominator[r]; L = listRationals[stage]; 
      Catch[For[i = Length[L], i >= 1, i--, If[L[[i]] == r, Throw[i]]]]]
 
zeroOneMatrixQ[m_] := MatrixQ[m, #1 == 0 || #1 == 1 & ]
 
meet[(a_)?zeroOneMatrixQ, (b_)?zeroOneMatrixQ] := BitAnd[a, b]
 
join[(a_)?zeroOneMatrixQ, (b_)?zeroOneMatrixQ] := BitOr[a, b]
 
boolProduct[(A_)?zeroOneMatrixQ, (B_)?zeroOneMatrixQ] := 
    Module[{m, kA, kB, n, output, i, j, c, p}, {m, kA} = Dimensions[A]; 
      {kB, n} = Dimensions[B]; If[kA != kB, 
       Message[boolProduct::dimMismatch]; Return[]]; 
      output = ConstantArray[0, {m, n}]; For[i = 1, i <= m, i++, 
       For[j = 1, j <= n, j++, c = BitAnd[A[[i,1]], B[[1,j]]]; 
         For[p = 2, p <= kA, p++, c = BitOr[c, BitAnd[A[[i,p]], 
              B[[p,j]]]]; ]; output[[i,j]] = c; ]]; output]
 
boolProduct /: boolProduct::dimMismatch = 
     "The dimensions of the input matrices do not match."
 
fuzzyIntersectionCP[A_, B_] := Module[{U, Abits, Bbits, resultBits}, 
     U = Union[A[[All,1]], B[[All,1]]]; Abits = rosterToBit[A, U]; 
      Bbits = rosterToBit[B, U]; resultBits = MapThread[Min, {Abits, Bbits}]; 
      bitToRoster[resultBits, U]]
 
symmetricQ[(m_)?MatrixQ] := m == Transpose[m]
