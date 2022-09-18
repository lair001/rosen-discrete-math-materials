
Attributes[and] = {Listable}
 
and[p_, q_] := Switch[{p, q}, {1, 1}, 1, {1, 0}, 0, {0, 1}, 0, {0, 0}, 0, _, 
     Message[and::arg]]
 
and /: and::arg = "and called with non-bit arguments."
 
equivalentQ[p_, q_] := TautologyQ[Equivalent[p, q]]
 
getVars[p_] := Module[{L = {p}, i = 1}, 
     While[i <= Length[L], If[Head[L[[i]]] === Symbol, i++, 
        L[[i,0]] = List; L = Flatten[L]]]; DeleteDuplicates[L]]
 
nextTA[A_] := Module[{i, newTA = A}, 
     Catch[For[i = 1, i <= Length[A], i++, If[newTA[[i]], newTA[[i]] = False, 
         newTA[[i]] = True; Throw[newTA]]]; Throw[Null]]]
 
myEquivalentQ[p_, q_] := Module[{bicond, vars, numVars, TA, val}, 
     bicond = Equivalent[p, q]; vars = getVars[bicond]; 
      numVars = Length[vars]; TA = ConstantArray[False, numVars]; 
      Catch[While[TA =!= Null, val = bicond /. MapThread[Rule, {vars, TA}]; 
          If[ !val, Throw[False]]; TA = nextTA[TA]]; Throw[True]]]
 
nQueens1[n_] := And @@ Table[Or @@ Table[p[i, j], {j, 1, n}], {i, 1, n}]
 
nQueens2[n_] := And @@ 
     Table[And @@ Table[And @@ Table[ !p[i, j] ||  !p[i, k], {k, j + 1, n}], 
        {j, 1, n - 1}], {i, 1, n}]
 
nQueens3[n_] := And @@ 
     Table[And @@ Table[And @@ Table[ !p[i, j] ||  !p[k, j], {k, i + 1, n}], 
        {i, 1, n - 1}], {j, 1, n}]
 
nQueens4[n_] := And @@ 
     Table[And @@ Table[And @@ Table[ !p[i, j] ||  !p[i - k, k + j], 
          {k, 1, Min[i - 1, n - j]}], {j, 1, n - 1}], {i, 2, n}]
 
nQueens5[n_] := And @@ 
     Table[And @@ Table[And @@ Table[ !p[i, j] ||  !p[i + k, j + k], 
          {k, 1, Min[n - i, n - j]}], {j, 1, n - 1}], {i, 1, n - 1}]
 
nQueens[n_] := Grid[Partition[SatisfiabilityInstances[
        nQueens1[n] && nQueens2[n] && nQueens3[n] && nQueens4[n] && 
         nQueens5[n], Flatten[Table[p[i, j], {i, 1, n}, {j, 1, n}]]][[1]], n]]
 
validQ[A_] := Module[{premiseList, premises}, premiseList = A[[1 ;; -2]]; 
      premises = And @@ premiseList; TautologyQ[Implies[premises, A[[-1]]]]]
 
allCompound[vars_] := Module[{p, q, tempList = vars, propList}, 
     Do[AppendTo[tempList,  !p], {p, vars}]; propList = tempList; 
      Do[If[ !TautologyQ[p && q] &&  !TautologyQ[ !(p && q)], 
         AppendTo[propList, p && q]]; If[ !TautologyQ[p || q] && 
           !TautologyQ[ !(p || q)], AppendTo[propList, p || q]]; 
        If[ !TautologyQ[Implies[p, q]] &&  !TautologyQ[ !Implies[p, q]], 
         AppendTo[propList, Implies[p, q]]], {p, tempList}, {q, tempList}]; 
      DeleteDuplicates[propList]]
 
findConsequences[premises_, level_] := 
    Module[{vars, P, possibleC, conclusions = {}, c, i}, 
     vars = getVars[premises]; possibleC = vars; For[i = 1, i <= level, i++, 
       possibleC = allCompound[possibleC]]; 
      Do[If[validQ[Append[premises, c]], AppendTo[conclusions, c]], 
       {c, possibleC}]; conclusions]
 
find3squares[n_] := Module[{a, b, c, max = Floor[Sqrt[n]]}, 
     Catch[For[a = 0, a <= max, a++, For[b = 0, b <= max, b++, 
         For[c = 0, c <= max, c++, If[n == a^2 + b^2 + c^2, 
           Throw[{a, b, c}]]]]]; Throw[False]]]
 
findPowers[n_] := Module[{L = {}, b, p = 2, continuep = True, continueb}, 
     While[continuep, b = 1; continueb = True; While[continueb, 
         If[b^p > n, continueb = False, AppendTo[L, b^p]; b++]]; p++; 
        If[2^p > n, continuep = False]]; Union[L]]
 
findConsecutivePowers[n_] := Module[{powers, x}, powers = findPowers[n]; 
      Do[If[MemberQ[powers, x + 1], Print[x, " ", x + 1]], {x, powers}]]
 
mySatisfiableQ[p_] := Module[{result = False, vars, numVars, TA, val}, 
     vars = getVars[p]; numVars = Length[vars]; 
      TA = ConstantArray[False, numVars]; While[TA =!= Null, 
       val = p /. MapThread[Rule, {vars, TA}]; 
        If[val, result = True; Print[TA]]; TA = nextTA[TA]; ]; result]
 
allPairSums[L_, max_] := Module[{a = 1, b, s, sumList = {}, num = Length[L]}, 
     While[a <= num, b = a; While[b <= num, s = L[[a]] + L[[b]]; 
          If[s <= max, AppendTo[sumList, s], b = num]; b++; ]; a++; ]; 
      Union[sumList]]
