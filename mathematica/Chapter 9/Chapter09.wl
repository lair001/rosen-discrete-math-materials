posIntQ[n_] := IntegerQ[n] && n > 0
 
myFactorial[(n_)?posIntQ] := Module[{}, If[n == 1, Return[1], 
      Return[n*myFactorial[n - 1]]]]
 
pairQ[{_, _}] := True
 
pairQ[___] := False
 
relationQ[{___?pairQ}] := True
 
relationQ[___] := False
 
dividesRelation[A:{__Integer}] := Select[Tuples[A, 2], 
     Divisible[#1[[2]], #1[[1]]] & ]
 
dividesRelation[n_Integer] := Select[Tuples[Range[n], 2], 
     Divisible[#1[[2]], #1[[1]]] & ]
 
inverseRelation[(R_)?relationQ] := Reverse[R, 2]
 
findDomain[(R_)?relationQ] := Union[Flatten[R, 1]]
 
reflexiveQ[(R_)?relationQ] := Module[{a, domain}, domain = findDomain[R]; 
      Catch[Do[If[ !MemberQ[R, {a, a}], Throw[False]], {a, domain}]; 
        Throw[True]]]
 
symmetricQ[(R_)?relationQ] := Module[{u}, 
     Catch[Do[If[ !MemberQ[R, Reverse[u]], Throw[False]], {u, R}]; 
       Throw[True]]]
 
antisymmetricQ[(R_)?relationQ] := Module[{u}, 
     Catch[Do[If[u[[1]] != u[[2]] && MemberQ[R, Reverse[u]], Throw[False]], 
        {u, R}]; Throw[True]]]
 
transitiveQ[(R_)?relationQ] := Module[{domain, a, b, c}, 
     domain = findDomain[R]; 
      Catch[Do[If[MemberQ[R, {a, b}] && MemberQ[R, {b, c}] && 
            !MemberQ[R, {a, c}], Throw[False]], {a, domain}, {b, domain}, 
         {c, domain}]; Throw[True]]]
 
tupleQ[_List] := True
 
tupleQ[___] := False
 
nrelationQ[{__?tupleQ}] := True
 
nrelationQ[___] := False
 
projectRelation[(R_)?nrelationQ, P:{__Integer}] := R[[All,P]]
 
joinRelation[(R_)?nrelationQ, (S_)?nrelationQ, p_Integer] := 
    Module[{overlapR, i, u, v, x, joinElement, T = {}}, 
     Do[x = u[[-p ;; -1]]; Do[If[v[[1 ;; p]] == x, 
          joinElement = Join[u, v[[p + 1 ;; -1]]]; AppendTo[T, joinElement]], 
         {v, S}], {u, R}]; T]
 
relationToMatrix[(R_)?relationQ] := Module[{u, max, m}, 
     max = Max[findDomain[R]]; m = ConstantArray[0, {max, max}]; 
      Do[m = ReplacePart[m, u -> 1], {u, R}]; m]
 
matrix01Q[m_List] := MatrixQ[m, #1 == 0 || #1 == 1 & ] && 
     Dimensions[m][[1]] == Dimensions[m][[2]]
 
matrix01Q[___] = False
 
reflexiveMatrixQ[(m_)?matrix01Q] := Module[{i, dim}, 
     dim = Dimensions[m][[1]]; Catch[For[i = 1, i <= dim, i++, 
         If[m[[i,i]] == 0, Throw[False]]]; Throw[True]]]
 
drawRelation[(R_)?relationQ, size_:Medium] := 
    Graph[Apply[Rule, Reverse[R, 2], 2], VertexSize -> size, 
     VertexLabels -> Placed["Name", Center], EdgeShapeFunction -> 
      {DirectedEdge[x_, x_] -> None}]
 
transitiveGraphQ[g_Graph] := Module[{d, i, j}, d = GraphDistanceMatrix[g]; 
      Cases[Flatten[d], Except[0 | 1 | Infinity]] == {}]
 
reflexiveClosure[(m_)?matrix01Q] := Module[{ans = m, i}, 
     Do[ans[[i,i]] = 1, {i, Dimensions[m][[1]]}]; ans]
 
symmetricClosure[(m_)?matrix01Q] := Module[{ans = m, i, j}, 
     Do[If[ans[[i,j]] == 1, ans[[j,i]] = 1], {i, Dimensions[m][[1]]}, 
       {j, Dimensions[m][[2]]}]; ans]
 
boolProduct[(A_)?matrix01Q, (B_)?matrix01Q] := 
    Module[{m, kA, kB, n, output, i, j, c, p}, {m, kA} = Dimensions[A]; 
      {kB, n} = Dimensions[B]; If[kA != kB, 
       Message[boolProduct::dimmismatch]; Return[]]; 
      output = ConstantArray[0, {m, n}]; For[i = 1, i <= m, i++, 
       For[j = 1, j <= n, j++, c = BitAnd[A[[i,1]], B[[1,j]]]; 
         For[p = 2, p <= kA, p++, c = BitOr[c, BitAnd[A[[i,p]], 
              B[[p,j]]]]; ]; output[[i,j]] = c; ]]; output]
 
boolProduct /: boolProduct::dimMismatch = 
     "The dimensions of the input matrices do not match."
 
transitiveClosure[(m_)?matrix01Q] := Module[{i, a = m, b = m}, 
     Do[a = boolProduct[a, m]; b = BitOr[b, a], {i, 2, Dimensions[m][[1]]}]; 
      b]
 
warshall[(m_)?matrix01Q] := Module[{i, j, k, w = m, n}, 
     n = Dimensions[m][[1]]; For[k = 1, k <= n, k++, For[i = 1, i <= n, i++, 
        For[j = 1, j <= n, j++, w[[i,j]] = BitOr[w[[i,j]], 
           BitAnd[w[[i,k]], w[[k,j]]]]]]]; w]
 
equivalenceQ[(R_)?relationQ] := reflexiveQ[R] && symmetricQ[R] && 
     transitiveQ[R]
 
makeMod4[n_Integer] := Module[{i, j}, 
     Reap[Do[If[Mod[i - j, 4] == 0, Sow[{i, j}]], {i, 0, n}, {j, 0, n}]][[2,
      1]]]
 
equivalenceClass[(R_)?equivalenceQ, a_] := 
    Module[{b}, Union[Cases[R, {a, b_} -> b]]]
 
allEquivalenceRelations[A_List] := Select[Subsets[Tuples[A, 2]], equivalenceQ]
 
equivalenceClosure[(R_)?relationQ] := transitiveClosure[
     symmetricClosure[reflexiveClosure[relationToMatrix[R]]]]
 
partialOrderQ[(R_)?relationQ] := reflexiveQ[R] && antisymmetricQ[R] && 
     transitiveQ[R]
 
divisorLattice[n_Integer] := dividesRelation[Divisors[n]]
 
coversQ[(R_)?partialOrderQ, {x_, y_}] := Module[{z, checkSet}, 
     Catch[If[x == y, Throw[False]]; If[ !MemberQ[R, {x, y}], Throw[False]]; 
       checkSet = Complement[findDomain[R], {x, y}]; 
       Do[If[MemberQ[R, {x, z}] && MemberQ[R, {z, y}], Throw[False]], 
        {z, checkSet}]; Throw[True]]]
 
coveringRelation[(R_)?partialOrderQ] := Select[R, coversQ[R, #1] & ]
 
hasseDiagram[(R_)?partialOrderQ, size_:Medium] := 
    Module[{edges}, edges = Apply[Rule, Reverse /@ coveringRelation[R], {1}]; 
      Graph[edges, VertexSize -> size, VertexLabels -> 
        Placed["Name", Center]]]
 
minimalElements[(R_)?partialOrderQ, S_List] := Module[{M, s, t}, 
     M = S; Do[Do[If[MemberQ[R, {t, s}], M = Complement[M, {s}]], 
        {t, Complement[S, {s}]}], {s, S}]; M]
 
maximalElements[(R_)?partialOrderQ, S_List] := 
    minimalElements[inverseRelation[R], S]
 
upperBoundQ[(R_)?partialOrderQ, S_List, u_] := 
    Module[{s}, Catch[Do[If[ !MemberQ[R, {s, u}], Throw[False]], {s, S}]; 
       Throw[True]]]
 
upperBounds[(R_)?partialOrderQ, S_List] := Module[{domR, d, U = {}}, 
     domR = findDomain[R]; Do[If[upperBoundQ[R, S, d], AppendTo[U, d]], 
       {d, domR}]; U]
 
leastUpperBound[(R_)?partialOrderQ, S_List] := 
    Module[{U, M}, U = upperBounds[R, S]; M = minimalElements[R, U]; 
      If[Length[M] != 1, Null, M[[1]]]]
 
latticeQ[(R_)?partialOrderQ] := hasLUBs[R] && hasGLBs[R]
 
hasLUBs[(R_)?partialOrderQ] := Module[{domR, a, b}, 
     domR = findDomain[R]; Catch[Do[If[leastUpperBound[R, {a, b}] === Null, 
          Throw[False]], {a, domR}, {b, domR}]; Throw[True]]]
 
hasGLBs[(R_)?partialOrderQ] := hasLUBs[inverseRelation[R]]
 
topologicalSort[(R_)?partialOrderQ] := Module[{S, a, T}, 
     T = {}; S = findDomain[R]; While[S != {}, 
       a = minimalElements[R, S][[1]]; S = Complement[S, {a}]; 
        T = AppendTo[T, a]]; T]
 
allRelations[S_List] := Subsets[Tuples[S, 2]]
 
countTransitive[n_Integer] := Module[{i, j, T, M, count = 0}, 
     For[i = 0, i <= 2^n^2 - 1, i++, T = IntegerDigits[i, 2, n^2]; 
        M = Partition[T, n]; If[warshall[M] == M, count++]]; count]
