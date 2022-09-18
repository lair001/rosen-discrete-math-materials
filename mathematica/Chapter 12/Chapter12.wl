dual[expr_] := expr /. {And -> Or, Or -> And, False -> True, True -> False}
 
Attributes[expressionTree] = {HoldFirst}
 
expressionTree[s_Symbol, opts___] := If[Head[Evaluate[s]] =!= Symbol, 
     expressionTree[Evaluate[s], opts], newExpressionTree[s, opts]]
 
expressionTree[expr_, opts___] := Module[{e, operator, len, operands, trees, 
      op, result}, If[expr[[0]] === Hold, e = expr, e = Hold[expr]]; 
      If[e[[1,0]] === Integer || e[[1,0]] === Symbol, 
       result = newExpressionTree[ReleaseHold[e], opts], 
       operator = Extract[e, {1, 0}]; 
        len = Length[ReleaseHold[Apply[List, e, {1}]]]; 
        operands = Extract[e, Table[{1, i}, {i, len}], Hold]; 
        trees = Table[expressionTree[op], {op, operands}]; 
        result = joinTrees[operator, trees, opts]]; result]
 
newExpressionTree[r_, opts___] := Module[{T, v}, v = ToString[v]; 
      T = orderedTree[{v}, {}, Association[v -> 0], opts]; 
      PropertyValue[{T, v}, VertexLabels] = Placed[r, Below]; T]
 
orderedTree[V_List, edges:{___Rule | ___DirectedEdge}, order_Association, 
     opts___] := Module[{sortedV, root}, 
     Check[If[ !rootedTreeQ[Graph[V, edges]], Message[orderedTree::argx]], 
       Return[$Failed]]; Check[If[Union[Keys[order]] != Union[V], 
        Message[setChildOrder::argx]], Return[$Failed]]; 
      sortedV = Sort[V, order[#1] < order[#2] & ]; root = sortedV[[1]]; 
      sortedV = (Property[#1, "order" -> order[#1]] & ) /@ sortedV; 
      Graph[sortedV, edges, GraphLayout -> {"LayeredEmbedding", 
         "RootVertex" -> root}, opts]]
 
orderedTree[edges:{___Rule | ___DirectedEdge}, order_Association, opts___] := 
    orderedTree[Union[Flatten[Apply[List, edges, {1}]]], edges, order, opts]
 
orderedTree[g_Graph, order_Association, opts___] := 
    orderedTree[VertexList[g], EdgeList[g], order, opts]
 
orderedTree /: orderedTree::argx = 
     "Vertices and edges do not form a rooted tree."
 
rootedTreeQ[T_Graph] := TreeGraphQ[T] && DirectedGraphQ[T]
 
setChildOrder[(G_)?rootedTreeQ, order_Association] := 
    Module[{T = G, v}, Check[If[Union[Keys[order]] != Union[VertexList[G]], 
        Message[setChildOrder::argx]], Return[$Failed]]; 
      Do[PropertyValue[{T, v}, "order"] = order[v], {v, VertexList[T]}]; T]
 
setChildOrder /: setChildOrder::argx = 
     "Association keys do not match vertices."
 
joinTrees[newR_, trees:{__?orderedRootedTreeQ}, opts___] := 
    Module[{newRI, A, newVerts, oldRoots, Aroot, newEdges, newOrders, newT, 
      v, e, p, w}, newRI = ToString[newRI]; newVerts = 
       Join[{newRI}, Sequence @@ Table[VertexList[A], {A, trees}], 1]; 
      oldRoots = Table[findRoot[A], {A, trees}]; 
      newEdges = Join[Sequence @@ Table[EdgeList[A], {A, trees}], 
        Table[DirectedEdge[newRI, Aroot], {Aroot, oldRoots}]]; 
      newOrders = Join[Sequence @@ Flatten[Table[orderAssociation[A], 
           {A, trees}], 1], Association @@ Table[oldRoots[[i]] -> i, 
          {i, Length[oldRoots]}], Association[newRI -> 0]]; 
      newT = orderedTree[newVerts, newEdges, newOrders, opts]; 
      Do[PropertyValue[{newT, v}, VertexLabels] = PropertyValue[{A, v}, 
         VertexLabels], {A, trees}, {v, VertexList[A]}]; 
      PropertyValue[{newT, newRI}, VertexLabels] = Placed[newR, After]; newT]
 
orderedRootedTreeQ[T_] := Module[{v}, Catch[If[ !rootedTreeQ, Throw[False]]; 
       Do[If[PropertyValue[{T, v}, "order"] === $Failed, Throw[False]], 
        {v, VertexList[T]}]; If[PropertyValue[{T, findRoot[T]}, "order"] != 
         0, Throw[False]]; Throw[True]]]
 
findRoot[(G_)?rootedTreeQ] := VertexList[G][[Position[VertexInDegree[G], 0][[
      1,1]]]]
 
orderAssociation[(T_)?orderedRootedTreeQ] := 
    Module[{v}, Association @@ Table[v -> PropertyValue[{T, v}, "order"], 
       {v, VertexList[T]}]]
 
mtToBitstring[minterm_, variableList_] := Module[{i, bitstring}, 
     bitstring = ConstantArray[Null, Length[variableList]]; 
      For[i = 1, i <= Length[variableList], i++, 
       Which[MemberQ[minterm, variableList[[i]]], bitstring[[i]] = 1, 
        MemberQ[minterm,  !variableList[[i]]], bitstring[[i]] = 0, True, 
        bitstring[[i]] = "-"]]; bitstring]
 
dnfToBitList[dnfExpr_Or, variableList_] := 
    (mtToBitstring[#1, variableList] & ) /@ List @@ dnfExpr
 
dnfToBitList[dnfExpr_And, variableList_] := 
    {mtToBitstring[dnfExpr, variableList]}
 
bitStringToMT[bitstring_, variableList_] := Module[{outList, i}, 
     outList = {}; For[i = 1, i <= Length[variableList], i++, 
       Switch[bitstring[[i]], 1, AppendTo[outList, variableList[[i]]], 0, 
        AppendTo[outList,  !variableList[[i]]], "-", Null]]; And @@ outList]
 
bitListToDNF[bitList_, variableList_] := 
    (bitStringToMT[#1, variableList] & ) /@ Or @@ bitList
 
mergeBitstrings[bit1_, bit2_] := Module[{i, pos, result}, 
     Catch[pos = 0; For[i = 1, i <= Length[bit1], i++, 
        If[bit1[[i]] != bit2[[i]], If[pos == 0, pos = i, Throw[False]]]]; 
       If[pos == 0, Throw[False]]; result = bit1; result[[pos]] = "-"; 
       Throw[result]]]
 
Attributes[nextBitList] = {HoldRest}
 
nextBitList[lastgroups_, coverDict_] := Module[{nextL = {}, primeImps, n, A, 
      B, a, b, m}, primeImps = Flatten[Values[lastgroups], 1]; 
      For[n = 1, n <= Max[Keys[lastgroups]], n++, 
       If[KeyExistsQ[lastgroups, n] && KeyExistsQ[lastgroups, n - 1], 
        A = lastgroups[n - 1]; B = lastgroups[n]; 
         Do[m = mergeBitstrings[a, b]; If[m =!= False, 
            nextL = Union[nextL, {m}]; primeImps = Complement[primeImps, {a, 
                b}]; coverDict[m] = Union[coverDict[a], coverDict[b]]; ], 
          {a, A}, {b, B}]]]; {nextL, primeImps}]
 
initCoverageMatrix[minterms_List, primeImps_List, coverDict_Association] := 
    Module[{M, i, C, j}, M = ConstantArray[0, {Length[primeImps], 
         Length[minterms]}]; For[i = 1, i <= Length[primeImps], i++, 
       C = coverDict[primeImps[[i]]]; Do[M[[i,j]] = 1, {j, C}]]; M]
 
Attributes[updateCT] = {HoldRest}
 
updateCT[newPI_, coverTable_, minterms_, primeImps_] := 
    Module[{newPIbitstring, numRows, numCols, covered, i, remainingRows, 
      remainingCols}, newPIbitstring = primeImps[[newPI]]; 
      {numRows, numCols} = Dimensions[coverTable]; covered = {}; 
      For[i = 1, i <= numCols, i++, If[coverTable[[newPI,i]] == 1, 
        AppendTo[covered, i]]]; remainingRows = Delete[Range[numRows], 
        newPI]; remainingCols = Complement[Range[numCols], covered]; 
      coverTable = coverTable[[remainingRows,remainingCols]]; 
      primeImps = primeImps[[remainingRows]]; 
      minterms = minterms[[remainingCols]]; newPIbitstring]
 
findEssentials[coverTable_List] := Module[{essentials = {}, r, c, i, j, 
      rowhas1}, {r, c} = Dimensions[coverTable]; For[i = 1, i <= c, i++, 
       rowhas1 = 0; For[j = 1, j <= r, j++, If[coverTable[[j,i]] == 1, 
          If[rowhas1 == 0, rowhas1 = j, rowhas1 = -1; Break[]]]]; 
        If[rowhas1 > 0, AppendTo[essentials, rowhas1]]]; 
      Sort[Union[essentials], Greater]]
 
findBestImp[coverTable_] := Module[{maxCoverage = 0, bestImp = 0, i, j, sum}, 
     For[i = 1, i <= Dimensions[coverTable][[1]], i++, 
       sum = Plus @@ coverTable[[i]]; If[sum > maxCoverage, 
         maxCoverage = sum; bestImp = i]]; bestImp]
 
quineMcCluskey[F_, variables_] := Module[{fBits, fBitsL, coverageDict, 
      groupsL, primesL, newFbits, newprimes, i, allprimeImps, j, 
      coverageTable, essentialPIs, minBits, nextPI}, 
     fBits = dnfToBitList[F, variables]; coverageDict = PositionIndex[fBits]; 
      i = 0; fBitsL = {fBits}; groupsL = {}; primesL = {}; 
      While[fBitsL[[-1]] =!= {}, AppendTo[groupsL, GroupBy[fBitsL[[-1]], 
          Count[1]]]; {newFbits, newprimes} = nextBitList[groupsL[[-1]], 
          coverageDict]; AppendTo[fBitsL, newFbits]; AppendTo[primesL, 
         newprimes]; ]; allprimeImps = Union @@ primesL; 
      coverageTable = initCoverageMatrix[fBits, allprimeImps, coverageDict]; 
      essentialPIs = findEssentials[coverageTable]; minBits = {}; 
      Do[AppendTo[minBits, updateCT[i, coverageTable, fBits, allprimeImps]], 
       {i, essentialPIs}]; While[MatrixQ[coverageTable] && 
        Dimensions[coverageTable][[2]] > 0, 
       nextPI = findBestImp[coverageTable]; AppendTo[minBits, 
         updateCT[nextPI, coverageTable, fBits, allprimeImps]]]; 
      bitListToDNF[minBits, variables]]
 
quineMcCluskeycountCT[F_, variables_] := 
    Module[{fBits, fBitsL, coverageDict, groupsL, primesL, newFbits, 
      newprimes, i, allprimeImps, j, coverageTable, essentialPIs, minBits, 
      nextPI, count = 0}, fBits = dnfToBitList[F, variables]; 
      coverageDict = PositionIndex[fBits]; i = 0; fBitsL = {fBits}; 
      groupsL = {}; primesL = {}; While[fBitsL[[-1]] =!= {}, 
       AppendTo[groupsL, GroupBy[fBitsL[[-1]], Count[1]]]; 
        {newFbits, newprimes} = nextBitList[groupsL[[-1]], coverageDict]; 
        AppendTo[fBitsL, newFbits]; AppendTo[primesL, newprimes]; ]; 
      allprimeImps = Union @@ primesL; coverageTable = 
       initCoverageMatrix[fBits, allprimeImps, coverageDict]; 
      essentialPIs = findEssentials[coverageTable]; minBits = {}; 
      Do[AppendTo[minBits, updateCT[i, coverageTable, fBits, allprimeImps]]; 
        count++, {i, essentialPIs}]; While[MatrixQ[coverageTable] && 
        Dimensions[coverageTable][[2]] > 0, 
       nextPI = findBestImp[coverageTable]; AppendTo[minBits, 
         updateCT[nextPI, coverageTable, fBits, allprimeImps]]]; 
      bitListToDNF[minBits, variables]; count]
