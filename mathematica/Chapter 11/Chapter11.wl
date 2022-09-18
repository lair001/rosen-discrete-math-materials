rootedTreeQ[T_Graph] := TreeGraphQ[T] && DirectedGraphQ[T]
 
findRoot[(G_)?rootedTreeQ] := VertexList[G][[Position[VertexInDegree[G], 0][[
      1,1]]]]
 
rootedTreePlot[(G_)?rootedTreeQ, opts___] := TreePlot[G, Top, findRoot[G], 
     opts]
 
parentQ[(T_)?rootedTreeQ, p_, c_] := EdgeQ[T, DirectedEdge[p, c]]
 
findParent[(T_)?rootedTreeQ, v_] := Module[{P, p}, 
     P = Cases[EdgeList[T], DirectedEdge[p_, v] -> p]; 
      If[Length[P] != 1, Null, P[[1]]]]
 
findChildren[(T_)?rootedTreeQ, v_] := Module[{c}, Cases[EdgeList[T], 
      DirectedEdge[v, c_] -> c]]
 
internalVertexQ[(T_)?rootedTreeQ, v_] := Length[findChildren[T, v]] != 0
 
leafQ[(T_)?rootedTreeQ, v_] := Length[findChildren[T, v]] == 0
 
findLeaves[(T_)?rootedTreeQ] := Module[{V}, V = VertexList[T]; 
      Select[V, leafQ[T, #1] & ]]
 
setChildOrder[(G_)?rootedTreeQ, order_Association] := 
    Module[{T = G, v}, Check[If[Union[Keys[order]] != Union[VertexList[G]], 
        Message[setChildOrder::argx]], Return[$Failed]]; 
      Do[PropertyValue[{T, v}, "order"] = order[v], {v, VertexList[T]}]; T]
 
setChildOrder /: setChildOrder::argx = 
     "Association keys do not match vertices."
 
orderedRootedTreeQ[T_] := Module[{v}, Catch[If[ !rootedTreeQ, Throw[False]]; 
       Do[If[PropertyValue[{T, v}, "order"] === $Failed, Throw[False]], 
        {v, VertexList[T]}]; If[PropertyValue[{T, findRoot[T]}, "order"] != 
         0, Throw[False]]; Throw[True]]]
 
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
 
orderAssociation[(T_)?orderedRootedTreeQ] := 
    Module[{v}, Association @@ Table[v -> PropertyValue[{T, v}, "order"], 
       {v, VertexList[T]}]]
 
findLevel[(T_)?rootedTreeQ, V_] := Module[{v, level}, 
     level = 0; v = V; While[findParent[T, v] =!= Null, 
       level++; v = findParent[T, v]]; level]
 
findHeight[(T_)?rootedTreeQ] := Module[{v, height, level}, 
     height = 0; Do[level = findLevel[T, v]; If[level > height, 
         height = level], {v, VertexList[T]}]; height]
 
balancedTreeQ[(T_)?rootedTreeQ] := Module[{height, leaves, v}, 
     height = findHeight[T]; leaves = findLeaves[T]; 
      Catch[Do[If[findLevel[T, v] < height - 1, Throw[False]], {v, leaves}]; 
        Throw[True]]]
 
binaryTreeQ[T_Graph] := Module[{R, v, vpos}, 
     Catch[If[ !orderedRootedTreeQ[T], Throw[False]]; R = findRoot[T]; 
       Do[If[VertexOutDegree[T, v] > 2, Throw[False]]; 
          vpos = PropertyValue[{T, v}, "order"]; If[(vpos == 0 && v != R) || 
            (vpos != 0 && vpos != 1 && vpos != 2), Throw[False]], 
         {v, VertexList[T]}]*Throw[True]]]
 
Attributes[drawBinaryTree] = {HoldFirst}
 
drawBinaryTree[(T_)?binaryTreeQ] := Module[{height, v, i, level, verts, x, y, 
      parent, side}, PropertyValue[T, VertexCoordinates] = GraphEmbedding[T]; 
      height = findHeight[T]; v = findRoot[T]; 
      PropertyValue[{T, v}, VertexCoordinates] = {1/2, 1}; 
      verts = findChildren[T, v]; i = 1; While[i <= Length[verts], 
       v = verts[[i]]; level = findLevel[T, v]; y = 1 - level/height; 
        parent = findParent[T, v]; x = PropertyValue[{T, parent}, 
           VertexCoordinates][[1]]; side = Switch[PropertyValue[{T, v}, 
           "order"], 1, -1, 2, 1]; x = x + side*(1/2^(level + 1)); 
        PropertyValue[{T, v}, VertexCoordinates] = {x, y}; 
        verts = Join[verts, findChildren[T, v]]; i++]; T]
 
binaryTree[V_List, edges:{___Rule | ___DirectedEdge}, order_Association, 
     opts___] := Module[{T}, T = orderedTree[V, edges, order, opts]; 
      Check[If[ !binaryTreeQ[T], Message[binaryTree::argx]], 
       Return[$Failed]]; drawBinaryTree[T]]
 
binaryTree[edges:{___Rule | ___DirectedEdge}, order_Association, opts___] := 
    binaryTree[Union[Flatten[Apply[List, edges, {1}]]], edges, order, opts]
 
binaryTree[g_Graph, order_Association, opts___] := 
    binaryTree[VertexList[g], EdgeList[g], order, opts]
 
binaryTree /: binaryTree::argx = "Arguments do not form a binary tree."
 
findLeftChild[(T_)?binaryTreeQ, v_] /; VertexQ[T, v] := 
    Module[{children, w, pos}, children = findChildren[T, v]; 
      Catch[Do[pos = PropertyValue[{T, w}, "order"]; If[pos == 1, Throw[w]], 
         {w, children}]; Throw[Null]]]
 
findRightChild[(T_)?binaryTreeQ, v_] /; VertexQ[T, v] := 
    Module[{children, w, pos}, children = findChildren[T, v]; 
      Catch[Do[pos = PropertyValue[{T, w}, "order"]; If[pos == 2, Throw[w]], 
         {w, children}]; Throw[Null]]]
 
newBinaryTree[r_, opts___] := binaryTree[{r}, {}, Association[r -> 0], opts]
 
addLeftChild[(T_)?binaryTreeQ, v_, newV_] /; VertexQ[T, v] := 
    Module[{vertexL, edgeL, orderA}, If[findLeftChild[T, v] != Null, 
       Return[$Failed]]; vertexL = Append[VertexList[T], newV]; 
      edgeL = Append[EdgeList[T], DirectedEdge[v, newV]]; 
      orderA = Append[orderAssociation[T], newV -> 1]; 
      binaryTree[vertexL, edgeL, orderA]]
 
addRightChild[(T_)?binaryTreeQ, v_, newV_] /; VertexQ[T, v] := 
    Module[{vertexL, edgeL, orderA}, If[findRightChild[T, v] != Null, 
       Return[$Failed]]; vertexL = Append[VertexList[T], newV]; 
      edgeL = Append[EdgeList[T], DirectedEdge[v, newV]]; 
      orderA = Append[orderAssociation[T], newV -> 2]; 
      binaryTree[vertexL, edgeL, orderA]]
 
Attributes[binaryInsertion] = {HoldFirst}
 
binaryInsertion[(BST_)?binaryTreeQ, x_] := 
    Module[{v}, v = findRoot[BST]; While[v =!= Null && v != x, 
       If[Order[x, v] == 1, If[findLeftChild[BST, v] === Null, 
         BST = addLeftChild[BST, v, x]; v = Null, v = findLeftChild[BST, v]], 
        If[findRightChild[BST, v] === Null, BST = addRightChild[BST, v, x]; 
          v = Null, v = findRightChild[BST, v]]]]; v =!= Null]
 
makeBST[L_List, opts___] := Module[{T, v}, T = newBinaryTree[L[[1]]]; 
      Do[binaryInsertion[T, L[[i]]], {i, 2, Length[L]}]; T = Graph[T, opts]]
 
newHTree[s_, w_, opts___] := Module[{T}, T = newBinaryTree[s]; 
      PropertyValue[T, "weight"] = w; Graph[T, opts]]
 
createForest[L_List, opts___] := Module[{forest = {}, M, v, w, G}, 
     Do[{v, w} = M; AppendTo[forest, newHTree[v, w, opts]], {M, L}]; forest]
 
compareTrees[(A_)?binaryTreeQ, (B_)?binaryTreeQ] := 
    Module[{a, b}, a = PropertyValue[A, "weight"]; 
      b = PropertyValue[B, "weight"]; a < b]
 
joinHTrees[newR_, (A_)?binaryTreeQ, (B_)?binaryTreeQ, opts___] := 
    Module[{newT, newVerts, Aroot, Broot, newEdges, newOrders, v, e, p, w}, 
     newVerts = Join[{newR}, VertexList[A], VertexList[B]]; 
      Aroot = findRoot[A]; Broot = findRoot[B]; 
      newEdges = Join[EdgeList[A], EdgeList[B], {DirectedEdge[newR, Aroot], 
         DirectedEdge[newR, Broot]}]; newOrders = Join[orderAssociation[A], 
        orderAssociation[B], Association[newR -> 0, Aroot -> 1, Broot -> 2]]; 
      newT = binaryTree[newVerts, newEdges, newOrders, opts]; 
      Do[PropertyValue[{newT, e}, EdgeLabels] = PropertyValue[{A, e}, 
         EdgeLabels], {e, EdgeList[A]}]; 
      Do[PropertyValue[{newT, e}, EdgeLabels] = PropertyValue[{B, e}, 
         EdgeLabels], {e, EdgeList[B]}]; 
      PropertyValue[{newT, DirectedEdge[newR, Aroot]}, EdgeLabels] = 
       Placed[0, {0.5, {1, 0}}]; 
      PropertyValue[{newT, DirectedEdge[newR, Broot]}, EdgeLabels] = 
       Placed[1, {0.5, {-1, 0}}]; w = PropertyValue[A, "weight"] + 
        PropertyValue[B, "weight"]; PropertyValue[newT, "weight"] = w; newT]
 
huffmanCode[L_List, opts___] := Module[{F, i, tempT}, 
     F = createForest[L, opts]; i = 0; While[Length[F] > 1, 
       F = Sort[F, compareTrees]; i++; tempT = joinHTrees[
          StringJoin["I", ToString[i]], F[[2]], F[[1]], opts]; 
        F = Append[F[[3 ;; -1]], tempT]]; F[[1]]]
 
encodeCharacter[(H_)?binaryTreeQ, c_String] /; StringLength[c] == 1 := 
    Module[{code = "", vertex, digit}, vertex = c; 
      While[findParent[H, vertex] =!= Null, 
       digit = PropertyValue[{H, vertex}, "order"] - 1; 
        code = StringJoin[ToString[digit], code]; 
        vertex = findParent[H, vertex]; ]; code]
 
encodeString[(H_)?binaryTreeQ, S_String] := Module[{char}, 
     StringJoin[Table[encodeCharacter[H, char], {char, Characters[S]}]]]
 
descendants[(T_)?rootedTreeQ, parent_] := Module[{dList, v, i}, 
     dList = findChildren[T, parent]; i = 1; While[i <= Length[dList], 
       v = dList[[i]]; dList = Join[dList, findChildren[T, v]]; i++]; dList]
 
subTree[(T_)?orderedRootedTreeQ, newRoot_, opts___] := 
    Module[{vList, subT, v}, vList = descendants[T, newRoot]; 
      PrependTo[vList, newRoot]; subT = Subgraph[T, vList, opts]; 
      Do[PropertyValue[{subT, v}, "order"] = PropertyValue[{T, v}, "order"], 
       {v, vList}]; PropertyValue[{subT, newRoot}, "order"] = 0; subT]
 
preorder[(T_)?orderedRootedTreeQ] := Module[{root, children, i, tempSubT}, 
     Reap[root = findRoot[T]; Sow[root]; children = findChildren[T, root]; 
        children = Sort[children, PropertyValue[{T, #1}, "order"] < 
            PropertyValue[{T, #2}, "order"] & ]; For[i = 1, 
         i <= Length[children], i++, tempSubT = subTree[T, children[[i]]]; 
          Sow[preorder[tempSubT]]; ]][[2,1]]]
 
preorderAnimation[(T_)?orderedRootedTreeQ] := Module[{traversal}, 
     traversal = Flatten[preorder[T]]; Animate[HighlightGraph[T, 
        traversal[[1 ;; i]]], {{i, 0, "step"}, 0, Length[traversal], 1}, 
       AnimationRunning -> False, AnimationRepetitions -> 1]]
 
postorder[(T_)?orderedRootedTreeQ] := Module[{root, children, i, tempSubT}, 
     Reap[root = findRoot[T]; children = findChildren[T, root]; 
        children = Sort[children, PropertyValue[{T, #1}, "order"] < 
            PropertyValue[{T, #2}, "order"] & ]; For[i = 1, 
         i <= Length[children], i++, tempSubT = subTree[T, children[[i]]]; 
          Sow[postorder[tempSubT]]; ]; Sow[root]][[2,1]]]
 
inorder[(T_)?orderedRootedTreeQ] := Module[{root, children, i, tempSubT}, 
     Reap[root = findRoot[T]; children = findChildren[T, root]; 
        children = Sort[children, PropertyValue[{T, #1}, "order"] < 
            PropertyValue[{T, #2}, "order"] & ]; If[Length[children] != 0, 
         tempSubT = subTree[T, children[[1]]]; Sow[inorder[tempSubT]]]; 
        Sow[root]; For[i = 2, i <= Length[children], i++, 
         tempSubT = subTree[T, children[[i]]]; Sow[inorder[tempSubT]]; ]][[2,
      1]]]
 
newExpressionTree[r_, opts___] := Module[{T, v}, v = ToString[v]; 
      T = orderedTree[{v}, {}, Association[v -> 0], opts]; 
      PropertyValue[{T, v}, VertexLabels] = Placed[r, Below]; T]
 
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
 
evalPostfix[expr_List] := Module[{i, L}, L = expr; While[Length[L] > 1, 
       i = 1; While[FreeQ[{"+", "-", "*", "/", "^"}, L[[i]]], i++]; 
        Switch[L[[i]], "+", L[[i]] = L[[i - 2]] + L[[i - 1]], "-", 
         L[[i]] = L[[i - 2]] - L[[i - 1]], "*", 
         L[[i]] = L[[i - 2]]*L[[i - 1]], "/", L[[i]] = L[[i - 2]]/L[[i - 1]], 
         "^", L[[i]] = L[[i - 2]]^L[[i - 1]]]; L = Drop[L, {i - 2, i - 1}]]; 
      L[[1]]]
 
depthSearch[(G_)?UndirectedGraphQ, startV_, opts___] := 
    Module[{toVisit, exploring, T, v, N, w}, 
     If[ !ConnectedGraphQ[G], Return[$Failed]]; 
      toVisit = Complement[VertexList[G], {startV}]; exploring = {startV}; 
      T = Graph[VertexList[G], {}, opts]; While[Length[exploring] > 0, 
       v = exploring[[-1]]; N = Intersection[AdjacencyList[G, v], toVisit]; 
        If[Length[N] > 0, w = N[[1]]; T = EdgeAdd[T, DirectedEdge[v, w]]; 
          toVisit = Complement[toVisit, {w}]; AppendTo[exploring, w], 
         exploring = Delete[exploring, -1]]]; T]
 
breadthSearch[(G_)?UndirectedGraphQ, startV_, opts___] := 
    Module[{toVisit, toProcess, T, v, N, w}, 
     If[ !ConnectedGraphQ[G], Return[$Failed]]; 
      toVisit = Complement[VertexList[G], {startV}]; toProcess = {startV}; 
      T = Graph[VertexList[G], {}, opts]; While[Length[toProcess] > 0, 
       v = toProcess[[1]]; N = Intersection[AdjacencyList[G, v], toVisit]; 
        Do[T = EdgeAdd[T, DirectedEdge[v, w]]; AppendTo[toProcess, w]; 
          toVisit = Complement[toVisit, {w}]; , {w, N}]; 
        toProcess = Delete[toProcess, 1]; ]; T]
 
backColor[G_Graph, C_List] := Module[{verts, numverts, allcolorsL, k, 
      coloring, i, N, j, used, available, g}, verts = VertexList[G]; 
      numverts = Length[verts]; allcolorsL = Range[Length[C]]; 
      coloring = {1}; i = 2; While[i > 1 && i <= numverts, 
       N = VertexList[NeighborhoodGraph[G, verts[[i]]]]; used = {}; 
        For[j = 1, j <= i - 1, j++, If[MemberQ[N, verts[[j]]], 
           AppendTo[used, coloring[[j]]]]; ]; If[Length[coloring] >= i, 
         used = Union[used, Range[coloring[[i]]]]]; 
        available = Complement[allcolorsL, used]; If[Length[available] > 0, 
         coloring = Append[coloring[[1 ;; i - 1]], First[available]]; i++, 
         If[Length[coloring] >= i, coloring = coloring[[1 ;; i - 1]]]; i--]]; 
      If[i > numverts, g = G; For[k = 1, k <= numverts, k++, 
         PropertyValue[{g, verts[[k]]}, VertexStyle] = C[[coloring[[k]]]]]; 
        Return[g], Return[$Failed]]]
 
backColorDT[G_Graph, C_List] := Module[{verts, numverts, allcolorsL, k, 
      coloring, i, N, j, used, available, DTList, parentV, newV}, 
     verts = VertexList[G]; numverts = Length[verts]; 
      allcolorsL = Range[Length[C]]; coloring = {1}; 
      newV = ToString[coloring]; DTList = {}; i = 2; 
      While[i > 1 && i <= numverts, 
       N = VertexList[NeighborhoodGraph[G, verts[[i]]]]; used = {}; 
        For[j = 1, j <= i - 1, j++, If[MemberQ[N, verts[[j]]], 
           AppendTo[used, coloring[[j]]]]; ]; If[Length[coloring] >= i, 
         used = Union[used, Range[coloring[[i]]]]]; 
        available = Complement[allcolorsL, used]; If[Length[available] > 0, 
         parentV = ToString[coloring[[1 ;; i - 1]]]; coloring = 
           Append[coloring[[1 ;; i - 1]], First[available]]; 
          newV = ToString[coloring]; AppendTo[DTList, parentV -> newV]; i++, 
         If[Length[coloring] >= i, coloring = coloring[[1 ;; i - 1]]]; i--]]; 
      Graph[DTList, VertexLabels -> "Name", GraphLayout -> 
        "LayeredDigraphEmbedding"]]
 
boardStatus[queenList_List, dim_Integer] := 
    Module[{board, i, dif, qRank, qFile, vQueens}, 
     board = ConstantArray[1, {dim, dim}]; For[qFile = 1, 
       qFile <= Length[queenList], qFile++, qRank = queenList[[qFile]]; 
        For[i = 1, i <= dim, i++, board[[qRank,i]] = 0; board[[i,qFile]] = 0; 
          dif = i - qFile; If[qRank + dif <= dim && qRank + dif >= 1, 
           board[[qRank + dif,i]] = 0]; If[qRank - dif <= dim && 
            qRank - dif >= 1, board[[qRank - dif,i]] = 0]]]; 
      For[qFile = 1, qFile <= Length[queenList], qFile++, 
       board[[queenList[[qFile]],qFile]] = "Q"]; board]
 
validQueens[queenList_List, dim_Integer] := Module[{board, file, i, freeSet}, 
     board = boardStatus[queenList, dim]; file = Length[queenList] + 1; 
      freeSet = {}; For[i = 1, i <= dim, i++, If[board[[i,file]] == 1, 
        AppendTo[freeSet, i]]]; freeSet]
 
nQueens[boardDim_Integer] /; boardDim > 0 := 
    Module[{queens = {}, file = 1, open, i}, 
     While[file > 0 && file <= boardDim, 
       open = validQueens[queens[[1 ;; file - 1]], boardDim]; 
        If[Length[queens] >= file, open = Complement[open, 
           Range[queens[[file]]]]]; If[open != {}, 
         queens = Join[queens[[1 ;; file - 1]], {open[[1]]}]; file++, 
         queens = queens[[1 ;; file - 1]]; file--]]; 
      If[file > boardDim, Return[MatrixForm[boardStatus[queens, boardDim]]], 
       Return[$Failed]]]
 
subsetSum[S:{__Integer}, M_Integer] := Module[{bIndices, allIndices, i, 
      availIndices, k, currentSum}, bIndices = {}; 
      allIndices = Range[Length[S]]; i = 1; currentSum = 0; 
      While[i > 0 && currentSum != M, availIndices = Complement[allIndices, 
          bIndices]; If[Length[bIndices] >= i, availIndices = 
          Complement[availIndices, Range[bIndices[[i]]]]]; 
        Do[If[currentSum + S[[k]] > M, availIndices = Complement[
            availIndices, {k}]], {k, availIndices}]; If[availIndices != {}, 
         bIndices = Append[bIndices[[1 ;; i - 1]], availIndices[[1]]]; i++, 
         If[Length[bIndices] >= i, bIndices = bIndices[[1 ;; i - 1]]]; i--]; 
        currentSum = Plus @@ S[[bIndices[[1 ;; i - 1]]]]]; 
      If[i == 0, Return[$Failed], Return[S[[bIndices]]]]]
 
edgeCompare[G_] := Function[{e1, e2}, PropertyValue[{G, e1}, EdgeWeight] < 
      PropertyValue[{G, e2}, EdgeWeight]]
 
minEdge[G_Graph, V_List] := Module[{possibleEdges, i}, 
     If[V == {}, possibleEdges = EdgeList[G], 
       possibleEdges = EdgeList[NeighborhoodGraph[G, V]]; i = 1; 
        While[i <= Length[possibleEdges], 
         If[MemberQ[V, possibleEdges[[i]][[1]]] == MemberQ[V, 
            possibleEdges[[i]][[2]]], possibleEdges = Delete[possibleEdges, 
            i], i++]]]; If[possibleEdges == {}, Return[Null]]; 
      possibleEdges = Sort[possibleEdges, edgeCompare[G]]; possibleEdges[[1]]]
 
prim[G_Graph, opts___] := Module[{newEdge, T, n, i, v}, 
     newEdge = minEdge[G, {}]; T = Graph[{newEdge}, opts]; 
      PropertyValue[{T, newEdge}, EdgeWeight] = PropertyValue[{G, newEdge}, 
        EdgeWeight]; PropertyValue[{T, newEdge}, EdgeLabels] = 
       PropertyValue[{G, newEdge}, EdgeWeight]; n = VertexCount[G]; 
      For[i = 1, i <= n - 2, i++, newEdge = minEdge[G, VertexList[T]]; 
        If[VertexQ[T, newEdge[[1]]], T = VertexAdd[T, newEdge[[2]]], 
         T = VertexAdd[T, newEdge[[1]]]]; T = EdgeAdd[T, newEdge]; 
        PropertyValue[{T, newEdge}, EdgeWeight] = PropertyValue[{G, newEdge}, 
          EdgeWeight]; PropertyValue[{T, newEdge}, EdgeLabels] = 
         PropertyValue[{G, newEdge}, EdgeWeight]]; T]
 
primEdges[G_Graph] := Module[{newEdge, T, edgeList, n, i, v}, 
     newEdge = minEdge[G, {}]; T = Graph[{newEdge}]; edgeList = {newEdge}; 
      n = VertexCount[G]; For[i = 1, i <= n - 2, i++, 
       newEdge = minEdge[G, VertexList[T]]; If[VertexQ[T, newEdge[[1]]], 
         T = VertexAdd[T, newEdge[[2]]], T = VertexAdd[T, newEdge[[1]]]]; 
        T = EdgeAdd[T, newEdge]; AppendTo[edgeList, newEdge]]; edgeList]
 
animateTree[G_Graph, T_List, opts___] := Module[{i, len}, 
     len = Length[T]; Animate[HighlightGraph[G, T[[1 ;; i]], opts], 
       {{i, 0, "step"}, 0, len, 1}, AnimationRunning -> False, 
       AnimationRepetitions -> 1]]
 
noCircuitQ[G_Graph, edge_] := Module[{components, C}, 
     components = ConnectedComponents[G]; 
      Catch[Do[If[MemberQ[C, edge[[1]]] && MemberQ[C, edge[[2]]], 
          Throw[False]], {C, components}]; Throw[True]]]
 
kruskal[G_Graph, opts___] := Module[{edges, T, n, i, newEdge, v}, 
     edges = Sort[EdgeList[G], edgeCompare[G]]; 
      T = Graph[VertexList[G], {}, opts]; n = VertexCount[G]; i = 1; 
      While[i <= n - 1, newEdge = edges[[1]]; If[noCircuitQ[T, newEdge], 
         T = EdgeAdd[T, newEdge]; PropertyValue[{T, newEdge}, EdgeWeight] = 
           PropertyValue[{G, newEdge}, EdgeWeight]; 
          PropertyValue[{T, newEdge}, EdgeLabels] = PropertyValue[
            {G, newEdge}, EdgeWeight]; i++]; edges = Delete[edges, 1]]; T]
 
kruskalEdges[G_Graph] := Module[{edges, edgeList, T, n, i, newEdge, v}, 
     edges = Sort[EdgeList[G], edgeCompare[G]]; edgeList = {}; 
      T = Graph[VertexList[G], {}]; n = VertexCount[G]; i = 1; 
      While[i <= n - 1, newEdge = edges[[1]]; If[noCircuitQ[T, newEdge], 
         T = EdgeAdd[T, newEdge]; AppendTo[edgeList, newEdge]; i++]; 
        edges = Delete[edges, 1]]; edgeList]
 
treeFromList[L_List, opts___] := Module[{T, e, curParent, childOrder, 
      thisEdge}, T = Graph[L, opts]; PropertyValue[{T, findRoot[T]}, 
        "order"] = 0; curParent = findRoot[T]; childOrder = 1; 
      Do[If[thisEdge[[1]] != curParent, curParent = thisEdge[[1]]; 
          childOrder = 1]; PropertyValue[{T, thisEdge[[2]]}, "order"] = 
         childOrder; childOrder++, {thisEdge, L}]; T]
 
universalAddress[edgeList_List, opts___] := 
    Module[{G}, G = treeFromList[edgeList, opts]; BreadthFirstScan[G, 
       findRoot[G], {"DiscoverVertex" -> 
         ((If[PropertyValue[{G, #2}, "order"] == 0, 
            PropertyValue[{G, #1}, "univ-address"] = ToString[
              PropertyValue[{G, #1}, "order"]], PropertyValue[{G, #1}, 
              "univ-address"] = StringJoin[PropertyValue[{G, #2}, 
               "univ-address"], ".", ToString[PropertyValue[{G, #1}, 
                "order"]]]]; PropertyValue[{G, #1}, VertexLabels] = 
            PropertyValue[{G, #1}, "univ-address"]) & )}]; G]
 
extendTrees[trees_List] := Module[{newTrees, newV, T, v, newT}, 
     newTrees = {}; newV = VertexCount[trees[[1]]] + 1; 
      Do[Do[newT = VertexAdd[T, newV]; newT = EdgeAdd[newT, v -> newV]; 
         AppendTo[newTrees, newT], {v, VertexList[T]}], {T, trees}]; newTrees]
 
movePiece[board_List, side_Integer] := Module[{newBoards = {}, direction, r, 
      c, isKing, king, rowDir, colDir, newB}, 
     direction = Switch[side, 1, -1, 2, 1]; For[r = 1, r <= 4, r++, 
       For[c = 1, c <= 4, c++, If[Abs[board[[r,c]]] == side, 
         If[board[[r,c]] < 0, isKing = 1, isKing = 0]; For[king = 0, 
           king <= isKing, king++, rowDir = Switch[king, 0, direction, 1, 
              -direction]; If[r + rowDir >= 1 && r + rowDir <= 4, 
             For[colDir = -1, colDir <= 1, colDir = colDir + 2, 
              If[c + colDir >= 1 && c + colDir <= 4, Which[board[[r + rowDir,
                  c + colDir]] == 0, newB = board; If[((r + rowDir == 1 && 
                     side == 1) || (r + rowDir == 4 && side == 2)) && 
                   board[[r,c]] > 0, newB[[r + rowDir,c + colDir]] = 
                   -board[[r,c]], newB[[r + rowDir,c + colDir]] = board[[r,
                    c]]]; newB[[r,c]] = 0; AppendTo[newBoards, newB], 
                Abs[board[[r + rowDir,c + colDir]]] != side, 
                If[r + 2*rowDir >= 1 && r + 2*rowDir <= 4 && c + 2*colDir >= 
                   1 && c + 2*colDir <= 4, If[board[[r + 2*rowDir,
                    c + 2*colDir]] == 0, newB = board; If[((r + 2*rowDir == 
                        1 && side == 1) || (r + 2*rowDir == 4 && side == 
                        2)) && board[[r,c]] > 0, newB[[r + 2*rowDir,
                      c + 2*colDir]] = -board[[r,c]], newB[[r + 2*rowDir,
                      c + 2*colDir]] = board[[r,c]]]; newB[[r,c]] = 0; 
                   newB[[r + rowDir,c + colDir]] = 0; AppendTo[newBoards, 
                    newB]]]]]]]]]]]; newBoards]
