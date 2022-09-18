neighbors[g_Graph, v_] := Union[Cases[EdgeList[g], 
      DirectedEdge[v, x_] | DirectedEdge[x_, v] | UndirectedEdge[v, x_] | 
        UndirectedEdge[x_, v] :> x]]
 
drawBipartite[g_Graph, opts___] := Module[{V, AB, i, T, w, e}, 
     V = VertexList[g]; w = V[[1]]; AB[0] = {w}; AB[1] = {}; i = 0; 
      While[V != {}, T = Intersection[V, AB[i]]; i = Mod[i + 1, 2]; 
        Do[AB[i] = Union[AB[i], Complement[neighbors[g, w], 
            Union[AB[0], AB[1]]]], {w, T}]; V = Complement[V, T]]; 
      Catch[Do[If[(MemberQ[AB[0], e[[1]]] && MemberQ[AB[0], e[[2]]]) || 
           (MemberQ[AB[1], e[[1]]] && MemberQ[AB[1], e[[2]]]), Throw[False]], 
         {e, EdgeList[g]}]; Graph[g, VertexStyle -> 
          Union[Table[i -> Green, {i, AB[0]}], Table[i -> Yellow, 
            {i, AB[1]}]], VertexShapeFunction -> Table[i -> "Square", 
           {i, AB[0]}], opts]]]
 
adjacencyList[G_Graph] := Association @@ Table[v -> AdjacencyList[G, v], 
      {v, VertexList[G]}]
 
adjacencyRuleQ[r_Rule] := ListQ[r[[2]]]
 
adjacencyListGraph[A:Association[__?adjacencyRuleQ], opts___] := 
    Module[{V, n, D, rules, v, w}, V = Union[Keys[A], Flatten[Values[A]]]; 
      n = Length[V]; D = Association[MapThread[Rule, {V, Range[n]}]]; 
      rules = Flatten[Table[{D[v], D[w]} -> 1, {v, Keys[A]}, {w, A[v]}]]; 
      AdjacencyGraph[SparseArray[rules, {n, n}], opts]]
 
checkInvariants[G1_Graph, G2_Graph] := Module[{notIsomorphic = False}, 
     If[VertexCount[G1] != VertexCount[G2], notIsomorphic = True; 
        Print["Different numbers of vertices."]]; 
      If[EdgeCount[G1] != EdgeCount[G2], notIsomorphic = True; 
        Print["Different numbers of edges."]]; 
      If[ !(Equivalent[DirectedGraphQ[G1], DirectedGraphQ[G2]]), 
       notIsomorphic = True; Print["One is directed, one is undirected."]]; 
      If[ !(Equivalent[BipartiteGraphQ[G1], BipartiteGraphQ[G2]]), 
       notIsomorphic = True; Print["One is bipartite, one is not."]]; 
      If[Sort[VertexDegree[G1]] != Sort[VertexDegree[G2]], 
       notIsomorphic = True; Print["Degree sequences do not match."]]; 
      If[notIsomorphic, Print["The graphs are not isomorphic."], 
       Print["The graphs MAY be isomorphic."]]]
 
highlightComponents[G_Graph, opts___] := Module[{components, c, i, v, H = G}, 
     components = ConnectedComponents[G]; c = 0; 
      For[i = 1, i <= Length[components], i++, c = Mod[c + 1, 10, 1]; 
        Do[PropertyValue[{H, v}, VertexStyle] = ColorData[14][c], 
         {v, components[[i]]}]]; Graph[H, opts]]
 
animatePath[g_Graph, p_List] := Module[{i, len}, len = Length[p]; 
      Animate[HighlightGraph[g, p[[1 ;; i]]], {{i, 0, "step"}, 0, len, 1}, 
       AnimationRunning -> False, AnimationRepetitions -> 1]]
 
eulerPathQ[g_Graph] := UndirectedGraphQ[g] && ConnectedGraphQ[g] && 
     MemberQ[{0, 2}, Count[EvenQ /@ VertexDegree[g], False]]
 
findEulerianPath[g_Graph] := Module[{H, pathQ, oddvertices, newvertex, 
      circuit, subC, i, n, v, insertPoint, w, buildingSub, oldC, 
      newVlocations}, If[ !eulerPathQ[g], Return[$Failed]]; circuit = {}; 
      H = g; If[Count[EvenQ /@ VertexDegree[g], False] == 2, 
       pathQ = True; oddvertices = Select[VertexList[g], 
          OddQ[VertexDegree[g, #1]] & ]; H = VertexAdd[H, newvertex]; 
        H = EdgeAdd[H, {newvertex -> oddvertices[[1]], newvertex -> 
            oddvertices[[2]]}], pathQ = False]; While[EdgeList[H] != {}, 
       If[circuit == {}, subC = {EdgeList[H][[1]]}; 
          H = EdgeDelete[H, subC[[1]]]; insertPoint = 0, 
         For[i = 1, i <= Length[circuit], i++, v = circuit[[i,2]]; 
           n = neighbors[H, v]; If[n != {}, w = n[[1]]; subC = {v -> w}; 
             insertPoint = i; H = EdgeDelete[H, UndirectedEdge[v, w]]; 
             Break[]]]]; buildingSub = True; 
        While[buildingSub && EdgeList[H] != {}, v = subC[[-1,2]]; 
          w = First[neighbors[H, v]]; H = EdgeDelete[H, UndirectedEdge[v, 
             w]]; AppendTo[subC, UndirectedEdge[v, w]]; If[w == subC[[1,1]], 
           buildingSub = False]]; If[circuit == {}, circuit = subC, 
         circuit = Flatten[Insert[circuit, subC, insertPoint + 1]]]]; 
      If[pathQ, newVlocations = Position[circuit, newvertex][[All,1]]; 
        Join[circuit[[Max[newVlocations] + 1 ;; -1]], 
         circuit[[1 ;; Min[newVlocations] - 1]]], circuit]]
 
subdivideGraph[G_Graph, (E_Rule) | (E_UndirectedEdge)] /; 
     UndirectedGraphQ[G] := Module[{H, e, newV, v}, 
     If[Head[E] === Rule, e = UndirectedEdge @@ E, e = E]; 
      If[ !EdgeQ[G, e], Message[subdivideGraph::nonedge]; Return[$Failed]]; 
      newV = StringJoin[ToString[e[[1]]], "-", ToString[e[[2]]]]; 
      H = Graph[VertexAdd[G, newV], VertexCoordinates -> 
         Append[GraphEmbedding[G], {0, 0}]]; 
      PropertyValue[{H, newV}, VertexCoordinates] = 
       (PropertyValue[{H, e[[1]]}, VertexCoordinates] + 
         PropertyValue[{H, e[[2]]}, VertexCoordinates])/2; 
      H = EdgeDelete[H, e]; H = EdgeAdd[H, {e[[1]] -> newV, newV -> e[[2]]}]; 
      H]
 
subdivideGraph /: subdivideGraph::nonedge = 
     "Second argument must be an edge in the graph."
 
smoothGraph[G_Graph, v_] /; UndirectedGraphQ[G] := 
    Module[{N, H, e}, N = AdjacencyList[G, v]; 
      If[Length[N] != 2 || EdgeQ[G, UndirectedEdge[N[[1]], N[[2]]]], 
       Message[smoothGraph::vertx]; Return[$Failed]]; H = VertexDelete[G, v]; 
      e = UndirectedEdge[N[[1]], N[[2]]]; H = EdgeAdd[H, e]; H]
 
smoothGraph /: smoothGraph::vertx = "Cannot smooth this vertex."
 
sortVertices[G_Graph] := Sort[VertexList[G], 
     VertexDegree[G, #1] >= VertexDegree[G, #2] & ]
 
greedyColorer[G_Graph] := Module[{H = G, V, currentColor = 0, 
      colorFunction = ColorData[1], excludeSet, i}, 
     V = sortVertices[H]; While[V != {}, currentColor++; 
        PropertyValue[{H, V[[1]]}, VertexStyle] = colorFunction[
          currentColor]; excludeSet = VertexList[NeighborhoodGraph[H, 
           V[[1]]]]; V = Delete[V, 1]; i = 1; While[i <= Length[V], 
         If[ !MemberQ[excludeSet, V[[i]]], 
          PropertyValue[{H, V[[i]]}, VertexStyle] = colorFunction[
             currentColor]; excludeSet = Union[excludeSet, 
             VertexList[NeighborhoodGraph[H, V[[i]]]]]; V = Delete[V, i], 
          i++]]; ]; H]
 
allGraphs[n_Integer] /; n > 0 := Module[{cg, v, A = {}, V = Range[n], powerE, 
      vCoords, E}, cg = CompleteGraph[n]; powerE = Subsets[EdgeList[cg]]; 
      vCoords = GraphEmbedding[cg]; 
      Do[AppendTo[A, Graph[V, E, VertexCoordinates -> vCoords]], 
       {E, powerE}]; A]
 
nonIsoGraphs[n_Integer] /; n > 0 := Module[{cg, v, A = {}, V = Range[n], 
      powerE, vCoords, E, i, G, j}, cg = CompleteGraph[n]; 
      powerE = Subsets[EdgeList[cg]]; vCoords = GraphEmbedding[cg]; 
      Do[AppendTo[A, Graph[V, E, VertexCoordinates -> vCoords]], 
       {E, powerE}]; DeleteDuplicates[A, IsomorphicGraphQ]]
 
generateEulerian[n_Integer] /; n > 0 := Module[{G, path}, 
     While[ !EulerianGraphQ[G], G = RandomGraph[BernoulliGraphDistribution[n, 
          0.5]]]; animatePath[G, First[FindEulerianCycle[G]]]]
 
connectedProbability[n_Integer, max_Integer] /; n > 0 && max > 0 := 
    Module[{G, i, count = 0}, For[i = 1, i <= max, i++, 
       G = RandomGraph[BernoulliGraphDistribution[n, 0.5]]; 
        If[ConnectedGraphQ[G], count++]]; count/max]
