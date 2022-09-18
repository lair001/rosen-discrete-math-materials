formWords[V_, T_, S_, P_, timelimit_] := 
    Module[{L = {}, A = {"S"}, N, curString, D, s, d}, 
     N = Complement[V, T]; TimeConstrained[While[A != {}, 
        curString = A[[1]]; A = Delete[A, 1]; 
         D = Reap[Do[Do[Sow[StringReplacePart[curString, p, l]], {p, P[s]}, 
              {l, StringPosition[curString, s]}], {s, N}]][[2,1]]; 
         Do[If[StringContainsQ[d, N], AppendTo[A, d], AppendTo[L, d]], 
          {d, D}]], timelimit]; DeleteDuplicates[L]]
 
machineWithOutput[transTable_Association, inString_List] := 
    Module[{curState = 0, outString, i, newo, news}, 
     outString = ConstantArray[0, Length[inString]]; 
      For[i = 1, i <= Length[inString], i++, 
       {news, newo} = transTable[{curState, inString[[i]]}]; 
        outString[[i]] = newo; curState = news]; outString]
 
setCat[A_, B_] := Module[{a, b}, 
     Flatten[Table[Which[Head[a] === List && Head[b] === List, Join[a, b], 
        Head[a] === List && Head[b] =!= List, Join[a, {b}], 
        Head[a] =!= List && Head[b] === List, Join[{a}, b], 
        Head[a] =!= List && Head[b] =!= List, Join[{a}, {b}]], {a, A}, 
       {b, B}], 1]]
 
setPow[A_, k_] := If[k == 0, {{}}, setCat[setPow[A, k - 1], A]]
 
kleene[A_, n_] := Module[{K = {{}}, x, Ak, i}, 
     Do[K = Union[K, {{x}}], {x, A}]; Ak = K; For[i = 2, i <= n, i++, 
       Ak = setCat[Ak, A]; K = Union[K, Ak]]; K]
 
extendedTransition[state_, input_, transFunc_] := 
    Module[{curState = state, i}, For[i = 1, i <= Length[input], i++, 
       curState = transFunc[{curState, input[[i]]}]]; curState]
 
recognizedQ[x_, transFunc_, init_, final_] := Module[{endState}, 
     endState = extendedTransition[init, x, transFunc]; 
      MemberQ[final, endState]]
 
findLanguage[transFunc_, init_, final_, A_, n_] := 
    Module[{An, x, L = {}}, An = kleene[A, n]; 
      Do[If[recognizedQ[x, transFunc, init, final], AppendTo[L, x]], 
       {x, An}]; L]
 
makeDeterministic[transFunc_, alphabet_, init_, final_] := 
    Module[{S = {}, T = {{init}}, state, i, s, x, newfinal, 
      newTable = Association[]}, 
     While[T != {}, state = T[[1]]; T = Delete[T, 1]; AppendTo[S, state]; 
        Do[x = {}; Do[x = Union[x, transFunc[{s, i}]], {s, state}]; 
          x = Union[x]; newTable[{state, i}] = x; If[ !MemberQ[S, x], 
           T = Union[T, {x}]], {i, alphabet}]]; newfinal = {}; 
      Do[If[Intersection[state, final] != {}, newfinal = 
         Union[newfinal, {state}]], {state, S}]; {{init}, newfinal, newTable}]
 
catAutomata[atable_, astart_, afinal_, btable_, bstart_, bfinal_] := 
    Module[{abstart, abfinal, abtable, i}, abstart = 10*astart + 1; 
      abfinal = (10*#1 + 2 & ) /@ bfinal; If[MemberQ[afinal, astart] && 
        MemberQ[bfinal, bstart], abfinal = Union[abfinal, {abstart}]]; 
      abtable = Join[Association @@ KeyValueMap[{10*#1[[1]] + 1, #1[[2]]} -> 
            10*#2 + 1 & , atable], Association @@ KeyValueMap[
          {10*#1[[1]] + 2, #1[[2]]} -> 10*#2 + 2 & , btable]]; 
      Do[If[Intersection[atable[i], afinal] != {}, 
        abtable[{10*i[[1]] + 1, i[[2]]}] = 
         Union[abtable[{10*i[[1]] + 1, i[[2]]}], {2}]], {i, Keys[atable]}]; 
      If[MemberQ[afinal, astart], Do[If[i[[1]] == 0, abtable[{1, i[[2]]}] = 
          Union[abtable[{1, i[[2]]}], (10*#1 + 2 & ) /@ btable[i]]], 
        {i, Keys[btable]}]]; {abstart, abfinal, abtable}]
 
tuplesToIndexed[S_] := Module[{x}, Association @@ 
      Table[x[[{1, 2}]] -> x[[{3, 4, 5}]], {x, S}]]
 
Turing[f_, t_, init_] := Module[{pos = 1, state = init, tape = t, domain, y}, 
     domain = Keys[f]; While[MemberQ[domain, {state, tape[[pos]]}], 
       y = f[{state, tape[[pos]]}]; state = y[[1]]; tape[[pos]] = y[[2]]; 
        Which[pos == 1 && y[[3]] === L, PrependTo[tape, B], 
         pos == Length[tape] && y[[3]] === R, AppendTo[tape, B]; pos++, 
         y[[3]] === L, pos--, y[[3]] === R, pos++]; ]; {tape, state}]
 
verboseTuring[f_, t_, init_] := Module[{pos = 1, state = init, tape = t, 
      domain, y, displayTape}, domain = Keys[f]; displayTape = t; 
      displayTape[[pos]] = StringJoin["\[Rule]", ToString[tape[[pos]]]]; 
      Print[displayTape, state]; While[MemberQ[domain, {state, tape[[pos]]}], 
       y = f[{state, tape[[pos]]}]; state = y[[1]]; tape[[pos]] = y[[2]]; 
        Which[pos == 1 && y[[3]] === L, PrependTo[tape, B], 
         pos == Length[tape] && y[[3]] === R, AppendTo[tape, B]; pos++, 
         y[[3]] === L, pos--, y[[3]] === R, pos++]; displayTape = tape; 
        displayTape[[pos]] = StringJoin["\[Rule]", ToString[tape[[pos]]]]; 
        Print[displayTape, state]; ]; {tape, state}]
 
unaryTape[a_, b_] := Join[ConstantArray[1, {a + 1}], {"*"}, 
     ConstantArray[1, {b + 1}]]
 
extendedTransitionND[states_, input_, transFunc_] := 
    Module[{curStates, i, s, newStates}, curStates = states; 
      For[i = 1, i <= Length[input], i++, newStates = {}; 
        Do[newStates = Union[newStates, transFunc[{s, input[[i]]}]], 
         {s, curStates}]; curStates = newStates]; curStates]
 
recognizedNDQ[x_, transFunc_, init_, final_] := Module[{endStates}, 
     endStates = extendedTransitionND[{init}, x, transFunc]; 
      Intersection[endStates, final] != {}]
 
findLanguageND[transFunc_, init_, final_, A_, n_] := 
    Module[{An, x, L}, An = kleene[A, n]; L = {}; 
      Do[If[recognizedNDQ[x, transFunc, init, final], L = Union[L, {x}]], 
       {x, An}]; L]
 
makeTable[t_] := Module[{j, d, T = Association[]}, 
     For[j = 1, j <= 4, j++, d = dom[[j]]; T[{d[[1]], d[[2]]}] = t[[j]]]; T]
 
beaverTuring[f_, maxsteps_] := Module[{pos = 1, state = 0, tape = {B}, 
      domain, y, numsteps = 0}, domain = Keys[f]; 
      While[MemberQ[domain, {state, tape[[pos]]}] && numsteps < maxsteps, 
       y = f[{state, tape[[pos]]}]; state = y[[1]]; tape[[pos]] = y[[2]]; 
        Which[pos == 1 && y[[3]] === L, PrependTo[tape, B], 
         pos == Length[tape] && y[[3]] === R, AppendTo[tape, B]; pos++, 
         y[[3]] === L, pos--, y[[3]] === R, pos++]; numsteps++]; 
      If[numsteps < maxsteps, Count[tape, 1], -1]]
