fibonacci[1] = 1
 
fibonacci[2] = 1
 
fibonacci[n_Integer] := fibonacci[n] = fibonacci[n - 1] + fibonacci[n - 2]
 
printMove[src_String, dest_String] := Print["Move disk from peg ", src, 
     " to peg ", dest, "."]
 
transferDisk[src_String, via_String, dest_String, ndisks_Integer] := 
    If[ndisks == 1, printMove[src, dest], 
     transferDisk[src, dest, via, ndisks - 1]; printMove[src, dest]; 
      transferDisk[via, src, dest, ndisks - 1]]
 
hanoi[ndisks_Integer] /; ndisks > 1 := transferDisk["A", "B", "C", ndisks]
 
compatible[talkList_] := Module[{p, j, jstart, i}, 
     For[j = 1, j <= Length[talkList], j++, jstart = talkList[[j]][[1]]; 
        p[j] = Catch[For[i = j - 1, i >= 1, i--, If[talkList[[i]][[2]] <= 
              jstart, Throw[i]]]; Throw[0]]]; p]
 
totalAttendance[talkList_, p_] := Module[{j, T}, 
     T[0] = 0; For[j = 1, j <= Length[talkList], j++, 
       T[j] = Max[talkList[[j]][[3]] + T[p[j]], T[j - 1]]]; T]
 
maximumAttendance[talkList_List] := Module[{L, p, T}, 
     L = Sort[talkList, #1[[2]] < #2[[2]] & ]; p = compatible[L]; 
      T = totalAttendance[L, p]; T[Length[talkList]]]
 
fibonacci2[n_] = -(((1 - Sqrt[5])/2)^n/Sqrt[5]) - 
     ((-5 - Sqrt[5])*(1 + Sqrt[5])^(-1 + n))/(5*2^n)
 
recSol2Distinct[c_, d_, u_, v_] := Module[{CERoots, alphas, alpha, beta, f, 
      r}, CERoots = r /. Solve[r^2 - c*r - d == 0, r]; 
      alphas = Solve[{alpha*CERoots[[1]] + beta*CERoots[[2]] == u, 
          alpha*CERoots[[1]]^2 + beta*CERoots[[2]]^2 == v}, {alpha, beta}][[
        1]]; Function[n, alpha*CERoots[[1]]^n + beta*CERoots[[2]]^n /. 
        alphas]]
 
recSolver2[c_, d_, u_, v_] := Module[{CERoots, alphas, alpha, beta, r}, 
     CERoots = r /. Solve[r^2 - c*r - d == 0, r]; 
      If[CERoots[[1]] == CERoots[[2]], 
       alphas = Solve[{alpha*CERoots[[1]] + beta*CERoots[[1]] == u, 
            alpha*CERoots[[1]]^2 + 2*beta*CERoots[[1]]^2 == v}, 
           {alpha, beta}][[1]]; Return[Function[n, 
          alpha*CERoots[[1]]^n + n*beta*CERoots[[1]]^n /. alphas]], 
       alphas = Solve[{alpha*CERoots[[1]] + beta*CERoots[[2]] == u, 
            alpha*CERoots[[1]]^2 + beta*CERoots[[2]]^2 == v}, {alpha, beta}][[
          1]]; Return[Function[n, alpha*CERoots[[1]]^n + 
            beta*CERoots[[2]]^n /. alphas]]]]
 
binarySearch[x_Integer, A:{__Integer}] /; Less @@ A := 
    Module[{n, i, j, m, location}, n = Length[A]; i = 1; j = n; 
      While[i < j, m = Floor[(i + j)/2]; If[x > A[[m]], i = m + 1, j = m]]; 
      If[x == A[[i]], location = i, location = 0]; location]
 
testSeating[seating_List] := Module[{i, twinpair}, 
     Catch[For[i = 1, i <= 5, i++, Do[If[MemberQ[twinpair, seating[[i]]] && 
           MemberQ[twinpair, seating[[i + 1]]], Throw[False]], 
         {twinpair, twins}]]; Throw[True]]]
 
ontoFunctions[m_Integer, n_Integer] /; m > 0 && n > 0 := 
    If[m >= n, Sum[(-1)^k*Binomial[n, k]*(n - k)^m, {k, 0, n - 1}], 0]
 
findFib[target_Integer] := Module[{n = 1}, While[Fibonacci[n] < target, n++]; 
      Print["The ", n, "th Fibonacci number is ", Fibonacci[n]]]
 
primeFib[time_] := Module[{i = 0, temp, primes = {}}, 
     Reap[TimeConstrained[While[True, i++; temp = Fibonacci[i]; 
          If[PrimeQ[temp], Sow[temp]]], time]][[2,1]]]
 
derangementP[n_Integer] /; n > 0 := Sum[(-1)^k*(1/k!), {k, 0, n}]
