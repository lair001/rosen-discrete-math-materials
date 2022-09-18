findMax[L:{__Integer}] := Module[{tempMax, i}, tempMax = L[[1]]; 
      For[i = 2, i <= Length[L], i++, If[tempMax < L[[i]], 
        tempMax = L[[i]]]]; tempMax]
 
binarySearch[x_Integer, A:{__Integer}] /; Less @@ A := 
    Module[{n, i, j, m, location}, n = Length[A]; i = 1; j = n; 
      While[i < j, m = Floor[(i + j)/2]; If[x > A[[m]], i = m + 1, j = m]]; 
      If[x == A[[i]], location = i, location = 0]; location]
 
interchange[L_List, i_] := Module[{M = L, temp}, 
     temp = M[[i]]; M[[i]] = M[[i + 1]]; M[[i + 1]] = temp; M]
 
bubbleSort[A_List] := Module[{i, j, n = Length[A], B = A}, 
     For[i = 1, i <= n - 1, i++, For[j = 1, j <= n - i, j++, 
        If[B[[j]] > B[[j + 1]], B = interchange[B, j]]]]; B]
 
getBubbleTimes[trials_Integer, min_Integer, max_Integer, step_Integer] /; 
     trials > 0 && min > 0 && max > min && step > 0 := 
    Module[{s, avgTimeData = {}, times, input}, 
     For[s = min, s <= max, s = s + step, 
       times = Reap[Do[input = RandomSample[Range[s]]; 
             Sow[Timing[bubbleSort[input]][[1]]], trials]][[2,1]]; 
        AppendTo[avgTimeData, {s, Mean[times]}]]; avgTimeData]
 
stringMatch[n_Integer, m_Integer, t_String, p_String] /; 
     n > 0 && m > 0 && m <= n := Module[{T, P, s, j}, 
     T = Characters[t]; P = Characters[p]; For[s = 0, s <= n - m, s++, 
       j = 1; While[j <= m && T[[s + j]] == P[[j]], j = j + 1]; 
        If[j > m, Print[s, " is a valid shift"]]]]
 
stringMatch[t_String, p_String] := Module[{T, n, P, m, s, j}, 
     T = Characters[t]; n = Length[T]; P = Characters[p]; m = Length[P]; 
      For[s = 0, s <= n - m, s++, 
       j = 1; While[j <= m && T[[s + j]] == P[[j]], j = j + 1]; 
        If[j > m, Print[s, " is a valid shift"]]]]
 
binarySearchC[x_Integer, A:{__Integer}] := 
    Module[{n, i, j, m, location, count = 0}, n = Length[A]; i = 1; j = n; 
      While[i < j, count = count + 2; m = Floor[(i + j)/2]; 
        If[x > A[[m]], i = m + 1, j = m]]; count = count + 1; 
      If[x == A[[i]], location = i, location = 0]; count = count + 1]
 
binaryAvg[n_Integer] := Module[{data = {}, inputList, x}, 
     inputList = Range[n]; data = Reap[Do[Sow[binarySearchC[x, inputList]], 
          {x, 1, n}]][[2,1]]; N[Mean[data]]]
