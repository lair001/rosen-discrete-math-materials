AdditionTable[m_] := Module[{a, b}, TableForm[Table[Mod[a + b, m], 
       {a, 0, m - 1}, {b, 0, m - 1}], TableHeadings -> 
       {Range[0, m - 1], Range[0, m - 1]}]]
 
MultiplicationTable[m_] := Module[{a, b}, 
     TableForm[Table[Mod[a*b, m], {a, 0, m - 1}, {b, 0, m - 1}], 
      TableHeadings -> {Range[0, m - 1], Range[0, m - 1]}]]
 
convertString[n_, b1_, b2_] := IntegerString[FromDigits[n, b1], b2]
 
addition[a_List, b_List] := Module[{n, A, B, S, c, j, d}, 
     n = Max[Length[a], Length[b]]; A = PadLeft[a, n]; B = PadLeft[b, n]; 
      S = ConstantArray[0, n]; c = 0; For[j = n, j >= 1, j--, 
       d = Floor[(A[[j]] + B[[j]] + c)/2]; S[[j]] = A[[j]] + B[[j]] + c - 
          2*d; c = d]; If[c == 1, PrependTo[S, 1]]; S]
 
multiplication[a_List, b_List] := Module[{n, j, c, p}, 
     n = Length[b]; For[j = 0, j <= n - 1, j++, If[b[[n - j]] == 1, 
        c[j] = Join[a, ConstantArray[0, j]], c[j] = {0}]]; p = {0}; 
      For[j = 0, j <= n - 1, j++, p = addition[p, c[j]]]; p]
 
crTestArgs[a_, m_] := Check[If[Length[a] != Length[m], 
       Message[crTheorem::argsize]]; If[ !CoprimeQ @@ m, 
       Message[crTheorem::argcp]]; True, False]
 
crTheorem[a:{__Integer}, m:{__Integer}] /; crTestArgs[a, m] := 
    Module[{p, M, y, i, x}, p = Times @@ m; For[i = 1, i <= Length[a], i++, 
       M[i] = p/m[[i]]; y[i] = PowerMod[M[i], -1, m[[i]]]]; 
      x = Sum[a[[i]]*M[i]*y[i], {i, Length[a]}]; Mod[x, p]]
 
crTheorem /: crTheorem::argcp = "Moduli must be pairwise relatively prime."
 
crTheorem /: crTheorem::argsize = "Arguments must be lists of the same size."
 
findPseudoprimes[b_Integer, max_Integer] := 
    Module[{n}, Reap[For[n = 3, n <= max, n = n + 2, 
        If[PowerMod[b, n - 1, n] == 1 && CompositeQ[n], Sow[n]]]][[2,1]]]
 
allPrimitiveRoots[(p_)?PrimeQ] := Select[Range[2, p - 1], 
     MultiplicativeOrder[#1, p] == p - 1 & ]
 
calculateHash[id_Integer] := Mod[id, 57] + 1
 
printRecords[database_List] := Module[{i}, For[i = 1, i <= Length[database], 
      i++, If[database[[i]] =!= 0, Print[i, " ", database[[i]]]]]]
 
storeRecord[id_Integer, gpa_Real] := Module[{record, hash, i}, 
     record = {id, gpa}; For[i = 0, i <= 56, i++, 
       hash = calculateHash[id + i]; If[studentRecords[[hash]] === 0, 
         Break[]]]; studentRecords[[hash]] = record; ]
 
studentRecords = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
 
retrieveRecord[id_Integer] := Module[{hash, i}, 
     Catch[For[i = 0, i <= 56, i++, hash = calculateHash[id + i]; 
        If[studentRecords[[hash]] === 0, Message[retrieveRecord::missing]; 
          Throw[Null]]; If[studentRecords[[hash]][[1]] == id, 
         Throw[studentRecords[[hash]]]]]]]
 
retrieveRecord /: retrieveRecord::missing = "Desired record does not exist."
 
randomIDs[n_Integer] := Module[{m = 8999, a = 57, c = 328, x, i}, 
     x = Mod[Floor[1000*SessionTime[]], m]; 
      Reap[For[i = 1, i <= n, i++, Sow[x = Mod[a*x + c, m]]]][[2,1]]]
 
randomGPAs[n_Integer] := Module[{m = 2^31 - 1, a = 7^5, x, i}, 
     x = Mod[Floor[1000*SessionTime[]], m]; 
      Reap[For[i = 1, i <= n, i++, x = Mod[a*x, m]; 
          Sow[Round[(x/(m - 1))*4, 0.01]]]][[2,1]]]
 
checkISBN[isbn_String] := Module[{i, check}, 
     check = Mod[Sum[i*ToExpression[StringTake[isbn, {i}]], {i, 9}], 11]; 
      Which[check < 10, ToString[check] == StringTake[isbn, {10}], 
       check == 10, StringTake[isbn, {10}] == "X"]]
 
affineCipher[s_String, a_Integer, b_Integer] /; If[CoprimeQ[a, 27], True, 
      Message[affineCipher::arga]; False] := Module[{S, T}, 
     S = LetterNumber[s]; T = (Mod[a*#1 + b, 27] & ) /@ S; 
      StringJoin[FromLetterNumber[T]]]
 
affineCipher /: affineCipher::arga = 
     "Second argument must be relatively prime to 27."
 
generateKeys[(p_)?PrimeQ, (q_)?PrimeQ] := Module[{n, phin, e, d}, 
     e = 13; n = p*q; phin = (p - 1)*(q - 1); d = PowerMod[e, -1, phin]; 
      {{n, e}, {n, d}}]
 
RSA[{n_Integer, e_Integer}, msg:{__Integer}] := 
    Module[{c}, c = (PowerMod[#1, e, n] & ) /@ msg]
 
cantorExpansion[n_Integer] := Module[{a, k = 1, y = n}, 
     Reap[While[y != 0, a = Mod[y, k + 1]; Sow[a]; y = (y - a)/(k + 1); 
         k++]][[2,1]]]
 
checkMersenne[max_Integer] := Module[{p = 2}, 
     Reap[While[p <= max, If[PrimeQ[2^p - 1], Sow[p]]; p = NextPrime[p]]][[2,
      1]]]
 
ce5[max_Integer] := Module[{n}, Reap[For[n = 1, n <= max, n++, 
        If[PrimeQ[n^2 + 1], Sow[n^2 + 1]]]][[2,1]]]
