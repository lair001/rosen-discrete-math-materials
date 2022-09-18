lottery[n_Integer] /; n >= 6 := 1./Binomial[n, 6]
 
miller[n_Integer, b_Integer] := Module[{s = 0, t = n - 1, j}, 
     While[Mod[t, 2] == 0, t = t/2; s++]; 
      Catch[If[PowerMod[b, t, n] == 1, Throw[True]]; For[j = 0, j <= s - 1, 
         j++, If[PowerMod[b, 2^j*t, n] == n - 1, Throw[True]]]; Throw[False]]]
 
millerMC[n_Integer] := Module[{b}, 
     Catch[Do[b = RandomInteger[{2, n - 1}]; If[ !miller[n, b], 
          Throw["Composite"]], 30]; Throw["Prime"]]]
 
wordQ[poem_String, word_String] := 
     !StringFreeQ[poem, Except[WordCharacter | "'"]~~word~~
       Except[WordCharacter | "'"], IgnoreCase -> True]
 
countMessages[word_String, L:{__String}] := Module[{count = 0, p}, 
     Do[If[wordQ[p, word], count++], {p, L}]; count]
 
pShakespeareGivenWord[word_String] := Module[{sCount, eCount, pWordGivenS, 
      pWordGivenNotS}, sCount = Length[sPoems]; eCount = Length[ePoems]; 
      pWordGivenS = countMessages[word, sPoems]/sCount; 
      pWordGivenNotS = countMessages[word, ePoems]/eCount; 
      N[pWordGivenS/(pWordGivenS + pWordGivenNotS)]]
 
pShakespeareGivenList[L_List] := Module[{sCount, eCount, pGivenS, 
      pGivenNotS}, sCount = Length[sPoems]; eCount = Length[ePoems]; 
      pGivenS = Product[countMessages[w, sPoems]/sCount, {w, L}]; 
      pGivenNotS = Product[countMessages[w, ePoems]/eCount, {w, L}]; 
      If[pGivenS + pGivenNotS != 0, N[pGivenS/(pGivenS + pGivenNotS)], 0.5]]
 
pShakespeare[testMessage_String, testSize_Integer] := 
    Module[{testWordList}, testWordList = RandomSample[
        DeleteDuplicates[StringSplit[testMessage, 
          Except[WordCharacter | "'"]..]], testSize]; 
      pShakespeareGivenList[testWordList]]
 
cardSimulate[m_Integer] := Module[{currCollection, count, tempCard}, 
     currCollection = ConstantArray[0, m]; count = 0; 
      While[Total[currCollection] != m, tempCard = RandomInteger[{1, m}]; 
        count++; currCollection[[tempCard]] = 1]; count]
 
lottery2[n_Integer, k_Integer] /; n >= k := 1./Binomial[n, k]
 
birthdays[percentage_Real] := Module[{numPeople = 0, curProb = 0}, 
     While[curProb < percentage, numPeople++; curProb = 
         1 - 366!/(366 - numPeople)!/366^numPeople]; numPeople]
