# helper function 
GetStartRedWord := function(blocks,reds)
	local startRedWord, i, pos;
	# Output - positions of red strands 
	
	# start with empty word
	startRedWord := [];
	pos := 1;

	for i in [1..Size(blocks)] do
		
		# check if Lyndon factor has red strand
		if reds[i] = 1 then
			
			# record position in startRedWord
			Append(startRedWord,[pos]);
		
		fi;
		pos := pos + blocks[i];
	od;	
	return startRedWord;
end;

# determine if permutation contains a crossing of red strands
CheckRedCrossing := function(startRedWord,perm)
	local finalRedWord, i, pos,cross;
	
	# record final positions of red strands
	finalRedWord := Filtered(perm, x -> x in startRedWord);
	cross := false;

	# compare to initial positions of red strands
	for i in [1..Size(finalRedWord)] do
		
		# determine if there was crossing
		if finalRedWord[i] > startRedWord[i] then
			cross := true;
		fi;
	
	od;

  # true when reds crossed, false otherwise
	return cross;
end;

# keep only permutations that avoid red crossings
RemoveRedCrossings := function(blocks,reds,shuffledperms)
	local startRedWord;
	
	startRedWord := GetStartRedWord(blocks,reds);
	return Filtered(shuffledperms, x -> not CheckRedCrossing(startRedWord,x)); 
end;

# gives ShufflePermutations now with red strands
ShufflePermutationsRed := function(blocks,reds)
	local startRedWord,perms;
	
	# get permutations as in original 
	perms := ShufflePermutations(blocks);
	
	# determine which blocks have red strand
	startRedWord := GetStartRedWord(blocks,reds);

	# remove permutations which cross red strands
	return RemoveRedCrossings(blocks,reds,perms);
end;


# same as InverseShufflePermutations but it Calls ShufflePermutationsRed 
InverseShufflePermutationsRed := function(blocks,reds)
  return List(ShufflePermutationsRed(blocks,reds),InvertPermutation);
end;


# same as WordShuffle but it calls InverseShufflePermutationsRed
WordShuffleRed := function(w) local blocks,i,perms,ans,p,this,cf,concatenated,j, reds;
  blocks := [];
  concatenated := [];
  reds:=[];
  for i in w do
      Add(blocks,Length(i));
      Append(concatenated,i);
      if i[1]=redindex then  Add(reds,1); else  Add(reds,0); fi;
  od;
  perms := InverseShufflePermutationsRed(blocks,reds);
  ans := ZeroWord();
  for p in perms do
    this := [];
    cf := q^0;
    for i in [1..Length(p)] do
# Need to position concatenated[i] into position p[i]
      for j in [1..i-1] do
        if p[j] > p[i] then cf := cf * q^(-d[concatenated[i]]*a[concatenated[i]][concatenated[j]]);fi;
      od;
      this[p[i]] := concatenated[i];
    od;
    ans := ans+cf*Word(this);
  od;
  return ans;
end;

ShufffleRed := function(arg) local lengths,places,ans,cf,w,i,j;
  if Length(arg) = 0 then return(Word([]));fi;
  if not IsMvpObj(arg[1]) then 
    Assert(0,Length(arg) = 1);
    arg := arg[1];
  fi;
  if Length(arg) = 0 then return(Word([]));fi;
  Assert(0,IsMvpObj(arg[1]));

# OK ready to begin, arg is now a list of MVPs
# Need to open some parentheses

  lengths := [];
  for i in [1..Length(arg)] do
    Add(lengths,[1..Length(arg[i]!.elm)]);
  od;
  ans := ZeroWord();
  for places in Cartesian(lengths) do
    cf := q^0;
    w := [];
    for i in [1..Length(places)] do
      cf := cf * arg[i]!.coeff[places[i]];
      Add(w,MvpUnpack(arg[i]!.elm[places[i]][1][1]));
    od;

    ans := ans + cf * WordShuffleRed(w);
  od;
  return ans;
end;
