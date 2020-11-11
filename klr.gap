goodies := [];
# Code to make calculations in finite type KLR algebras
# Call e.g. SetCartan("a",7) before you do anything!!!!


if not IsBound(a) then
  Read("bergman.gap");
  q := Indeterminate(Rationals,"q");
  store := [];
  stored := [];

  rankedroots := [];	# This is all roots separated by height
  roots := [];         	# This is all roots in Lyndon order
  lyndon := [];		# This is the good Lyndon words corresponding to roots, also in Lyndon order
  characters := [];	# We'll store cuspidal characters globally; a list of pairs [goodlyndonword,character]
  a := [];   		# The Cartan matrix; simply-laced only right now but only minor changes for general... 
       			# My convention is that a[i][j] = <alpha_i^vee,alpha_j>
  d := [];		# d[i]'s are 1,2,3 according to root length then (alpha_i,alpha_j) = d[i] a[i][j] is symmetric
  kappas := [];
  highestroot := [];
  block := 0;			# I store the last decomp matrix and irred characters
  goodwords := [];		# This is the ordered list of good words in the block
  D := [];			# computed but only for one block at a time...
  		      	 	# The cols are the standards written in simples ordered by lex
  IC := [];			# The rows are the characters as mvp's
  SC := [];
fi;

QuantumInteger := function(n,deg) local i,ans;
  i:=1-n;
  ans := 0*q;
  while i <= n-1 do
    ans := ans + q^(i*deg);
    i := i+2;
  od;
  return ans;
end;

BarLaurent := function(laurent) local c,deg,ans,i;
  c := CoefficientsOfLaurentPolynomial(laurent);
  deg := -c[2]-Length(c[1])+1;
  ans := 0*q;
  for i in [1..Length(c[1])] do
    ans := ans + q^(deg+i-1)*c[1][Length(c[1])+1-i];
  od;
  return ans;
end;

DimensionAt1 := function(mvp) local ans,i;
  ans := 0;
  for i in mvp!.coeff do
    ans := ans + Sum(CoefficientsOfLaurentPolynomial(i)[1]);
  od;
  return ans;
end;



IsBarInvariant := function(laurent)
  return laurent = BarLaurent(laurent);
end;

# In Leclerc's algorithm I need to square root something that's a product of smallish quantum integers. This tries to do it...
# Its a cludge so may well fail!

FakeSquareRoot := function(laurent) local p,pp;
  Assert(0,IsLaurentPolynomial(laurent));
  if laurent = q^0 then return q^0;fi;
  for p in Reversed(Set([1,Maximum(d)])) do
    for pp in [2..10] do
      if QuotRemLaurpols(laurent,QuantumInteger(pp,p)^2,4) <> fail then

# Print("Div by q_", p, "^",pp,"\n");

        return(FakeSquareRoot(laurent / QuantumInteger(pp,p)^2) * QuantumInteger(pp,p));
      fi;
    od;
  od;
  Assert(0,false);
end;

# This is to humanize Laurent polys a bit...

PrettyPrintLaurent := function(laurent) local p,pp;
  Assert(0,IsLaurentPolynomial(laurent));
  if laurent = q^0 then return q^0;fi;
  for p in Reversed(Set([1,Maximum(d)])) do
    for pp in [2..10] do
      if QuotRemLaurpols(laurent,QuantumInteger(pp,p),4) <> fail then
        Print("[",pp,"]_",p," ");
        PrettyPrintLaurent(laurent / QuantumInteger(pp,p));
        return;
      fi;
    od;
  od;
  Print("(",laurent,")");
end;

PrettyPrintMvp := function(mvp) local i;
  for i in [1..Length(mvp!.elm)] do
    Print("(");
    PrettyPrintLaurent(mvp!.coeff[i]);
    Print(")");
    Print(mvp!.elm[i][1][1]);
    if i < Length(mvp!.elm) then Print("+\n");fi;
  od;
end;

GetCoefficient := function(mvp,word) local i;
  for i in [1..Length(mvp!.elm)] do
    if MvpUnpack(mvp!.elm[i][1][1]) = word then
      return mvp!.coeff[i];
    fi;
  od;
  return 0*q;
end;

Word := function(w) local s,i;
  s := "[";
  for i in [1..Length(w)] do
    Append(s,String(w[i]));
    if i < Length(w) then Append(s,"|");fi;
  od;
  Append(s,"]");
  return Mvp(s);
end;

# Call with two words

Concatenate := function(w1,w2) local s,i;
  s := "[";
  if w1 = [] then return Word(w2);fi;
  if w2 = [] then return Word(w1);fi;
  for i in [1..Length(w1)] do
    Append(s,String(w1[i]));
    Append(s,"|");
  od;
  for i in [1..Length(w2)] do
    Append(s,String(w2[i]));
    if i < Length(w2) then Append(s,"|");fi;
  od;
  Append(s,"]");
  return Mvp(s);
end;

ZeroWord := function()
  return 0*Word([]);
end;

#####
# This is all about finding good lyndon words

# Given a word returns \sum_{i \in w} alpha_i

WordToAlpha := function(word) local root,i;
  root := [];
  for i in [1..Length(a)] do Add(root,0);od;
  for i in word do root[i] := root[i]+1;od;
  return root;
end;

SimpleRoot := function(i)
  return WordToAlpha([i]);
end;

InnerProduct := function(root1,root2) local ans,i,j;
  ans := 0;
  for i in [1..Length(a)] do for j in [1..Length(a)] do
    ans := ans + root1[i]*root2[j]*d[i]*a[i][j];
  od;od;
  return ans;
end;

NormSquared := function(root)
  return InnerProduct(root,root);
end;

# The first finds the good Lyndon word corresponding to positive root beta from the algorithm in 4.3 of Leclerc

Lyndon := function(beta) local i,j,candidates,ell1,ell2,found;

# To speed things up we store the good lyndon word for root beta in the list lyndon...

  found := 0;
  for i in [1..Length(roots)] do
    if roots[i] = beta then found := i;fi;
  od;
  Assert(0,found > 0);
  if IsBound(lyndon[found]) then return ShallowCopy(lyndon[found]);fi;

# First if beta = alpha_i the good Lyndon word is (i)

  if Sum(beta) = 1 then
    for i in [1..Length(beta)] do
      if beta[i] > 0 then
        lyndon[found] := [i];
        return([i]);
      fi;
    od;
    Assert(0,false);
  fi;

# So its not a simple root. Now write beta = beta_1 + beta_2 for positive roots beta_1, beta_2 in all
# possible ways so that Lyndon(beta_1) < Lyndon(beta_2)
# Then Lyndon(beta) is the maximum of Lyndon(beta_1).Lyndon(beta_2)'s

  candidates := [];
  for i in [1..Length(roots)] do 
    if beta - roots[i] in roots then
      ell1 := Lyndon(roots[i]); ell2 := Lyndon(beta-roots[i]);
      if ell1 < ell2 then Append(ell1,ell2); Add(candidates,ell1);fi;
    fi;
  od;
  Assert(0,candidates <> []);
  lyndon[found] := Maximum(candidates);
  return ShallowCopy(lyndon[found]);
end;

#####
# Routines to list the positive roots
# I store these as a list with i-th entry being a list of all the roots of height i.

PositiveRoot := function(r) local i;
  for i in [1..Length(r)] do
    if r[i] < 0 then return false;fi;
  od;
  return true;
end;

GetNewRoots := function(earlier, i) local newroots,ell,root,new;
  if earlier = [] then return [];fi;
  newroots := [];
  ell := Sum(earlier[1]);
  for root in earlier do
    new := ShallowCopy(root) - SimpleRoot(i)*InnerProduct(SimpleRoot(i),root)/d[i];
    if PositiveRoot(new) and Sum(new) > ell then Add(newroots,new);fi;
  od;
  return newroots;
end;

GenerateRoots := function() local simpleroots,i,j,newlevel,w;
  rankedroots := [];
  simpleroots := [];
  store := []; stored := [];
  for i in [1..Length(a)] do
    Add(simpleroots,[]);
    for j in [1..Length(a)] do
      Add(simpleroots[i],0);
    od;
    simpleroots[i][i] := 1;
  od;
  Add(rankedroots,simpleroots);
  while true do
    newlevel := [];
    for i in [1..Length(a)] do
      Append(newlevel, GetNewRoots(rankedroots[Length(rankedroots)], i));
    od;
    if newlevel = [] then 
      roots := Union(rankedroots);
      lyndon := [];				# Reset all the other stuff that we store on the way...
      characters := [];
      kappas := [];
      block := 0;
      D := [];
      goodwords := [];
      SC := [];
      IC := [];
      for i in [1..Length(a)] do
        Add(characters,[SimpleRoot(i),Word([i])]);
        Add(kappas, [[i],q^0]);
      od;
      for w in roots do Lyndon(w);od;		# This puts the lyndon word into storage
      SortParallel(lyndon,roots);
      return; 
    fi;
    Add(rankedroots, Set(newlevel));
  od;
  Assert(0,false);
end;

#####
# I've hard-coded a few Cartan matrices with a pretty random ordering of simple roots

SetCartan := function(type,rank) local i,j,this,beta;
  a := [];
  d := []; for i in [1..rank] do Add(d,1);od;
  if type = "a" then
    Assert(0,rank >= 1);
    for i in [1..rank] do
      this := [];
      for j in [1..rank] do
        this[j] := 0;
        if i = j then this[j] := 2;fi;
        if i = j+1 or i = j-1 then this[j] := -1;fi;
      od;
      Add(a,this);
    od;
  fi;
  if type = "d" then
    Assert(0,rank >= 3);
    for i in [1..rank-1] do
      this := [];
      for j in [1..rank-1] do
        this[j] := 0;
        if i = j then this[j] := 2;fi;
        if i = j+1 or i = j-1 then this[j] := -1;fi;
      od;
      if i = rank-2 then Add(this,-1); else Add(this,0);fi;
      Add(a,this);
    od;
    this := [];
    for j in [1..rank] do Add(this,0);od;
    this[rank] :=2; this[rank-2] := -1;
    Add(a,this);
  fi;
  if type = "b" then
    Assert(0,rank >= 2);
    for i in [1..rank] do
      this := [];
      for j in [1..rank] do
        this[j] := 0;
        if i = j then this[j] := 2;fi;
        if i = j+1 or i = j-1 then this[j] := -1;fi;
      od;
      Add(a,this);
    od;
    a[rank][rank-1] := -2;
    d := 2*d; d[rank] := 1;
  fi;
  if type = "c" then
    Assert(0,rank >= 2);
    for i in [1..rank] do
      this := [];
      for j in [1..rank] do
        this[j] := 0;
        if i = j then this[j] := 2;fi;
        if i = j+1 or i = j-1 then this[j] := -1;fi;
      od;
      Add(a,this);
    od;
    a[rank-1][rank] := -2;
    d[rank] := 2;
  fi;
  if type = "g" then
    Assert(0,rank=2);
#    a := [[2,-3],[-1,2]];
#    d := [1,3];
    a := [[2,-1],[-3,2]];
    d := [3,1];
  fi;
  if type = "f" then
    Assert(0,rank=4);
    a := [[2,-1,0,0],[-1,2,-2,0],[0,-1,2,-1],[0,0,-1,2]];
    d := [1,1,2,2];
  fi;
  if type = "e" and rank = 6 then
    a := [[2,-1,0,0,0,0],[-1,2,-1,0,0,0],[0,-1,2,-1,0,-1],[0,0,-1,2,-1,0],[0,0,0,-1,2,0],[0,0,-1,0,0,2]];
  elif type = "e" and rank = 7 then
    a := [[2,-1,0,0,0,0,0],[-1,2,-1,0,0,0,0],[0,-1,2,-1,0,0,0],[0,0,-1,2,-1,0,-1],[0,0,0,-1,2,-1,0],[0,0,0,0,-1,2,0],[0,0,0,-1,0,0,2]];
  elif type = "e" and rank = 8 then
    a :=[ [ 2, -1, 0, 0, 0, 0, 0, 0 ], [ -1, 2, -1, 0, 0, 0, 0, 0 ], [ 0, -1, 2, -1, 0, 0, 0, 0 ], 
  [ 0, 0, -1, 2, -1, 0, 0, 0 ], [ 0, 0, 0, -1, 2, -1, 0, -1 ], [ 0, 0, 0, 0, -1, 2, -1, 0 ], 
  [ 0, 0, 0, 0, 0, -1, 2, 0 ], [ 0, 0, 0, 0, -1, 0, 0, 2 ] ];
  elif type = "e" then Assert(0,false);
  fi;
  GenerateRoots();
  highestroot:=rankedroots[Length(rankedroots)][1];
end;

CartanFlipSub := function(i,j) local b,temp,k;
  b := StructuralCopy(a);
  temp:=d[i];d[i]:=d[j];d[j]:=temp;
  a[i] := b[j];
  a[j] := b[i];
  for k in [1..Length(a)] do
    temp := a[k][i]; a[k][i] := a[k][j]; a[k][j] := temp;
  od;
end;

CartanFlip := function(i,j)
  CartanFlipSub(i,j);
  GenerateRoots();
  highestroot:=rankedroots[Length(rankedroots)][1];
end;

CartanPermute := function(p) local h,temp;
  for h in [1..Length(p)-1] do
    if p[h] > p[h+1] then
      CartanFlipSub(h,h+1);
      temp := p[h]; p[h] := p[h+1]; p[h+1]:=temp;
      CartanPermute(p);
      return;
    fi;
  od;
  GenerateRoots();
  highestroot:=rankedroots[Length(rankedroots)][1];
end;  
  

#####
# Code to do with cuspidals

# This computes a component in the Kleschev-Ram graph

CKComponent := function(word) local i,j,k,newword,words,ans,this;
  if Length(word) <= 1 then return [ShallowCopy(word)];fi;
  i := word[Length(word)];
  newword := ShallowCopy(word); Unbind(newword[Length(word)]);
  words := CKComponent(newword);
  ans := [];
  for this in words do
   j := Length(this)+1;
   while j >= 1 and (j > Length(this) or a[this[j]][i] >= 0) do
     newword := [];
     for k in [1..j-1] do
       Add(newword,this[k]);
     od;
     Add(newword,i);
     for k in [j..Length(this)] do
       Add(newword,this[k]);
     od;
     if not newword in ans then Add(ans,ShallowCopy(newword));fi;
     j := j-1;
   od;
  od;
  return ans;
end;

# Either gets homogeneous character or returns fail if its not homogeneous

HomogeneousCharacter := function(word) local words,ch,okay,i,this;
  words := CKComponent(word);
  ch := 0*q;
  for this in words do
    okay := true;
    for i in [1..Length(this)-1] do
      if this[i] = this[i+1] then okay := false;fi;
    od;
    for i in [1..Length(this)-2] do
      if this[i] = this[i+2] and d[this[i+1]] <= d[this[i]] then okay := false;fi;
    od;
    if not okay then return fail;fi;
    ch := ch + Word(this);
  od;
  return ch;
end;
#####
# This returns all root partitions for a given element of Q_+
# i.e. we write beta = beta_1+...+beta_k for beta_1 >= ... >- beta_k (the list roots is assumed smallest first) summing to beta
# For the output of this function I'll store just the list that is the index of beta_1,...index of beta_k in the list roots

# Normally call just with one argument, beta

RootPartitions := function(arg) local beta,lastnumber,part,i,stack,this;

  if not IsList(arg[1]) then
    lastnumber := arg[1];beta:=arg[2];
  else
    lastnumber := 1;beta:=arg[1];
  fi;
  if Sum(beta) = 0 then return [[]]; fi;
  part := [];
  for i in [lastnumber..Length(roots)] do
    if PositiveRoot(beta-roots[i]) then
      stack := RootPartitions(i,beta-roots[i]);
      for this in stack do
        Add(this,i);
        if not this in part then Add(part,this);fi;
      od;
    fi;
  od;

  return part;
end;

# This returns all good words for a given element of Q_+

GoodWords := function(beta) local part,ans,this,r;
  part := RootPartitions(beta);
  ans := [];
  for this in part do
    Add(ans,[]);
    for r in this do
      Append(ans[Length(ans)], lyndon[r]);
    od;
  od;
  Sort(ans);
  return ans;
end;

#####
# Every (good) word has a unique factorization into a weakly decreasing sequence of (good) Lyndon words

IsLyndon := function(w) local i,j,factor;
  for j in Reversed([2..Length(w)]) do
    factor := []; for i in [j..Length(w)] do Add(factor,w[i]);od;
     if w >= factor then return false;fi;
  od;
  return true;
end;

CheckFactorization := function(w) local i;
  for i in [1..Length(w)-1] do
    if w[i] < w[i+1] then return false;fi;
  od;
  for i in [1..Length(w)] do
    if not IsLyndon(w[i]) then return false;fi;
  od;
  return true;
end;

# I think this finds the canonical factorization of a word but I wasn't sure so I
# added some check in...
# Now its Duval's slick algorithm so believe it!

Factorize := function(w) local subw,i,j,k,ans,words,start,this,n;
  ans := [];
  n := Length(w);
  k := 0;
  while k < n do
    i := k+1; j := k+2;
    while j <= n and w[i] <= w[j] do
      if w[i] < w[j] then i := k+1; else i := i+1;fi;
      j := j+1;
    od;
    repeat k := k+j-i; Add(ans,k); until k >= i;
  od;
  words := [];
  for i in [1..Length(ans)] do
    if i > 1 then start := ans[i-1]+1;else start := 1;fi;
    this:=[];
    for j in [start..ans[i]] do Add(this,w[j]);od;
    Add(words,this);
  od;
  Assert(0,CheckFactorization(words));
  return words;
end;

# Check that a word is good, i.e. all the lyndon words in its factorixation are good

IsGood := function(w) local i;
  for i in Factorize(w) do
    if not i in lyndon then return false;fi;
  od;
  return true;
end;

IsGoodLyndon := function(w)
  return IsLyndon(w) and IsGood(w);
end;

#####
# Now things are getting serious. We're trying to find the characters of the cuspidals by induction on height
# For a given height, take the smallest good word. By shuffle product 

ListInsert := function(list,pos,val) local ans,j;
  ans := [];
  for j in [1..pos-1] do Add(ans,list[j]);od;
  Add(ans,val);
  for j in [pos..Length(list)] do Add(ans,list[j]);od;
  return ans;
end;

InvertPermutation := function(perm) local ans,i;
  ans := [];
  for i in [1..Length(perm)] do
    ans[perm[i]] := i;
  od;
  return ans;
end;

ShufflePermutations := function(blocks) local ans,m,this,subans,subblocks,i;
  if Length(blocks) = 0  then return [[]];fi;
  subblocks := ShallowCopy(blocks);
  Unbind(subblocks[Length(subblocks)]);
  subans := ShufflePermutations(subblocks);
  ans := [];
  for m in Combinations([1..Sum(blocks)],blocks[Length(blocks)]) do
    for this in subans do
      for i in [1..Length(m)] do 
        this := ListInsert(this,m[i],Sum(subblocks)+i);
      od;
      Add(ans,this);
    od;
  od;
  return ans;
end;

InverseShufflePermutations := function(blocks)
  return List(ShufflePermutations(blocks),InvertPermutation);
end;

## e.g. WordShuffle([[2],[1]]) = (2,1) + q (1,2)

WordShuffle := function(w) local blocks,i,perms,ans,p,this,cf,concatenated,j;
  blocks := [];
  concatenated := [];
  for i in w do Add(blocks,Length(i));Append(concatenated,i);od;
  perms := InverseShufflePermutations(blocks);
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


### Either pass a sequence of MVPs or a list of MVPs

Shufffle := function(arg) local lengths,places,ans,cf,w,i;
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
    ans := ans + cf * WordShuffle(w);
  od;
  return ans;
end;

# This takes x and y and computes y-coeff of x_1 *... * x_n

FullShuffleCoefficient := function(x,y) local bit,n,ans,i,j,xx,yy;
  Assert(0,WordToAlpha(x)=WordToAlpha(y));
  if Length(x) = 0 then return q^0;fi;
  n := Length(x);
  xx := ShallowCopy(x); Unbind(xx[n]);
  ans := 0*q;
  for i in [1..n] do
    if y[i] = x[n] then
      yy := [];
      bit := q^0;
      for j in [i+1..n] do
        bit := bit * q^(-d[x[n]]*a[x[n]][y[j]]);
      od;
      for j in [1..i-1] do Add(yy,y[j]);od;
      for j in [i+1..n] do Add(yy,y[j]);od;
      ans := ans + bit*FullShuffleCoefficient(xx,yy);
    fi;
  od;
  return ans;
end;

#####
# This computes the Lyndon basis for a given Lyndon word

CostandardFactorization := function(w) local i,subw,neww,j;
  Assert(0,Length(w) > 1);
  subw := ShallowCopy(w);
  for i in Reversed([2..Length(subw)]) do
    Unbind(subw[i]);
    if IsLyndon(subw) then
      neww := [];
      for j in [i..Length(w)] do Add(neww,w[j]);od;
      return [subw,neww];
    fi;
  od;
  Assert(0,false);
end;

WordBracket := function(w1,w2,sign)
  return Concatenate(w1,w2)-q^(sign*InnerProduct(WordToAlpha(w1),WordToAlpha(w2)))*Concatenate(w2,w1);
end;

Bracket := function(mvp1,mvp2,sign) local lengths,places,ans,w1,w2;
  lengths := [[1..Length(mvp1!.coeff)],[1..Length(mvp2!.coeff)]];
  ans := ZeroWord();
  for places in Cartesian(lengths) do
    w1 := MvpUnpack(mvp1!.elm[places[1]][1][1]);
    w2 := MvpUnpack(mvp2!.elm[places[2]][1][1]);
    ans := ans + mvp1!.coeff[places[1]]*mvp2!.coeff[places[2]]*WordBracket(w1,w2,sign);
  od;
  return ans;
end;

## This returns the basis element [g] essentially as in Leclerc (with q replaced by q^{sign}) for lyndon word g

Monomial := function(goodword,sign) local cf;
  Assert(0,IsLyndon(goodword));
  if Length(goodword)=1 then return Word(goodword);fi;
  cf := CostandardFactorization(goodword);
  return Bracket(Monomial(cf[1],sign),Monomial(cf[2],sign),sign);
end;

# This is Bernard's normalization from RHS of (28) in his paper (tweaked a bit by some guesswork)

NormalizationScalar := function(goodword) local beta,scalar,i;
  beta := WordToAlpha(goodword); 
  scalar := (1-q^NormSquared(beta));
  for i in [1..Length(beta)] do
    scalar := scalar / ((1-q^(2*d[i]))^(beta[i]));
  od;
  return scalar;
end;

# This returns the dual PBW basis element for good lyndon word --- which is the dual canonical basis already! Except it needs to be scaled by NormalizationScalar then divided by kappa to get exactly
# the right thing...

CuspidalTimesKappa := function(goodword) local mon,ans,i,j,this;
  mon := Monomial(goodword,-1);
  ans := ZeroWord();
  for i in [1..Length(mon!.coeff)] do
    this := [];
    for j in MvpUnpack(mon!.elm[i][1][1]) do
      Add(this,[j]);
    od;
    ans := ans + mon!.coeff[i] * WordShuffle(this);
  od;
  return ans*NormalizationScalar(goodword);
end;

# UnscaledCuspidal takes too long. This just works out a particular coefficient which might
# be a tad quicker if you don't actually need the cuspidal character

CuspidalTimesKappaCoefficient := function(goodword,wantedone) local mon,ans,i,j;
  mon := Monomial(goodword,-1);
  ans := 0*q;
  for i in [1..Length(mon!.coeff)] do
    ans := ans + mon!.coeff[i] * FullShuffleCoefficient(MvpUnpack(mon!.elm[i][1][1]),wantedone);
  od;
  return ans*NormalizationScalar(goodword);
end;

## This computes kappa for a good lyndon word
# Its the square root of the coefficient of goodlyndon in dual PBW scaled.
# This is roughly what is written in Leclerc 5.5.2 but I tweaked a few things.
# Unfortunately it gets too slow already for E_7...

GoodKappa := function(goodlyndon) local beta,kappa,i;
  Assert(0,IsGoodLyndon(goodlyndon));
  for i in [1..Length(kappas)] do
    if kappas[i][1] = goodlyndon then return kappas[i][2];fi;
  od;
  if HomogeneousCharacter(goodlyndon) <> fail then kappa := q^0;
  else 
    kappa := FakeSquareRoot(CuspidalTimesKappaCoefficient(goodlyndon,goodlyndon));
  fi;
  Add(kappas, [goodlyndon, kappa]);
  return kappa;
end;

CuspidalCharacter := function(root) local goodlyndon,i,found,ans,kappa;
  goodlyndon := Lyndon(root);
  for i in [1..Length(characters)] do
    if characters[i][1] = root then return characters[i][2];fi;
  od;
  if Maximum(d) = 1 then		# Might be a homogeneous one!
    ans := HomogeneousCharacter(goodlyndon);
    if ans <> fail then
      Add(characters, [root,ans]);
      return ans;
    fi;
  fi;
  ans := CuspidalTimesKappa(goodlyndon);
  kappa := FakeSquareRoot(GetCoefficient(ans,goodlyndon));
  ans := ans / kappa;
  Add(characters, [root,ans]);
  found:=false;
  for i in [1..Length(kappas)] do
    if kappas[i][1] = goodlyndon then Assert(0,kappas[i][2]=kappa);found:=true;fi;
  od;
  if not found then Add(kappas,[goodlyndon,kappa]);fi;
  return ans;
end;

# This computes kappa for a good word using formula (19) from Bernard
# Actually I don't need this scalar every... but it makes
# the PBW basis computable: E_g = 1/kappa_g bar(monomial(g)) or something like that

Kappa := function(good) local cuspidals,kappa,mult,i,beta,deg;
  cuspidals := Factorize(good);
  kappa := q^0;
  mult := 1;
  for i in [1..Length(cuspidals)] do
    if i < Length(cuspidals) and cuspidals[i] = cuspidals[i+1] then mult := mult + 1;
    else 
      beta := WordToAlpha(cuspidals[i]);
      deg := NormSquared(beta)/2;
      kappa := kappa * GoodKappa(cuspidals[i])^mult * QuantumInteger(mult,deg); mult := 1;
    fi;
  od;
  return kappa;
end;



#####
# This returns the full character of a standard module with given highest good word

StandardCharacter := function(goodword) local i,cuspidals,substandards,ans,shift,mult;
  cuspidals := List(Factorize(goodword),WordToAlpha);
  shift := 0;
  mult := 1;
  for i in [1..Length(cuspidals)] do
    if i < Length(cuspidals) and cuspidals[i] = cuspidals[i+1] then mult := mult + 1;
    else shift := shift + NormSquared(cuspidals[i]) * mult * (mult-1) / 4; mult := 1;
    fi;
  od;
  substandards := [];
  for i in cuspidals do
    Add(substandards,CuspidalCharacter(i));
  od;
  ans := q^shift * Shufffle(substandards);
  return ans;
end;

# This by the way is exactly the dual PBW basis in Leclerc...

CostandardCharacter := function(goodword) local i,cuspidals,substandards,ans,shift,mult;
  cuspidals := List(Factorize(goodword),WordToAlpha);
  shift := 0;
  mult := 1;
  for i in [1..Length(cuspidals)] do
    if i < Length(cuspidals) and cuspidals[i] = cuspidals[i+1] then mult := mult + 1;
    else shift := shift + NormSquared(cuspidals[i]) * mult * (mult-1) / 4; mult := 1;
    fi;
  od;
  substandards := [];
  for i in cuspidals do
    Add(substandards,CuspidalCharacter(i));
  od;
  ans := q^(-shift) * Shufffle(Reversed(substandards));
  return ans;
end;

# Given a character this discards all but the "good" part

Good := function(character) local newcharacter,i,word;
  newcharacter := ZeroWord();
  for i in [1..Length(character!.elm)] do
    word := MvpUnpack(character!.elm[i][1][1]);
    if IsGood(word) then newcharacter := newcharacter + character!.coeff[i] * Word(word);fi;
  od;
  return newcharacter;
end;

####
# This code implements the algorithm to take
# a given bar-invariant polynomial kappa and d in qZ[q] and m bar invariant
# such that d kappa + m is known, it works out d and m.

DM := function(laurent,kappa) local dmv,n,m,r,a,b;
  if laurent = 0*q then return [0*q,0*q];fi;
  n := -CoefficientsOfLaurentPolynomial(laurent)[2];
  a := CoefficientsOfLaurentPolynomial(laurent)[1];
  m := -n+Length(a)-1;
  if m = 0 and n = 0 then return [0*q,a[1]*q^0];fi;
  r := -CoefficientsOfLaurentPolynomial(kappa)[2];
  b := CoefficientsOfLaurentPolynomial(kappa)[1][1];
  if m > n then
    dmv := DM(laurent-a[Length(a)]* q^(m-r)*kappa/b,kappa);
    dmv[1] := dmv[1]+a[Length(a)] * q^(m-r) / b;
  else
    dmv := DM(laurent-a[1]*q^(-n)-a[1]*q^n,kappa);
    dmv[2] := dmv[2]+a[1]*q^(-n)+a[1]*q^n;
  fi;
  return dmv;
end;

####
# Now for the algorithm to compute (a) the good part of the irreducible characters
# and (b) decomposition matrix of standard modules

# This is done as follows. First find the good words in the block in order, smallest to largest.
# Then find the good part of the standard characters stored in a list in the same order
# The bottom one in this list is already irreducible; make the first column of the decomposition
# matrix equal to e_1
# Now go from 2 to the end and work out the remaining columns and characters.
# At k-th step, look at (k-1)th coefficient in standard character.
# work out d and m from above algorithm taking kappa to be the top coefficient in the
# already found irreducible character for k-1.
# The d goes in k-1-th row of k-th row of decomp matrix.
# Then we subtract d*L(k-1) from k-th character.
# repeat with k-2...1

Compute := function(bl) local i,identity,j,dec;
  if block = bl then return;fi;
  block := 0;
  D := [];
  IC := [];
  SC := [];
  goodwords := GoodWords(bl);
  identity := [];
  for i in [1..Length(goodwords)] do 
    Add(identity,0*q);
  od;
  for i in [1..Length(goodwords)] do
    Add(D,ShallowCopy(identity));
    Add(IC,StandardCharacter(goodwords[i]));
    Add(SC,StructuralCopy(IC[Length(IC)]));
    Assert(0,IsBarInvariant(GetCoefficient(IC[i],goodwords[i])));
  od;
  for i in [1..Length(goodwords)] do
    D[i][i] := q^0;
    for j in Reversed([1..i-1]) do
      dec := DM(GetCoefficient(IC[i],goodwords[j]),GetCoefficient(IC[j],goodwords[j]))[1];
      D[j][i] := dec;
      IC[i] := IC[i]-dec*IC[j];
      Assert(0,IsBarInvariant(GetCoefficient(IC[i],goodwords[j])));
    od;
  od;
  block := bl;
end;

#####
# OK so I nearly have everything!
# I would like to write the E(i) in terms of the P(i) for good words i.
# So let's build a matrix whose j-th col is E(j) in terms of P(i)'s
# the ij-entry of this matrix is qdim Hom(E(j),L(i)) = qdim e(j) L(i)
# i.e. the j-coefficient of the i-th entry of IC
# Then the inverse of that matrix has cols giving P(j) in terms of E(i)'s

EtoP := function(block) local m,i,j;
  Compute(block);
  m := [];
  for i in [1..Length(goodwords)] do
    Add(m,[]);
    for j in [1..Length(goodwords)] do
      m[i][j] := GetCoefficient(IC[i],goodwords[j]);
    od;
  od;
  return m;
end;

PtoE := function(block)
  return EtoP(block)^(-1);
end;

# Also this is the matrix whose j-th col is E(j) expressed in terms of good words
# Observe it is just EtoP transpose!

LtoW := function(block) local m,i,j;
  Compute(block);
  m := [];
  for i in [1..Length(goodwords)] do
    Add(m,[]);
    for j in [1..Length(goodwords)] do
      m[i][j] := GetCoefficient(IC[j],goodwords[i]);
    od;
  od;
  return m;
end;

StoW := function(block) local m,i,j;
  Compute(block);
  m := [];
  for i in [1..Length(goodwords)] do
    Add(m,[]);
    for j in [1..Length(goodwords)] do
      m[i][j] := GetCoefficient(SC[j],goodwords[i]);
    od;
  od;
  return m;
end;

WtoL := function(block)
  return LtoW(block)^(-1);
end;

WtoS := function(block)
  return StoW(block)^(-1);
end;


# Now the main new work is to go from E to W
# We want the matrix whose j-th col is E(j) expressed in terms of good words,
# i.e. ij entry is qdim e(i) R e(j)
# This is a matter of finding all w such that e(i) psi_w  = psi_w e(j)
# and computing the degree... then its that times prod_{k in i}(1-q^(2d_k))^(-1)
# which I'll omit as its something global

EtoW := function(block) local i,j,m;
  Compute(block);
  m := [];
  for i in [1..Length(goodwords)] do
    Add(m,[]);
    for j in [1..Length(goodwords)] do
      m[i][j] := FullShuffleCoefficient(goodwords[i],goodwords[j]);
    od;
  od;
  for i in goodwords[1] do
    m := m / (1-q^(2*d[i]));
  od;
  return m;
end;

WtoE := function(block) 
  return EtoW(block)^(-1);
end;

PtoL := function(block)
  return WtoL(block)*EtoW(block)*PtoE(block);
end;

PtoS := function(block)
  return WtoS(block)*EtoW(block)*PtoE(block);
end;

EtoL := function(block)
  return WtoL(block)*EtoW(block);
end;

LtoE := function(block)
  return WtoE(block)*LtoW(block);
end;

StoE := function(block)
  return WtoE(block)*StoW(block);
end;

LtoP := function(block)
  return PtoL(block)^(-1);
end;

StoP := function(block)
  return PtoS(block)^(-1);
end;

PrettyPrint := function() local w,al,k,ka,bad;
#  Print("\nHere are the good Lyndon words:\n");
  bad := false;
  for w in lyndon do 
    k := HomogeneousCharacter(w);
    Print("\nRoot ", WordToAlpha(w), " <-> Lyndon word ", w);
   if k <> fail then Print(" homogeneous <-> kappa=1");fi;
    if k = fail then
      ka := GoodKappa(w);
      if ka <> q^0 then Error("BAD KAPPA!");fi;
      Print(" NOT homogeneous <-> kappa=", ka, "\n");
#      Print(" NOT homogeneous"); 
      bad := true;
    fi;
    if Length(w) > 1 and Length(CostandardFactorization(w)[2]) > 1 then 
      Print(" BAD FACTORIZATION\n");
      bad:=true;
    else 
      Print("\n");
    fi;
  od;
  if not bad then 
    Print(a,"\n");
    Add(goodies,StructuralCopy(a));
  fi;
  Print("\n");
return;
  Compute(highestroot);
  Print("\nHere are the cuspidal characters:\n");
  for w in characters do
    Print("Root=", w[1],".\n");
    Print(w[2],"\n");
  od;
  Print("\nHere are all the irreducible characters:\n");
  for al in roots do
    Print("Block ", al, ":\n");
    Compute(al);
    for w in IC do
      Print(w, ".\n");
    od;
  od;
end;

# This works out kappas FOR ALL orderings

AllOrderings := function() local b,e,this,counter;
  counter:=1;
  goodies := [];
  b := StructuralCopy(a); e := StructuralCopy(d);
  for this in Arrangements([1..Length(a)],Length(a)) do
    a := StructuralCopy(b); d := StructuralCopy(e);
    CartanPermute(this);
    PrettyPrint();
    Print(counter, "/",Factorial(Length(a)),"\n");counter:=counter+1;
  od;
end;
  

##############
# This code takes
# a good lyndon word i
# and finds its costandard factorization jk
# Then we look at the shuffle of L(j) L(k)
# and find all dominant words appearing in that.
# Expect only jk and kj...

DominantWords := function(ch) local i,this,dw;
  dw := [];
  for i in [1..Length(ch!.elm)] do
    this := MvpUnpack(ch!.elm[i][1][1]);
    if IsGood(this) then Add(dw, ShallowCopy(this));fi;
  od;
  return dw;
end;

DominantWordsInShuffle := function(i) local ii,a,b;
  ii := CostandardFactorization(i);
  a := CuspidalCharacter(WordToAlpha(ii[1]));
  b := CuspidalCharacter(WordToAlpha(ii[2]));
  return DominantWords(Shufffle(a,b));
end;

DominantE8 := function() local a,i,jbar,k;
  SetCartan("e",8);
  a := HomogeneousCharacter([1,2,3,4,5,8,6,7,5,6,4,5,3,4,2,3]);
  for i in [1..Length(a!.elm)] do
    jbar := MvpUnpack(a!.elm[i][1][1]);
    k := [1,2,3,4,5,8,6,7,5,6,4,5,8];
    Append(k,jbar);
    Print(k, " is ", IsGood(k), "\n");
  od;
end;
   

ScanAll := function() local i,ans;
  for i in lyndon do
    if Length(i) > 1 then 
      Print("Testing ", i, "\n");
      ans := DominantWordsInShuffle(i);
      Print(ans[1],"+",ans[2]);
      if Length(ans) > 2  then Error(ans);fi;
      Print("OK\n");
    fi;
  od;
end;

##############
# Here I want to compute \bar\theta_i for a dominant lyndon word i
# My conjectural algorithm: list all words j <= i of same weight; put a coefficient of 1 on i
# Go through in descending order and scan the Serre relation for each word. Whenever you find one 
# where all but one coefficient is known you can complete the final coefficient.
# Iterate and hope the process terminates!

# This generates list of all j <= i in descending order

GenBelow := function(i) local j,k,a,b,words,first;
  if Length(i) <= 1 then return [i];fi;

# First find all the lower ones that start with the same letter

  j := [];
  for a in [2..Length(i)] do Add(j,i[a]);od;
  words := [];
  for j in GenBelow(j) do
    k := [i[1]]; Append(k,j); Add(words, k);
  od;

# Now find all smaller letters in the word and do the ones which start with that smaller letter

  for a in Reversed([1..i[1]-1]) do
    j := []; first := true;
    for b in i do
      if b = a and first then first := false;
      else Add(j,b);
      fi;
    od;
    if not first then
      for j in Reversed(Arrangements(j, Length(j))) do
        k := [a]; Append(k,j); Add(words,k);
      od;
    fi;
  od;

  return words;
end;

PullCoeff := function(k,w,c) local i;
  for i in [1..Length(w)] do
    if w[i] = k then
      if IsBound(c[i]) then return c[i];else return fail;fi;
    fi;
  od;
  return 0;  
end;

# Now the main algorithm. Note i must be dominant lyndon to have any chance for the algorithm to work...
# and even then the chances are it gets stuck... 

ComputeBarTheta := function(i) local words, coeffs, ans, done,x,j,k,cf,pos,cf2,unbound,cf3,cf4,action,print;
  print := false;

  words := GenBelow(i);
  coeffs := [1];
  unbound := Length(words)-1;
  while unbound > 0 do

# Go through the words in the list without coefficient

    action := false;
    for x in [2..Length(words)] do
      if not IsBound(coeffs[x]) then
        done := false;

# Ok here's a word whose coefficient is known, that is a start!

# First I'm coding the commuting Serre relation, so scan ij pairs with a_{ij} = 0; then look for ij pair in the word
# such that the corresponding ji word is known

        for i in [1..Length(a)] do for j in [1..Length(a)] do if a[i][j] = 0 then
	  
# Here we go looking for ij

          if not done then for pos in [1..Length(words[x])-1] do
	    if not done and words[x][pos] = i and words[x][pos+1] = j then
	      k := ShallowCopy(words[x]);k[pos]:=j;k[pos+1]:=i;
	      cf:=PullCoeff(k,words,coeffs);
	      if cf <> fail then 
	        coeffs[x] := cf;
		done := true;unbound:=unbound-1;
		action:=true;
	      fi;
	    fi;
 	  od;fi;
        fi;od;od;

# Next the iij Serre relation

        if not done then for i in [1..Length(a)] do for j in [1..Length(a)] do if a[i][j] = -1 then
	  
# Here we go looking for iij

          if not done then for pos in [1..Length(words[x])-2] do
	    if not done and words[x][pos] = i and words[x][pos+1] = i and words[x][pos+2]=j then
	      k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=j;k[pos+2]:=i;
	      cf:=PullCoeff(k,words,coeffs);
	      if cf <> fail then 
  	        k := ShallowCopy(words[x]);k[pos]:=j;k[pos+1]:=i;k[pos+2]:=i;
	        cf2:=PullCoeff(k,words,coeffs);
		if cf2 <> fail then
		  coeffs[x] := (q^(d[i])+q^(-d[i]))*cf - cf2; 
		  done := true;
 		  action:=true;
		  unbound:=unbound-1;
		  if print then Print(words[x],"=",coeffs[x],":", i, i, j, "\n");fi;
		fi;
	      fi;
	    fi;
 	  od;fi;

# Here we go looking for jii

          if not done then for pos in [1..Length(words[x])-2] do
	    if not done and words[x][pos] = j and words[x][pos+1] = i and words[x][pos+2]=i then
	      k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=j;k[pos+2]:=i;
	      cf:=PullCoeff(k,words,coeffs);
	      if cf <> fail then 
  	        k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=i;k[pos+2]:=j;
	        cf2:=PullCoeff(k,words,coeffs);
		if cf2 <> fail then
		  coeffs[x] := (q^(d[i])+q^(-d[i]))*cf - cf2; 
		  done := true;
 		  action:=true;
		  unbound:=unbound-1;
		  if print then Print(words[x],"=",coeffs[x], ":",j,i,i,"\n");fi;
		fi;
	      fi;
	    fi;
 	  od;fi;

# Here we go looking for iji

          if not done then for pos in [1..Length(words[x])-2] do
	    if not done and words[x][pos] = i and words[x][pos+1] = j and words[x][pos+2]=i then
	      k := ShallowCopy(words[x]);k[pos]:=j;k[pos+1]:=i;k[pos+2]:=i;
	      cf:=PullCoeff(k,words,coeffs);
	      if cf <> fail then 
  	        k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=i;k[pos+2]:=j;
	        cf2:=PullCoeff(k,words,coeffs);
		if cf2 <> fail then
		  coeffs[x] := (cf+cf2) / (q^(d[i])+q^(-d[i])); 
		  done := true;
 		  action:=true;
		  unbound:= unbound-1;
		  if print then Print(words[x],"=",coeffs[x],":", i,j,i, "\n");fi;
		fi;
	      fi;
	    fi;
 	  od;fi;
        fi;od;od;fi;

# Here with a_ij = -2

# Next the iij Serre relation

        if not done then for i in [1..Length(a)] do for j in [1..Length(a)] do if a[i][j] = -2 then
	  
# Here we go looking for iiij

          if not done then for pos in [1..Length(words[x])-3] do
	    if not done and words[x][pos] = i and words[x][pos+1] = i and words[x][pos+2]=i and words[x][pos+3]=j then
	      k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=i;k[pos+2]:=j;k[pos+3]:=i;
	      cf:=PullCoeff(k,words,coeffs);
	      if cf <> fail then 
  	        k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=j;k[pos+2]:=i;k[pos+3]:=i;
	        cf2:=PullCoeff(k,words,coeffs);
		if cf2 <> fail then
     	          k := ShallowCopy(words[x]);k[pos]:=j;k[pos+1]:=i;k[pos+2]:=i;k[pos+3]:=i;
  	          cf3:=PullCoeff(k,words,coeffs);
		  if cf3 <> fail then
  		    coeffs[x] := cf3 + (q^(2*d[i])+1+q^(-2*d[i]))*(cf - cf2); 
		    done := true;
 		    action:=true;
		    unbound:=unbound-1;
		    if print then Print(words[x],"=",coeffs[x],":", i, i, i,j, "\n");fi;
		  fi;
		fi;
	      fi;
	    fi;
 	  od;fi;

# Here we go looking for iiji

          if not done then for pos in [1..Length(words[x])-3] do
	    if not done and words[x][pos] = i and words[x][pos+1] = i and words[x][pos+2]=j and words[x][pos+3]=i then
	      k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=i;k[pos+2]:=i;k[pos+3]:=j;
	      cf:=PullCoeff(k,words,coeffs);
	      if cf <> fail then 
  	        k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=j;k[pos+2]:=i;k[pos+3]:=i;
	        cf2:=PullCoeff(k,words,coeffs);
		if cf2 <> fail then
     	          k := ShallowCopy(words[x]);k[pos]:=j;k[pos+1]:=i;k[pos+2]:=i;k[pos+3]:=i;
  	          cf3:=PullCoeff(k,words,coeffs);
		  if cf3 <> fail then
  		    coeffs[x] := cf2 + (cf - cf3)/(q^(2*d[i])+1+q^(-2*d[i])); 
		    done := true;
 		    action:=true;
		    unbound:=unbound-1;
		    if print then Print(words[x],"=",coeffs[x],":", i, i, j,i, "\n");fi;
		  fi;
		fi;
	      fi;
	    fi;
 	  od;fi;

# Here we go looking for ijii

          if not done then for pos in [1..Length(words[x])-3] do
	    if not done and words[x][pos] = i and words[x][pos+1] = j and words[x][pos+2]=i and words[x][pos+3]=i then
	      k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=i;k[pos+2]:=i;k[pos+3]:=j;
	      cf:=PullCoeff(k,words,coeffs);
	      if cf <> fail then 
  	        k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=i;k[pos+2]:=j;k[pos+3]:=i;
	        cf2:=PullCoeff(k,words,coeffs);
		if cf2 <> fail then
     	          k := ShallowCopy(words[x]);k[pos]:=j;k[pos+1]:=i;k[pos+2]:=i;k[pos+3]:=i;
  	          cf3:=PullCoeff(k,words,coeffs);
		  if cf3 <> fail then
  		    coeffs[x] := cf2 + (cf3 - cf)/(q^(2*d[i])+1+q^(-2*d[i])); 
		    done := true;
 		    action:=true;
		    unbound:=unbound-1;
		    if print then Print(words[x],"=",coeffs[x],":", i, j, i,i, "\n");fi;
		  fi;
		fi;
	      fi;
	    fi;
 	  od;fi;

# Here we go looking for jiii

          if not done then for pos in [1..Length(words[x])-3] do
	    if not done and words[x][pos] = j and words[x][pos+1] = i and words[x][pos+2]=i and words[x][pos+3]=i then
	      k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=i;k[pos+2]:=i;k[pos+3]:=j;
	      cf:=PullCoeff(k,words,coeffs);
	      if cf <> fail then 
  	        k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=i;k[pos+2]:=j;k[pos+3]:=i;
	        cf2:=PullCoeff(k,words,coeffs);
		if cf2 <> fail then
     	          k := ShallowCopy(words[x]);k[pos]:=i;k[pos+1]:=j;k[pos+2]:=i;k[pos+3]:=i;
  	          cf3:=PullCoeff(k,words,coeffs);
		  if cf3 <> fail then
  		    coeffs[x] := cf + (q^(2*d[i])+1+q^(-2*d[i]))*(cf3 - cf2); 
		    done := true;
 		    action:=true;
		    unbound:=unbound-1;
		    if print then Print(words[x],"=",coeffs[x],":", j,i, i, i, "\n");fi;
		  fi;
		fi;
	      fi;
	    fi;
 	  od;fi;
        fi;od;od;fi;

# Note the above are all we need for G_2...

      fi;
    od;
    if action = false then Error("Stuck in loop\n");fi;
  od;

# Return the answer

  ans := 0;
  for x in [1..Length(words)] do
    if IsBound(coeffs[x]) then ans := ans + coeffs[x] * Word(words[x]);fi;
  od;
  return ans;
end;

AltComputeBarTheta := function(i) local j,k,s,lambda,beta,gamma,t;
  if Length(i) = 1 then return Word(i);fi;

  if i in store then
    for j in [1..Length(store)] do
      if store[j] = i then return stored[j];fi;
    od;
  fi;

  j := CostandardFactorization(i)[1];
  k := CostandardFactorization(i)[2];
  s := Shufffle(AltComputeBarTheta(k), AltComputeBarTheta(j));
  beta := WordToAlpha(j); gamma := WordToAlpha(k);
  t := q^(InnerProduct(beta,gamma))*Shufffle(AltComputeBarTheta(j), AltComputeBarTheta(k));
  lambda := GetCoefficient(s,i);
  Add(store, i); Add(stored, (s-t) / (lambda-BarLaurent(lambda)));
  return stored[Length(stored)];
end;

##############
# Code to compute lamdas and mus

LambdaMu := function() local i,j,k,di,dj,dk,alpha,beta,gamma,thetaj, thetak,s,lambda,mu,bad,w,iprime,counter,predict,nu,quicky;
  for i in lyndon do
    if Length(i) > 1 then 
      alpha := WordToAlpha(i); 
      di := EuclideanQuotient(InnerProduct(alpha,alpha),2);
      j := CostandardFactorization(i)[1];
      beta := WordToAlpha(j);
      dj := EuclideanQuotient(InnerProduct(beta,beta),2);
      k := CostandardFactorization(i)[2];
      gamma := WordToAlpha(k);
      dk := EuclideanQuotient(InnerProduct(gamma,gamma),2);

      quicky := false;
      if di = Minimum(dj,dk) and Length(k) = 1 and j[1] = Minimum(j) and beta[j[1]] = 1 then
        s := HomogeneousCharacter(j);
	if s <> fail then
	  quicky := true;
	  for counter in [1..Length(s!.elm)] do
	    w := MvpUnpack(s!.elm[counter][1][1]);
	    if w[Length(w)] = k[1] then quicky := false;fi;
	  od;
	fi;
      fi;

      if not quicky then 
      Print("\nDominant Lyndon word i = ", i, " (length ", di, ")\n");
      Print("j = ", j, " (length ", dj, ")\nk = ", k, " (length ", dk, ")\n");
#      Print("i orbit sum = ", AltComputeBarTheta(i), "\n");
      thetaj := AltComputeBarTheta(j); thetak := AltComputeBarTheta(k);
#      Print("j orbit sum = ", thetaj, "\n");
#      Print("k orbit sum = ", thetak, "\n");
      s := Shufffle(thetak, thetaj);
      lambda := GetCoefficient(s,i);
      Print("d_lambda = ", lambda - BarLaurent(lambda), "\n");
#      if lambda <> q then Error("Bad coefficient here");fi;

if dj = dk and dj > di then Error("Here long long short \n");fi;
if dj <> dk and di > 1 then Error("Here short long long \n");fi;
if dj > dk then Error("Here short long \n");fi;

      predict := QuantumInteger(EuclideanQuotient(Maximum(d)+InnerProduct(beta,gamma),2)+1,1);	# Conjecture for mu
      if predict^2 <> ((q^di - q^(-di)) * (lambda - BarLaurent(lambda)) / (q^dj - q^(-dj)) / (q^dk - q^(-dk))) then Error("Wrong prediction!");fi;
      mu := predict;
      Print("lambda = ", lambda,"\nmu = ", mu,"\n");
      iprime := ShallowCopy(k); Append(iprime, j);
      bad := true;
      for counter in [1..Length(s!.elm)] do
        w := MvpUnpack(s!.elm[counter][1][1]);
        if IsGood(w) and w <> i and w <> iprime then bad := false;fi;
      od;
      Print("The conjecture is ", bad ,"\n");
      if bad then 
        nu := q^EuclideanQuotient(Maximum(d)-InnerProduct(beta,gamma),2);
	if Maximum(d) = 3 and di = 1 and dj = 1 and dk = 1 then 
	  if mu <> QuantumInteger(2,1) then Error("Unexpected 1");fi;
	elif di > 1 and dj = 1 and dk = 1 then
	  if mu <> QuantumInteger(di,1) then Error("Unexpected 2");fi;
	else
	  if mu <> q^0 then Error("Unexpected 3");fi;
        fi;
      else Error("CONJECTURE FALSE HERE!\n");fi;
    fi;
    fi;  
  od;
end;





AllOrderingsLM := function() local b,e,this,counter;
  counter:=1;
  goodies := [];
  b := StructuralCopy(a); e := StructuralCopy(d);
  for this in Arrangements([1..Length(a)],Length(a)) do
    a := StructuralCopy(b); d := StructuralCopy(e);
    CartanPermute(this);
    LambdaMu();
    Print(counter, "/",Factorial(Length(a)),"\n");counter:=counter+1;
  od;
end;


#####
# This code finds all dominant words of given weight 

Dominates := function(root1, root2) local i;
  for i in [1..Length(a)] do
    if root1[i] < root2[i] then return false;fi;
  od;
  return true;
end;

# This simply finds all dominant words of given weight using roots <= upperroot

DominantWords := function(weight, upperroot) local ans,r,p,rc,this;
  if Sum(weight) = 0 then return [[]];fi;
  ans := [];
  for r in [1..upperroot] do
    if Dominates(weight, roots[r]) then
      rc := DominantWords(weight-roots[r],r);
      for p in rc do
        this := ShallowCopy(lyndon[r]);
	Append(this,p);
	Assert(0,IsGood(this));
	Add(ans,this);
      od;
    fi;
  od;
  return ans;
end;

# This finds all dominant words of given weight and prescribed first letter

DominantWordsStart := function(weight,letter) local ans,upperroot,this,sofar,p,new;
  ans := [];
  for upperroot in [1..Length(roots)] do
    if lyndon[upperroot][1] = letter then
      this := roots[upperroot];
      if Dominates(weight,this) then
        sofar := DominantWords(weight-this,upperroot);
	for p in sofar do
	  new := ShallowCopy(lyndon[upperroot]);
	  Append(new,p);
	  Add(ans,new);
	od;
      fi;            
    fi;
  od;
  return ans;
end;

# Find all dominant words strictly between i and j with first letter in given range; must have same weights

DominantWordsStrictlyBetween := function(i,j,firstletterrange) local ans,weight,letter,this;
  ans := [];
  weight := WordToAlpha(i);
  Assert(0, WordToAlpha(j)=weight);
  for letter in firstletterrange do
    for this in DominantWordsStart(weight,letter) do
      if this > i and this < j then Add(ans, this);fi;
    od;
  od;
  return ans;
end;


EpsilonScan := function() local i,j,k,iprime,potentials,this,new,okay,s,t,ch,w,count,restart,temp;
  for i in lyndon do
    if Length(i) > 1 then 
      j := CostandardFactorization(i)[1];
      k := CostandardFactorization(i)[2];
      iprime := ShallowCopy(k); 
      Append(iprime, j);

      if Length(k) = 1 then 

# When k is a singleton, I find everything between i and iprime starting with the same thing as j
# Then from them I remove a k in all possible ways and check the result is <= j...

        potentials := DominantWordsStrictlyBetween(i,iprime,[j[1]]);
	for this in [1..Length(potentials)] do
	  okay := false;
	  for s in [1..Length(potentials[this])] do
	    if potentials[this][s] = k[1] then
	      new := [];
	      for t in [1..s-1] do Add(new,potentials[this][t]);od;
	      for t in [s+1..Length(potentials[this])] do Add(new,potentials[this][t]);od;

# I've found a potential case! Does new appear in ch theta_j^*?
# I want to avoid computing the character here. But I can look at new and make it bigger using
# commuting Serre relations... if get anything bigger than j I'm done

Print(new,"\n");
  
	      restart := true;
  	      while restart do
	        restart := false; 
		for t in [1..Length(new)-1] do
		  if a[new[t]][new[t+1]] = 0 and new[t] < new[t+1] then
		    temp := new[t]; new[t] := new[t+1]; new[t+1] := temp; restart := true;
		  fi;
		od;
	      od;
	      if new <= j then

# Last resort which may get stuck

  Error("Stuck at ", j, " ", k, " (",potentials[this],")\n");
#  okay := true;

       	        ch := AltComputeBarTheta(j);
	        for count in [1..Length(ch!.elm)] do
		  w := MvpUnpack(ch!.elm[count][1][1]);
		  if w[1] = new then okay := true;fi;
	        od;
	      fi;
	    fi;
	  od;
	  if not okay then Unbind(potentials[this]);fi;
	od;

      else potentials := DominantWordsStrictlyBetween(i,iprime,[j[1]..k[1]]);
      fi;

      if potentials <> [] then
        Print("j = ", j, "\n");
        Print("k = ", k, "\n");
        Print(potentials, "\n");
      fi;
    fi; 
  od;
end;	

AllEpsilon := function() local b,e,this,counter;
  counter:=1;
  goodies := [];
  b := StructuralCopy(a); e := StructuralCopy(d);
  for this in Arrangements([1..Length(a)],Length(a)) do
    a := StructuralCopy(b); d := StructuralCopy(e);
    CartanPermute(this);
    EpsilonScan();
    Print(counter, "/",Factorial(Length(a)),"\n");counter:=counter+1;
  od;
end;


##############
# This is code to find minimal pairs (gamma > beta) for root alpha

Pairs := function(alpha) local gammaindex, betaindex, answer;
  answer := [];
  for betaindex in [1..Length(roots)-1] do for gammaindex in [betaindex+1..Length(roots)] do
    if roots[betaindex]+roots[gammaindex] = alpha then Add(answer, [roots[gammaindex],roots[betaindex]]);fi;
  od;od;
  return answer;
end;

PairSmaller := function(q,p) local q1,q2,p1,p2;
  q1 := Lyndon(q[1]); q2 := Lyndon(q[2]);
  p1 := Lyndon(p[1]); p2 := Lyndon(p[2]);
  if q1 > p1 then return false;fi;
  if q2 < p2 then return false;fi;
  return true;
end;

MinimalPairsUgly := function(alpha) local answer, p, q, minimal;
  answer := [];
  for p in Pairs(alpha) do
    minimal := true;
    for q in Pairs(alpha) do
      if q <> p then
        if PairSmaller(q,p) then minimal := false;fi;
      fi;
    od;
    if minimal then 
      Add(answer, [Lyndon(p[2]), Lyndon(p[1])]);
    fi;
  od;
  return answer;
end;


MinimalPairs := function(alpha) local answer, p, q, minimal,newroot,k,new,c;
  answer := [];
  Print("\n");
  for c in Lyndon(alpha) do Print(c);od;   
  Print("& ");
  for p in Pairs(alpha) do
    minimal := true;
    for q in Pairs(alpha) do
      if q <> p then
        if PairSmaller(q,p) then minimal := false;fi;
      fi;
    od;
    if minimal then 

      for c in Lyndon(p[2]) do Print(c);od;
      Print("|");
      for c in Lyndon(p[1]) do Print(c);od;
      Print(", ");

      new := ShallowCopy(Lyndon(p[1]));
      k := new[Length(new)];
      Unbind(new[Length(new)]);
      newroot := ShallowCopy(alpha); newroot[k] := newroot[k] - 1;
#      if new <> [] then
#        if not [Lyndon(p[2]),new] in MinimalPairsUgly(newroot) then
#	  Print("Not good for this one!\n");
#	fi;
#      fi;
    fi;
  od;
  Print("\n");
end;



##############
# default start block

if a = [] then SetCartan("g",2);fi;


