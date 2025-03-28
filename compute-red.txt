   D:=[]; 
  IC:=[]; 
  SC := [];
  ICcoeff := [];
  ICelm := [];
  SCelm := [];
  SCcoeff := [];
 ComputeRedP:= function(bl,first,last) local i,identity,j,dec,stringbl,Dfile,ICfile,SCfile,start;
Print(block,"\n");
if not block=bl then
Print(block," is not ",bl,"\n");
IC:=[];
 D:=[]; 
  SC := [];
 fi;
  goodwords := Reversed(GoodWordsRed2(bl));
  identity := [];
  for i in [1..Length(goodwords)] do 
    identity[i]:=0*q;
  od;
  for i in [1..last] do
    Print("trying ",i,"\n");
    if not IsBound(IC[i]) then
    Print("IsBound(IC[i]) is ",IsBound(IC[i]),"\n");
    Add(D,ShallowCopy(identity));
    Add(IC,StandardCharacterRed(goodwords[i]));
    Add(SC,StructuralCopy(IC[Length(IC)]));
    Assert(0,IsBarInvariant(GetCoefficient(IC[i],goodwords[i])));
    D[i][i] := q^0;
    for j in Reversed([1..i-1]) do
      dec := DM(GetCoefficient(IC[i],goodwords[j]),GetCoefficient(IC[j],goodwords[j]))[1];
      D[j][i] := dec;
      IC[i] := IC[i]-dec*IC[j];
      Assert(0,IsBarInvariant(GetCoefficient(IC[i],goodwords[j])));
    od;
 #   PrintTo(Dfile,D,"\n");
 #   PrintTo(ICfile,IC,"\n");
 #   PrintTo(SCfile,SC,"\n");
    Print("IC[",i,"] computed\n");
    fi;
  od;
  block := bl;
end;
 ComputeRed := function(bl) local i,identity,j,dec,stringbl,Dfile,ICfile,SCfile,start,m;
  m:=Length(bl);
  SetCartan("a",m);
  stringbl:=String(bl);
  RemoveCharacters(stringbl,"[], ");
  Dfile:=Filename(directory,Concatenation(stringbl,"D.out"));
  ICfile:=Filename(directory,Concatenation(stringbl,"IC.out"));
  SCfile:=Filename(directory,Concatenation(stringbl,"SC.out"));
     D:=[]; 
  IC:=[]; 
  SC := [];
  goodwords := Reversed(GoodWordsRed2(bl));
  identity := [];
  for i in [1..Length(goodwords)] do 
    Add(identity,0*q);
  od;
  for i in [1..Length(goodwords)] do
    Add(D,ShallowCopy(identity));
    Add(IC,StandardCharacterRed(goodwords[i]));
    Add(SC,StructuralCopy(IC[Length(IC)]));
    Assert(0,IsBarInvariant(GetCoefficient(IC[i],goodwords[i])));
    D[i][i] := q^0;
    for j in Reversed([1..i-1]) do
      dec := DM(GetCoefficient(IC[i],goodwords[j]),GetCoefficient(IC[j],goodwords[j]))[1];
      D[j][i] := dec;
      IC[i] := IC[i]-dec*IC[j];
      Assert(0,IsBarInvariant(GetCoefficient(IC[i],goodwords[j])));
    od;
    PrintTo(Dfile,D,"\n");
    PrintTo(ICfile,IC,"\n");
    PrintTo(SCfile,SC,"\n");
    Print("IC[",i,"] computed\n");
  od;
  block := bl;
end;
CheckNumber := function(n) local bl,rp;
  max:=0;
  SetCartan("a",n);
  bl := [1,2..n];
  rp := CountRPRed2(bl);
  return rp;
end;
LoadD := function(bl) local stringbl,Dfile;
  stringbl:=String(bl);
  RemoveCharacters(stringbl,"[], ");
   Dfile:=Filename(directory,Concatenation(stringbl,"D.out"));
  if IsExistingFile(Dfile) then
      Read(Dfile); 
  fi;
end;
LoadIC := function(bl) local stringbl,ICcoefffile,ICelmfile,j,x;
  stringbl:=String(bl);
  RemoveCharacters(stringbl,"[], ");
  ICelmfile:=Filename(directory,Concatenation(stringbl,"ICelm.out"));
  ICcoefffile:=Filename(directory,Concatenation(stringbl,"ICcoeff.out"));
  Print("does ",ICcoefffile, " exist? ",IsExistingFile(ICcoefffile),"\n");
  Print("does ",ICelmfile, " exist? ",IsExistingFile(ICelmfile),"\n");
  if IsExistingFile(ICcoefffile) then
      ICcoeff:=[];
      Read(ICelmfile);
    #   Print("ICelm is ",ICelm,"\n");
      Read(ICcoefffile);
   #    Print("ICcoeff is ",ICcoeff,"\n");
      for j in [1..Length(ICcoeff)] do
          if IsBound(ICelm[j]) then 
   #           IC[j]:=Sum([1..Length(ICelm[j])], x -> Mvp(ICelm[j][x],ICcoeff[j][x]));
              Print("IC[",j,"] loaded \n");
          fi;
      od; 
  fi;
end;
LoadSC := function(bl,zip) local stringbl,SCcoefffile,SCelmfile,j,x;
  stringbl:=String(bl);
  RemoveCharacters(stringbl,"[], ");
  SCelmfile:=Filename(directory,Concatenation(stringbl,"SCelm.out"));
  SCcoefffile:=Filename(directory,Concatenation(stringbl,"SCcoeff.out"));
  Print("does ",SCcoefffile, " exist? ",IsExistingFile(SCcoefffile),"\n");
  Print("does ",SCelmfile, " exist? ",IsExistingFile(SCelmfile),"\n");
  SC:=[];
  if IsExistingFile(SCcoefffile) then
      SCcoeff:=[];
         SCelm:=[];
      Read(SCelmfile);
   #    Print("SCelm is ",SCelm,"\n");
      Read(SCcoefffile);
   #    Print("SCcoeff is ",SCcoeff,"\n");
      if zip then 
      for j in [1..Length(SCcoeff)] do
          if IsBound(SCelm[j]) then             
              SC[j]:=Sum([1..Length(SCelm[j])], x -> Mvp(SCelm[j][x],SCcoeff[j][x]*q^0));
              Print("SC[",j,"] loaded \n");
          fi;
      od;
      fi; 
  fi;
end;
CheckSC := function(bl,p) local stringbl,SCcoefffile,SCelmfile,j,x;
  stringbl:=String(bl);
  RemoveCharacters(stringbl,"[], ");
  SCelmfile:=Filename(directory,Concatenation(stringbl,"SCelm.out"));
  SCcoefffile:=Filename(directory,Concatenation(stringbl,"SCcoeff.out"));
  Print("does ",SCcoefffile, " exist? ",IsExistingFile(SCcoefffile),"\n");
  Print("does ",SCelmfile, " exist? ",IsExistingFile(SCelmfile),"\n");
  SC:=[];
  if IsExistingFile(SCcoefffile) then
      SCcoeff:=[];
      Read(SCcoefffile);
      if IsBound(SCcoeff[p]) then
        Print("already have k=",p,"\n");
        return true;
      else return false;
      fi;
      else return false;
  fi;
end;

ComputeRedStop := function(bl) local i,identity,j,dec,stringbl,Dfile,ICfile,SCfile,start,ICcoefffile,ICelmfile,SCelmfile,SCcoefffile;
  if block = bl then return;fi;
  stringbl:=String(bl);
  RemoveCharacters(stringbl,"[], ");
  Dfile:=Filename(directory,Concatenation(stringbl,"D.out"));
  ICfile:=Filename(directory,Concatenation(stringbl,"IC.out"));
  SCfile:=Filename(directory,Concatenation(stringbl,"SC.out"));
#  ICelmfile:=Filename(directory,Concatenation(stringbl,"ICelm.out"));
  SCelmfile:=Filename(directory,Concatenation(stringbl,"SCelm.out"));
#  ICcoefffile:=Filename(directory,Concatenation(stringbl,"ICcoeff.out"));
  SCcoefffile:=Filename(directory,Concatenation(stringbl,"SCcoeff.out"));
#  LoadD(bl);
#  LoadIC(bl);
  LoadSC(bl,true);
  goodwords := Reversed(GoodWordsRed2(bl));
  identity := [];
  for i in [1..Length(goodwords)] do 
    Add(identity,0*q);
  od;
  Print("about to start computing ", Length(goodwords),"\n");
  for i in [1..Length(goodwords)] do
    Print("step ",i,"\n");
    if IsBound(SC[i]) then 
    Add(D,ShallowCopy(identity));
    Add(IC,StructuralCopy(SC[i]));
#    Print(IC[i]);
    Assert(0,IsBarInvariant(GetCoefficient(IC[i],goodwords[i])));
    D[i][i] := q^0;
    for j in Reversed([1..i-1]) do
#      Print("i=",i, "j=",j,"\nIC[i]=",IC[i],"\nIC[j]=", IC[j],"\n"); 
      dec := DM(GetCoefficient(IC[i],goodwords[j]),GetCoefficient(IC[j],goodwords[j]))[1];
      D[j][i] := dec;
      IC[i] := IC[i]-dec*IC[j];
      Assert(0,IsBarInvariant(GetCoefficient(IC[i],goodwords[j])));
    od;
    PrintTo(Dfile,D);
    PrintTo(ICfile,IC);
    PrintTo(SCfile,SC);
#    PrintTo(ICelmfile,"ICelm:= ",IC!.elm);
#    PrintTo(SCelmfile,"SCelm:= ",SC!.elm);
#   PrintTo(ICcoefffile,"ICcoeff:= ", IC!.coeff);
#    PrintTo(SCcoefffile,"SCcoeff:= ",SC!.coeff);
    else Print("Finished after ",i," characters\n"); return; fi;
  od;
  block := bl;
end;

ComputeStandardsM := function(bl,res,quo) local i,identity,j,k,lastres,dec,stringbl,Dfile,ICfile,SCfile,standard,ICcoefffile,ICelmfile,SCelmfile,SCcoefffile,x;
#   D:=[]; 
#   identity := [];
#  for j in [1..Length(goodwords)] do 
#    Add(identity,0*q);
#  od;
#  identity := [];
#  for j in [1..Length(goodwords)] do 
#    Add(D,identity);
#  od;
#  IC:=[]; 
  SC := [];
 block := 0;
  stringbl:=String(bl);
  RemoveCharacters(stringbl,"[], ");
#  Dfile:=Filename(directory,Concatenation(stringbl,"D.out"));
#  ICfile:=Filename(directory,Concatenation(stringbl,"IC.out"));
  SCfile:=Filename(directory,Concatenation(stringbl,"SC.out"));
#  ICelmfile:=Filename(directory,Concatenation(stringbl,"ICelm.out"));
  SCelmfile:=Filename(directory,Concatenation(stringbl,"SCelm.out"));
#  ICcoefffile:=Filename(directory,Concatenation(stringbl,"ICcoeff.out"));
  SCcoefffile:=Filename(directory,Concatenation(stringbl,"SCcoeff.out"));
  goodwords := Reversed(GoodWordsRed2(bl));
  Print("total number of standards is ",Length(goodwords),"\n");
  lastres := QuoInt(Length(goodwords)-res, quo)*quo+res;
  for k in [res,res+quo..lastres] do
      if CheckSC(bl,k) then  
        Print("already have k=",k,"\n");
        k:=k+quo;
      else
        Print("doing standard for k=",k," with word ",goodwords[k],"\n");
        standard:=StandardCharacterRed(goodwords[k]);
	LoadSC(bl,false);
               SCelm[k]:=StructuralCopy(standard)!.elm;
               SCcoeff[k]:=StructuralCopy(standard)!.coeff;
	     k:=k+quo;
    	PrintTo(SCfile,SC);
    	PrintTo(SCelmfile,"SCelm:= ",SCelm,";");
    	PrintTo(SCcoefffile,"SCcoeff:= ",SCcoeff,";");
     fi;
  od;
  block := bl;
end;



ComputeStandardsMold := function(bl,res,quo) local i,identity,j,k,dec,stringbl,Dfile,ICfile,SCfile,standard,ICcoefffile,ICelmfile,SCelmfile,SCcoefffile,x;
#   D:=[]; 
#   identity := [];
#  for j in [1..Length(goodwords)] do 
#    Add(identity,0*q);
#  od;
#  identity := [];
#  for j in [1..Length(goodwords)] do 
#    Add(D,identity);
#  od;
#  IC:=[]; 
  SC := [];
 block := 0;
  stringbl:=String(bl);
  RemoveCharacters(stringbl,"[], ");
#  Dfile:=Filename(directory,Concatenation(stringbl,"D.out"));
#  ICfile:=Filename(directory,Concatenation(stringbl,"IC.out"));
  SCfile:=Filename(directory,Concatenation(stringbl,"SC.out"));
#  ICelmfile:=Filename(directory,Concatenation(stringbl,"ICelm.out"));
  SCelmfile:=Filename(directory,Concatenation(stringbl,"SCelm.out"));
#  ICcoefffile:=Filename(directory,Concatenation(stringbl,"ICcoeff.out"));
  SCcoefffile:=Filename(directory,Concatenation(stringbl,"SCcoeff.out"));
  goodwords := Reversed(GoodWordsRed2(bl));
  k:=res;
  LoadSC(bl);
  while k <= Length(goodwords) do
      if IsBound(SC[k]) then  
        Print("already have k=",k,"\n");
        k:=k+quo;
      else
        Print("doing standard for k=",k," with word ",goodwords[k],"\n");
        SC[k]:=StandardCharacterRed(goodwords[k]);
        LoadSC(bl);
 #      LoadD(bl);
 #       LoadIC(bl);
      fi;
#    IC[k]:=StructuralCopy(standard);
#    if not IsBound(D[k]) then 
#        D[k]:=ShallowCopy(identity); 
#    fi;
#    D[k][k] := q^0;
#    for i in [1..Length(goodwords)] do
#        if ForAll([1..i],n ->  IsBound(IC[n])) then      
#          for j in Reversed([1..i-1]) do
#              Print("i=",i, "j=",j,"\nIC[i]=",IC[i],"\nIC[j]=", IC[j],"\n"); 
#              dec := DM(GetCoefficient(IC[i],goodwords[j]),GetCoefficient(IC[j],goodwords[j]))[1];
#              D[j][i] := dec;
#              IC[i] := IC[i]-dec*IC[j];
#              #Assert(0,IsBarInvariant(GetCoefficient(IC[i],goodwords[j])));
#          od;
#        fi;
#    od;
    for j in [1..Length(goodwords)] do
        if IsBound(SC[j]) then 
#            ICelm[j]:=StructuralCopy(IC[j])!.elm;
#            ICcoeff[j]:=StructuralCopy(IC[j])!.coeff;
            SCelm[j]:=StructuralCopy(SC[j])!.elm;
            SCcoeff[j]:=StructuralCopy(SC[j])!.coeff;
        fi;
    od;   
#    PrintTo(Dfile,"D:= ",D,";");
#    PrintTo(ICfile,IC);
    PrintTo(SCfile,SC);
#    PrintTo(ICelmfile,"ICelm:= ",ICelm,";");
    PrintTo(SCelmfile,"SCelm:= ",SCelm,";");
#   PrintTo(ICcoefffile,"ICcoeff:= ", ICcoeff,";");
    PrintTo(SCcoefffile,"SCcoeff:= ",SCcoeff,";");
    k:=k+quo;
  od;
  block := bl;
end;
WordFlip := function(w,k) local p,m,perm,n,new,l;
m:=1;
p:=w[k];
l:=Length(w);
while p-m = w[k+m]  do
m:=m+1;
if k+m=l+1 then return w; fi;
od;
new:=w;
if w[k+m] <p then
   perm:=CycleFromList([k..k+m]);
   new:=Permuted(w,perm);
elif w[k+m] =p and p<redindex then
     n:=1;
      if k+m+n<l+1 then
      	 while p-n = w[k+m+n] do    
     	   n:=n+1;
	   if k+m+n=l+1 then break; fi;
     	 od;
     fi;
     if n>m then perm:=CycleFromList([k+m..k+m+m]);
         new:=Permuted(w,perm);
     fi;
fi;
return new;
end;
ToCanonical := function(w) local p,m,perm,n,new;
m:=1;
n:=Length(w);
while m<n do
  new:=WordFlip(w,m);
  if new=w then m:=m+1;
  else
  #Print(w," -> ",new,"\n");
  m:=1; w:=new;
  fi;
od;
return w;
end;
PrintIC := function(ICs) local p,m,perm,n,new;
n:=Length(ICs);
for m in [1..n] do
Print(ICs[m],"\n");
od;
end;

BoringWords := function(w) local i;
   for i in [1..Length(w)-1] do 
       if w[i]-w[i+1] >1 then return false; fi;
   od;
   return true;
end;
TestIC := function(subIC,w,min) local k;
for k in subIC do if Sum(CoefficientsOfLaurentPolynomial(GetCoefficient(k,w))[1])>min-1  then return true; fi; od;
return false;
end;
ICMax := function(totalIC,max) local k,coeffs;
 coeffs:=List(totalIC!.coeff,x -> Sum(CoefficientsOfLaurentPolynomial(x)[1]));
 if Maximum(coeffs) < max then return false; else return true; fi;
end;
MakeTable := function(bl) local all,ans,i,j,k, a,shuflist,canonical;
SetCartan("a",Length(bl));
 ComputeRed(bl);
 shuflist:=[];
 a:=0;
 for i in [1..Length(bl)] do k:=bl[i]; Add(shuflist,List([1..k], x -> i)); od;
 all:=Filtered(ShuffleList(shuflist),x->true);
 Sort(all);
 all:=Reversed(all);
 canonical:=List(all,ToCanonical);
 Print("FGR");
 for k in [1..Length(goodwords)] do Print("&",goodwords[k]); od;
 Print("\\\\\\hline\n");
 for i in [1..Length(all)] do
     for j in all[i] do Print(j); od;
    for k in [1..Length(goodwords)] do a:=Sum(CoefficientsOfLaurentPolynomial(GetCoefficient(IC[k],all[i]))[1]);
    if canonical[i]=goodwords[k] then Print("&\\boxed\{",a,"\}");elif not a=0 then Print("&",a); else Print("&"); fi; od;
    Print("\\\\\\hline\n");
 od;
return;
end;
MakeTableP := function(bl,first, last, min) local all,allp,ans,i,j,k, a,shuflist,totalIC,subIC,canonical;
 if not redindex=Length(bl) then SetCartan("a",Length(bl)); fi;
 ComputeRedP(bl,first,last);
 shuflist:=[];
 a:=0;
 subIC := [];
  for k in [first..last] do Add(subIC,IC[k]); od;
  subIC := Filtered(subIC,x -> ICMax(x, min));
  totalIC:=Sum(subIC);
 # Print(totalIC);
# if not bl=block then
 for i in [1..Length(bl)] do k:=bl[i]; Add(shuflist,List([1..k], x -> i)); od;
 allp:=Filtered(ShuffleList(shuflist),BoringWords);
# fi;
 all:=Filtered(allp, x -> TestIC(subIC,x,min));
 Sort(all);
 all:=Reversed(all);
 canonical:=List(all,ToCanonical);
 Print("FGR");
 for k in  [first..last] do Print("&",goodwords[k]); od;
 Print("\\hline\n");
 for i in [1..Length(all)] do
     for j in all[i] do Print(j); od;
    for k in  [first..last] do a:=Sum(CoefficientsOfLaurentPolynomial(GetCoefficient(IC[k],all[i]))[1]);
    if canonical[i]=goodwords[k] then Print("&\\boxed\{",a,"\}");elif not a=0 then Print("&",a); else Print("&"); fi; od;
    Print("\\\\\\hline\n");
 od;
return;
end;


