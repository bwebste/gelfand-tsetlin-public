DeclareCategory("IsMvpObj", IsScalar);
DeclareCategoryCollections("IsMvpObj");
DeclareRepresentation("IsMvpRep", IsComponentObjectRep, ["coeff", "term", "normalize"]);
DeclareGlobalFunction("Mvp");


MvpStringToNumber := function(s) local n,i,ten,j;
  n := 0;
  ten := 1;
  for i in Reversed([1..Length(s)]) do
    for j in [0..9] do
      if s[i] = String(j)[1] then n := n + j*ten;fi;
    od;
    if s[i] = '-' then n := -n;fi;
    ten := ten*10;
  od;
  return(n);
end;

MvpUnpack := function(string) local i,j;
  return List(SplitString(string, ".,;|", "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz()[] "), MvpStringToNumber);
end;

############################################################

MvpSet := function(e,c,s) local R,F,i,j,k,b,ee,eee,cc,new,uppers,lowers;
  eee := [];
  for i in [1..Length(e)] do
    uppers := []; lowers := [];
    for j in [1..Length(e[i])] do
      if e[i][j][1][1] < 'a' or e[i][j][1][1] >'z' then
        Add(uppers, ShallowCopy(e[i][j]));
      else
        Add(lowers, ShallowCopy(e[i][j]));
      fi;
    od;
    Sort(lowers); new := [];
    for k in [1..Length(lowers)] do
      if k=1 or lowers[k][1]<>lowers[k-1][1] then Add(new,lowers[k]);
      else new[Length(new)][2]:=new[Length(new)][2]+lowers[k][2];
      fi;
    od;
    for k in [1..Length(uppers)] do
      if k=1 or uppers[k][1]<>uppers[k-1][1] then Add(new,uppers[k]);
      else new[Length(new)][2]:=new[Length(new)][2]+uppers[k][2];
      fi;
    od;
    new:=Filtered(new,x->x[2] <> 0*x[2]);
    Add(eee, new);
  od;
  SortParallel(eee,c);
  ee := []; cc := [];
  for i in [1..Length(eee)] do
    if i=1 or eee[i]<>eee[i-1] then
      Add(ee,eee[i]);Add(cc,c[i]);
    else cc[Length(cc)]:=cc[Length(cc)]+c[i];
    fi;
  od;
  b:=List(cc,x->x <> 0*x);
  R := rec(elm:=Immutable(ListBlist(ee,b)),coeff:=Immutable(ListBlist(cc,b)),normalize:=s);
  F := NewFamily("IsMvpObj", IsMvpObj);
  return Objectify(NewType(F, IsMvpObj and IsMvpRep), R);
end;

MvpNormalize := function() end;

MvpNormalizeSub := function(thise,thiscf,normalizefunc) local i,j,lowers,uppers,flip;
  if normalizefunc <> fail then 
    lowers := []; uppers := [];
    for i in [1..Length(thise)] do 
      if thise[i][1][1] < 'a' or thise[i][1][1] > 'z' then
        Add(uppers, thise[i]);
      else
        Add(lowers,thise[i]);
      fi;
    od;
    flip := normalizefunc(uppers);
    if flip <> fail then
      return MvpNormalize(MvpSet([lowers], [thiscf], normalizefunc) * flip);
    fi;
  fi;
  return MvpSet([thise],[thiscf], normalizefunc);
end;

MvpNormalize := function(x) local normalized,i;
  if IsCyc(x) or IsRationalFunction(x) then return(x);fi;
  normalized := Zero(x);
  for i in [1..Length(x!.elm)] do
    if x!.coeff[i] <> 0*x!.coeff[i] then
      normalized := normalized + MvpNormalizeSub(x!.elm[i],x!.coeff[i],x!.normalize);
    fi;
  od;
  return(normalized);
end;

################################################################
# Useful routines
# The first truncates all powers of var in pol > deg

MvpTruncateAbove := function(poly,deg,var) local e,c,i,j,valid,t;
  if IsCyc(poly) or IsRationalFunction(poly) then
    if deg < 0 then return Zero(poly);fi;
    return poly;
  fi;

  c := []; e := [];
  for i in [1..Length(poly!.coeff)] do
    valid := true;
    if poly!.elm[i] = [] then
       if deg < 0 then valid := false;fi;
    else
      for t in poly!.elm[i] do
        if t[1] = var and t[2] > deg then valid := false; fi;
      od;
    fi;
    if valid then
      Add(c, poly!.coeff[i]);
      Add(e, ShallowCopy(poly!.elm[i]));
    fi;
  od;
  return MvpSet(e,c,poly!.normalize);
end;

MvpTruncateBelow := function(poly,deg,var) local e,c,i,j,valid,t;
  if IsCyc(poly) or IsRationalFunction(poly) then
    if deg > 0 then return Zero(poly);fi;
    return poly;
  fi;
  c := []; e := [];
  for i in [1..Length(poly!.coeff)] do
    valid := true;
    if poly!.elm[i] = [] then
       if deg > 0 then valid := false;fi;
    else
      for t in poly!.elm[i] do
        if t[1] = var and t[2] < deg then valid := false; fi;
      od;
    fi;
    if valid then
      Add(c, poly!.coeff[i]);
      Add(e, ShallowCopy(poly!.elm[i]));
    fi;
  od;
  return MvpSet(e,c,poly!.normalize);
end;

# Return the deg coefficient of a polynomial
# which is of course usually another mvp.
# However if it is truly an integer it returns it as such!

MvpCoefficient := function(poly,var,deg) local i,j,thisdeg,c,e,t,newe;
  if IsCyc(poly) or IsRationalFunction(poly) then
    if deg = 0 then return poly;fi;
    return 0;
  fi;
  c := []; e := [];
  for i in [1..Length(poly!.coeff)] do
    thisdeg := 0;
    for t in poly!.elm[i] do
      if t[1] = var then thisdeg := t[2]; fi;
    od;
    if thisdeg = deg then
      newe := [];
      for t in poly!.elm[i] do
        if t[1] <> var then Add(newe, ShallowCopy(t)); fi;
      od;
      Add(e, newe);
      Add(c, poly!.coeff[i]);
    fi;
  od;
  if e = [[]] then return c[1];fi;
  return MvpSet(e,c,poly!.normalize);
end;

# Change all degrees to their negatives

MvpBar := function(poly, var) local c,e,i,j,this;
  if IsCyc(poly) or IsRationalFunction(poly) then return(poly);fi;

  c := ShallowCopy(poly!.coeff); 
  e := [];
  for i in [1..Length(poly!.elm)] do
    this := [];
    for j in [1..Length(poly!.elm[i])] do
      if poly!.elm[i][j][1] = var then
        Add(this, [poly!.elm[i][j][1], -poly!.elm[i][j][2]]);
      else
        Add(this, [poly!.elm[i][j][1], poly!.elm[i][j][2]]);
      fi;
    od;
    Add(e,this);
  od;
  return MvpSet(e,c,poly!.normalize);
end;  

# Returns a list [bot,top] giving the bottom and top degrees of
# variable var in poly. If it involves no var's at all, returns false.

MvpRange := function(poly,var) local bot,top,i,j,thisdeg;
  if IsCyc(poly) or IsRationalFunction(poly) then
    return false;
  fi;

  bot := false;
  top := false;
  for i in [1..Length(poly!.elm)] do
    thisdeg := false;
    for j in [1..Length(poly!.elm[i])] do
      if poly!.elm[i][j][1] = var then 
        if thisdeg = false then thisdeg := 0;fi;
        thisdeg := thisdeg + poly!.elm[i][j][2];
      fi;
    od;
    if thisdeg <> false then
      if bot = false or thisdeg < bot then bot := thisdeg;fi;
      if top = false or thisdeg > top then top := thisdeg;fi;
    fi;
  od;
  if bot = false then return false;fi;
  return [bot,top];
end;

############################################################
# Here are the methods

InstallGlobalFunction(Mvp, 
  "mvp",
  function(arg) local newelm;
    if not IsString(arg[1]) or arg[1] = [] then
      newelm := [arg[1]];
    else
      newelm := [[[arg[1],1]]];
    fi;
    if Length(arg) = 1 then 
      return MvpSet(newelm,[1],fail);
    fi;
    if Length(arg) = 2 then
      if IsFunction(arg[2]) then
        return MvpSet(newelm,[1],arg[2]);
      fi;
        return MvpSet(newelm, [arg[2]],fail);
    fi;
    if Length(arg) = 3 then
      return MvpSet(newelm, [arg[2]], arg[3]);
    fi;
  end
);

InstallMethod(PrintObj,
  "mvp",
  [IsMvpObj and IsMvpRep], 
  function(h) local i,j,coeff,elm,s,res;
    res:="";
    if h!.elm=[] then Append(res,"0");fi;
    for i in [1..Length(h!.elm)] do
      elm:="";
      for s in h!.elm[i] do Append(elm,s[1]);
        if s[2]<>1 then Append(elm,"^");Append(elm,String(s[2]));fi;
      od;
      coeff:=String(h!.coeff[i]);
      if elm<>"" then
        if coeff="1" then coeff:="";
	elif coeff="-1" then coeff:="-";
	fi;
      fi;
      if '-' in coeff{[2..Length(coeff)]} 
          or '+' in coeff{[2..Length(coeff)]} then
        coeff:=Concatenation("(",coeff,")");
      fi;
      if Position(coeff,'-')<>1 and i<>1 then Append(res,"+");fi;
      Append(res,coeff);
      Append(res,elm);
    od;
    Print(String(res));
  end 
);

InstallMethod(\=,
  "mvp=mvp",
  [IsMvpObj and IsMvpRep, IsMvpObj and IsMvpRep],
  function( x, y ) local diff;
    diff := MvpNormalize(x-y);
    return(diff!.elm = []);
  end
);

InstallMethod(\=,
  "mvp=cyc",
  [IsMvpObj and IsMvpRep, IsCyc],
  function( x, y ) local diff;
    diff := MvpNormalize(x-y);
    return(diff!.elm = []);
  end
);

InstallMethod(\=,
  "mvp=cyc",
  [IsMvpObj and IsMvpRep, IsRationalFunction],
  function( x, y ) local diff;
    diff := MvpNormalize(x-y);
    return(diff!.elm = []);
  end
);

InstallMethod(\=,
  "cyc=mvp",
  [IsCyc,IsMvpObj and IsMvpRep],
  function( x, y ) 
    return y=x;
  end
);

InstallMethod(\=,
  "cyc=mvp",
  [IsRationalFunction,IsMvpObj and IsMvpRep],
  function( x, y ) 
    return y=x;
  end
);

InstallMethod(\+,
  "mvp+mvp",
  [IsMvpObj and IsMvpRep, IsMvpObj and IsMvpRep],
  function( x, y )
    return MvpSet(Concatenation(x!.elm,y!.elm),Concatenation(x!.coeff,y!.coeff),x!.normalize);
  end
);

InstallMethod(\+,
  "mvp+cyc",
  [IsMvpObj and IsMvpRep, IsCyc],
  function( x, y )
    return MvpSet(Concatenation(x!.elm,[[]]),Concatenation(x!.coeff,[y]),x!.normalize);
  end
);
InstallMethod(\+,
  "mvp+cyc",
  [IsMvpObj and IsMvpRep, IsRationalFunction],
  function( x, y )
    return MvpSet(Concatenation(x!.elm,[[]]),Concatenation(x!.coeff,[y]),x!.normalize);
  end
);

InstallMethod(\+,
  "cyc+mvp",
  [IsCyc, IsMvpObj and IsMvpRep],
  function( x, y )
    return y+x;
  end
);
InstallMethod(\+,
  "cyc+mvp",
  [IsRationalFunction, IsMvpObj and IsMvpRep],
  function( x, y )
    return y+x;
  end
);

InstallMethod(ZeroOp,
  "mvp",
  [IsMvpObj],
  x -> MvpSet([[]],[0],x!.normalize));

InstallMethod(AdditiveInverseOp,
  "mvp",
  [IsMvpObj and IsMvpRep],
  x -> MvpSet(ShallowCopy(x!.elm),-ShallowCopy(x!.coeff),x!.normalize));

InstallMethod(\*,
  "mvp*mvp",
  [IsMvpObj and IsMvpRep, IsMvpObj and IsMvpRep],
  function( x, y ) local relm,rcoeff,i,j;
    relm:=[];rcoeff:=[];
    for i in [1..Length(x!.elm)] do
      for j in [1..Length(y!.elm)] do
	Add(relm,Concatenation(x!.elm[i],y!.elm[j]));
        Add(rcoeff,x!.coeff[i]*y!.coeff[j]);
      od;
    od;
    return MvpSet(relm,rcoeff,x!.normalize);
  end
);

InstallMethod(\*,
  "mvp*cyc",
  [IsMvpObj and IsMvpRep, IsCyc],
  function( x, y ) local relm,rcoeff,i;
    relm:=[];rcoeff:=[];
    for i in [1..Length(x!.elm)] do
      Add(relm,x!.elm[i]);
      Add(rcoeff,x!.coeff[i]*y);
    od;
    return MvpSet(relm,rcoeff,x!.normalize);
  end
);
InstallMethod(\*,
  "mvp*cyc",
  [IsMvpObj and IsMvpRep, IsRationalFunction],
  function( x, y ) local relm,rcoeff,i;
    relm:=[];rcoeff:=[];
    for i in [1..Length(x!.elm)] do
      Add(relm,x!.elm[i]);
      Add(rcoeff,x!.coeff[i]*y);
    od;
    return MvpSet(relm,rcoeff,x!.normalize);
  end
);

InstallMethod(\*,
  "cyc*mvp",
  [IsCyc,IsMvpObj and IsMvpRep],
  function( x, y ) 
    return y*x;
  end
);
InstallMethod(\*,
  "cyc*mvp",
  [IsRationalFunction,IsMvpObj and IsMvpRep],
  function( x, y ) 
    return y*x;
  end
);



InstallMethod(OneOp,
  "mvp",
  [IsMvpObj],
  x -> MvpSet([[]],[1],x!.normalize));

InstallMethod(InverseOp,
  "mvp",
  [IsMvpObj and IsMvpRep],
  function(x) local h,newelm;
    if Length(x!.elm) <> 1 or x!.coeff[1] = 0 then return fail; fi;
    newelm := [];
    for h in [1..Length(x!.elm[1])] do
      Add(newelm, ShallowCopy(x!.elm[1][h]));
      newelm[Length(newelm)][2] := -newelm[Length(newelm)][2];
    od;
    return MvpSet([Reversed(newelm)], [x!.coeff[1]^-1],x!.normalize);
  end
);


#####################################
# This is an equation solver.
# Unknowns are [x1, x2 ..., xn]
# pass a list of vectors
# each of the form x1 v1 + x2 v2 +.. + c
# it solves them simultaneously, returning
# fail if no solution, else a list consisting
# of particular solution for x'1 then a basis
# for general solution space.

# Given a bunch of MVP it splits
# it into two lists, the first
# being the monomials the second the coefficients

MvpConstantTerm := function(v,vars) local ans,i;
  ans := v;
  for i in [1..Length(vars)] do
    ans := MvpCoefficient(ans,vars[i],0);
  od;
  return ans;
end;

# Convert a vector to a list with respect to basis,
# which must be a single mvp monomial

MvpVectorToList := function(v,basis) local list,i,j,this;
  list := [];
  for i in [1..Length(basis)] do
    this := 0;
    if not IsMvpObj(v) then	# Deal with v a constant
      if basis[i] = [] then
        this := this + v;
      fi;
    else
      for j in [1..Length(v!.elm)] do
        if v!.elm[j] = basis[i] then
          this := this + v!.coeff[j];
        fi;
      od;
    fi;
    Add(list,this);
  od;
  return list;
end;

# arg[1] = eqns
# arg[2] = number of variables if no substitution
#       or variables if substitution required
# Given a list of linear equations with Length(variables) unknowns
# gotten from MvpUnknown, this finds all 
# solutions \sum a_i x_i then returns \sum a_i variable[i] if substitution
# The first thing in the solution is particular solution,
# rest is general solution; fail if no solution.

MvpUnknown := function(arg) local s,i;
  i := arg[1];
  if Length(arg) = 2 then s := ShallowCopy(arg[2]);
  else s := "x";
  fi;
  Append(s,"(");
  Append(s, String(i));
  Append(s,")");
  return s;
end;

MvpSolve := function(arg) local eqns,n,cfs,mat,vec,i,j,thiscf,newmat,newvec,ans,final,worsttype;

  eqns := arg[1];
  if IsList(arg[2]) then n:=Length(arg[2]);
  else n := arg[2];
  fi;

# Stupid cases.
# If no variables then all the equations must be zero to be a solution,
# then the solution is 0

  if n = 0 then
    for i in [1..Length(eqns)] do
      if eqns[i] <> 0 then return fail;fi;
    od;
    if IsList(arg[2]) then return([0]);fi;
    return([[]]);
  fi;

# If no equations then all things are solutions

  if eqns = [] then
    ans:=[];
    thiscf:=[];
    for i in [1..n] do Add(thiscf,0);od;
    Add(ans,ShallowCopy(thiscf));
    for i in [1..n] do
      thiscf[i] := 1;
      Add(ans,ShallowCopy(thiscf));
      thiscf[i] := 0;
    od;
    if IsList(arg[2]) then	# Substitute solution back
      final := [];
      for i in [1..Length(ans)] do
        thiscf := 0;
        for j in [1..n] do
          thiscf := thiscf + arg[2][j]*ans[i][j];
        od;
        Add(final,thiscf);
      od;
      return final;
    fi;
    return ans;
  fi;

# First we scan the equations to pull out
# a list of all x_i coefficients and a list of constant terms
# as vectors

  cfs := [];
  mat := [];
  for j in [1..n] do
    thiscf := [];
    for i in [1..Length(eqns)] do
      Add(thiscf,MvpCoefficient(eqns[i],MvpUnknown(j),1));
      if IsMvpObj(thiscf[Length(thiscf)]) then
        cfs := Union(cfs, thiscf[Length(thiscf)]!.elm);
      else
        cfs := Union(cfs, [[]]);
      fi;
    od;
    Add(mat, thiscf);
  od;
  vec := [];
  for i in [1..Length(eqns)] do
    Add(vec,MvpConstantTerm(-eqns[i],List([1..n],MvpUnknown)));
    if IsMvpObj(vec[Length(vec)]) then
      cfs := Union(cfs, vec[Length(vec)]!.elm);
    else
      cfs := Union(cfs, [[]]);
    fi;
  od;    

# Now we replace each entry of mat or vec
# with the sequence of coefficients...

  newmat := [];
  newvec := [];
  for i in [1..Length(eqns)] do
    Append(newvec, MvpVectorToList(vec[i],cfs));
  od;
  for j in [1..n] do
    thiscf := [];
    for i in [1..Length(eqns)] do
      Append(thiscf, MvpVectorToList(mat[j][i],cfs));
    od;
    Add(newmat,thiscf);
  od;

# Now solve

  ans := [];
  if newvec = [] then 
    Add(ans,[]);
    for i in [1..Length(newmat)] do
      Add(ans[1],0);
    od;
    for i in [1..Length(newmat)] do
      Add(ans,[]);
      for j in [1..Length(newmat)] do
        Add(ans[i+1],0);
      od;
      ans[i+1][i] := 1;
    od;
  else

# This is a cludge because gap is crap at types.

    worsttype := 1;
    for i in [1..Length(newvec)] do
      if IsRationalFunction(newvec[i]) and not IsRationalFunction(worsttype) then
        worsttype := newvec[i]^0;
      fi;
    od;
    for i in [1..Length(newvec)] do
      newvec[i] := newvec[i]*worsttype;
      for j in [1..Length(newmat)] do
        newmat[j][i] := newmat[j][i]*worsttype;
      od;
    od;

    Add(ans,SolutionMat(newmat,newvec));
    if ans[1] = fail then return fail;fi;
    Append(ans,NullspaceMatDestructive(newmat));
  fi;
  if IsList(arg[2]) then	# Substitute solution back
    final := [];
    for i in [1..Length(ans)] do
      thiscf := 0;
      for j in [1..n] do
        thiscf := thiscf + arg[2][j]*ans[i][j];
      od;
      Add(final,thiscf);
    od;
    return final;
  fi;
  return ans;
end;

# Substitute a monomial for something else

MvpSubstitute := function(vec,from,to) local ans,i,j,newmy;
  if not IsMvpObj(vec) then return vec;fi;
  ans := 0;
  for i in [1..Length(vec!.elm)] do
    newmy := 1;
    for j in [1..Length(vec!.elm[i])] do
      if vec!.elm[i][j][1] = from then
        newmy := newmy * (to^(vec!.elm[i][j][2]));
      else
        if vec!.normalize = fail then
          newmy := newmy * Mvp([vec!.elm[i][j]]);
        else
          newmy := newmy * Mvp([vec!.elm[i][j]],vec!.normalize);
        fi;
      fi;
    od;
    ans := ans + vec!.coeff[i]*newmy;
  od;
  return ans;
end;

