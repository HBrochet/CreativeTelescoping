# Copyright (c) 2018, Alin Bostan, Frédéric Chyzak, Pierre Lairez, Bruno Salvy

read "Mgfun_missing.mpl":
read "red.mpl";

really_lose_info_I_mean_it := proc(mm, $)
  local tv, tvars := mm:-typed_vars;
  local tt := table([seq(tv = mm:-matrices[tv], tv = tvars)]);
  tvars, subs(mm:-subs_set, eval(tt))
end:

_ORDMAX:=20:

### Input:
###   . int   an integral in the form Int(expr,var=range) or Int(expr,var)
###   . alg   list of the form [var1::type1,var2::type2,...]
###       where var1,..d are names and type1,... are in {diff,shift} or others that
###       Mgfun recognizes
### Output:
###   . a basis of an ideal canceling the integrand modulo derivatives
###
### In this version, the shift,diff,... variables are denoted D[var].
redctint:=proc(int,alg,{cert:=0,minimal::boolean:=true})
local x,var,vars,matrices,basis,comp,dim,i,Dx,diffop,vv,cv,action,X,ini,newop;
local mm,prefact,singsandshift,shiftinfinity,ratfun,shellremoved,polpart:=1,F,co;
  x:=op(2,int);
  if type(x,`=`) then x:=op(1,x) fi;
  ### translate integral into a GB in matrix form
  F:=op(1,int);
  if op(0,F)='LFSol' then
    mm := LFSol_to_matrices(F, {x :: diff, op(alg)})
  else
    if type(F,`*`) then polpart,F:=selectremove(type,F,polynom) fi;
    mm := dfinite_expr_to_matrices(F, {x :: diff, op(alg)})
  fi;
  vars, matrices := really_lose_info_I_mean_it(mm);
  dim:=op([1,1],matrices[vars[1]]);
  userinfo(1,'redct',"dimension",dim);
  ### Cyclic vector method
  basis,comp:=cyclic_vec(matrices[x::diff],x);
  cv:=convert(basis[1..dim,1..1],Vector);
  Dx:=D[x];
  diffop:=adjoint(numer(normal(Dx^dim-add(comp[i]*Dx^(i-1),i=1..dim))),Dx,x);
  diffop:=primpart(diffop,Dx,'prefact');
  if dim=1 then
    diffop,co,singsandshift:=removeshell(diffop,'Dvar'=Dx,'tvar'=x,_options);
    prefact:=prefact*co;
    shellremoved:=true;
    diffop:=primpart(diffop,Dx,'co');
    prefact:=normal(prefact*co)
  else
    shellremoved:=false
  fi;
  if prefact<>1 then userinfo(2,'redct',"content found",prefact) fi;
  if shellremoved then
    shiftinfinity:=max(seq(degree(coeff(diffop,Dx,i),x)-i,i=0..dim));
    userinfo(1,'redct',"bound on the confinement dim for the homogeneous part",add(i[2],i=singsandshift)+shiftinfinity)
  fi;
  userinfo(3,'redct',"operator:",sprintf("%.300a",diffop));
  ### compute the actions on multiples of the cyclic vector
  for vv in vars do
    var:=op(1,vv);
    if var=x then
      if dim=1 then X:=comp else X:=[0,1,0$(dim-2)] fi
    elif op(2,vv)='diff' then
      X:=LinearAlgebra['LinearSolve'](basis,map(diff,cv,var)+matrices[vv].cv)
    elif op(2,vv)='shift' then
      X:=LinearAlgebra['LinearSolve'](basis,matrices[vv].subs(var=var+1,cv));
    else error "two lines missing in the code"
    fi;
    newop:=adjoint(add(X[i]*Dx^(i-1),i=1..dim),Dx,x);
    newop:=add(coeff(newop,Dx,i)*diff(y(x),[x$i]),i=0..dim-1);
    if op(2,vv)='shift' then
      action[op(1,vv)]:=subs(_v=op(1,vv),_newop=subs(y(x)=_r2,newop),_arg=ratfun,
        proc(_arg) local _r2:=subs(_v=_v+1,_arg);_newop end)
    else
      action[op(1,vv)]:=subs(_v=op(1,vv),_newop=subs(y(x)=_arg,newop),_arg=ratfun,
        proc(_arg) diff(_arg,_v)+_newop end)
    fi;
  od;
  ### value of 1 on the cyclic vector
  ini:=LinearAlgebra['LinearSolve'](basis,Vector([1,0$(dim-1)]));
  ini:=polpart*add((-1)^i*diff(ini[i+1],[x$i]),i=0..dim-1);
  ###
  scalar_red_ct(diffop,ini,prefact,subs(x::diff=NULL,vars),eval(action),'Dvar'=Dx,'tvar'=x,_options,'liouvilleform'=(shellremoved or not minimal))
end:


scalar_red_ct:=proc(diffop,ini,prefact,vars,action,
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      cert := 0,
      shellremoved := NULL
    })
local denovergg,denquoovergg,rnd,rndpoint,x,HH,quotient,nextmons,mon,
i,basis,lmons,red,var,dvars,diffvars,dvar,prevmons,X,prev,typevar,
den,num,co,denquo,elementquotient,gg,newelt,newrel,sol,sys,pol,goodfact,
varsres,mat,inds;
  x:=tvar;
  dvars:=[seq(D[op(1,i)],i=vars)];
  varsres:=map2(op,1,vars);
  for i in vars do typevar[op(1,i)]:=op(2,i) od;
  diffvars:={op(select(has,dvars,map2(op,1,select(has,vars,diff))))};
  quotient:=[];
  nextmons:=[1];
  basis:=[];
  lmons:={};
  HH:=ini; # initial rational function
  elementquotient:=0;
  denquo:=1;
  pol[1]:=1;
  inds:=indets(diffop,name) minus {x,D[x]} union {op(varsres)};
  rnd:=rand(-1000..1000);
  rndpoint:=[seq(op(1,i)=rnd(),i=inds)];
  # finds generators of a D-finite ideal, or a quotient of dimension > _ORDMAX
  while nextmons<>[] and nops(lmons)<_ORDMAX do
    mon:=nextmons[1];
    nextmons:=subsop(1=NULL,nextmons);
    if member(true,map2(divide,mon,lmons)) then next fi;
    userinfo(2,'redct',"dealing with monomial",mon,"at time:",time());
    ######### Compute rational function to be reduced ########
    prevmons:=select(has,indets(mon,indexed),dvars);
    if prevmons<>{} then # the other case is when HH=ini
      # give an advantage to differentiation
      if has(prevmons,diffvars) then prevmons:=prevmons intersect diffvars fi;
      dvar:=prevmons[min[index](map(length,[seq(red[mon/i],i=prevmons)]))];
         # +map(length,[seq(action[op(i)::typevar[op(i)]],i=prevmons)]))];
      prev:=red[mon/dvar];
      var:=op(dvar);
      HH:=action[var](prev);
      HH:=normal(HH);
      if typevar[var]='diff' then
        pol[mon]:=collect(diff(pol[mon/dvar],var)+pol[mon/dvar]*dvar,dvars,expand)
      else # shift
        pol[mon]:=collect(subs(subs(var=var+1,dvar)=dvar,
            subs(var=var+1,pol[mon/dvar]*dvar)),dvars,expand)
      fi
    fi;
    red[mon]:=normal(prefact*reduction(HH/prefact,diffop,_options,_rest));
    userinfo(2,'redct',"reduction done at time:",time());
    userinfo(4,'redct',"reduces to",red[mon]);
    ########### Find linear relation ############
    den:=primpart(denom(red[mon]),x,'goodfact');
    num:=primpart(numer(red[mon]),x,'co');
    if co=0 then co:=1 fi;
    pol[mon]:=goodfact*pol[mon]/co;
    red[mon]:=num/den;
    gg:=gcd(denquo,den);
    divide(den,gg,'denovergg');
    divide(denquo,gg,'denquoovergg');
    denquo:=denquo*denovergg;
    elementquotient:=expand(denovergg*elementquotient);
    newelt:=expand(denquoovergg*numer(red[mon]));
    sys:={coeffs(elementquotient-newelt,x)} minus {0};
    if remove(has,sys,X)<>{} then sol:=NULL
    else
      mat:=LinearAlgebra['GenerateMatrix'](sys, [seq(X[i],i=quotient)], 'augmented' = true);
      if op([1,1],mat)>=op([1,2],mat) then
      # probabilistic test of consistency first
        try
          sol:=LinearAlgebra['LinearSolve'](eval(mat,rndpoint),'method'='modular')
        catch "system is inconsistent": sol:=NULL
        end try
      fi;
      if op([1,1],mat)<op([1,2],mat) or sol<>NULL then
        userinfo(2,'redct',"dimension of the matrix:",nops(quotient));
        userinfo(2,'redct',"col. degrees of the matrix entries:",seq(max(map(degree,convert(mat[1..-1,i],list),varsres)),i=1..nops(quotient)));
        try
          sol:=LinearAlgebra['LinearSolve'](mat,'method'='solve');
        catch: sol:=NULL
        end try;
      fi
    fi;
    if sol<> NULL then
      userinfo(2,'redct',"relation found");
      userinfo(2,'redct',"degree of the solution:",max(
        map(degree,map(numer,convert(sol,list)),varsres)));
      newrel:=(primpart(collect(pol[mon]-add(sol[i]*pol[quotient[i]],i=1..nops(quotient)),dvars),dvars));
      userinfo(3,'redct',"relation:",sprintf("%.300a",newrel));
      basis:=[op(basis),newrel];
      lmons:=lmons union {mon}
    else
      quotient:=[op(quotient),mon];
      elementquotient:=elementquotient+expand(X[mon]*newelt);
      for var in vars do
        if not member(mon*D[op(1,var)],nextmons) and
          not member(true,map2(divide,mon*D[op(1,var)],lmons)) then
          nextmons:=[op(nextmons),mon*D[op(1,var)]];
        fi
      od
    fi;
  od;
  userinfo(1,'redct',"dim quotient:",nops(quotient));
  userinfo(1,'redct',"degree coeffs:",max(op(map(degree,basis,varsres))));
  basis
end:

removeshell:=proc(dop,{ Dvar :: name := NULL, tvar :: name := NULL})
local order,sings,sing,Q,shift,zz,N,g,zero,newdop,i,den,prefact;
  order:=degree(dop,Dvar);
  sings:=select(has,map2(op,1,factors(coeff(dop,Dvar,order))[2]),tvar);
  for sing in sings do
        zz, Q, shift[sing] := indicialeq1(dop, sing, indvar_, _options);
        zero[sing]:=max(0,op(zz));
  od;
  N:=mul(sing^zero[sing],sing=sings);
  if N=1 then newdop:=dop;prefact:=1
  else
    userinfo(2,'redct',"rational factor found",1/N);
    g:=exp(tvar*Dvar-add(zero[sing]*ln(sing),sing=sings));
    newdop:=normal(eval(add(coeff(dop,Dvar,i)*diff(g,[tvar$i]),i=0..order),exp=1));
    den:=denom(newdop);
    prefact:=1/den/N;
    userinfo(2,'redct',"prefactor",prefact)
  fi;
  if newdop<>dop then userinfo(2,'redct',"length new:",length(newdop),"length orig:",length(dop)) fi;
  newdop,prefact,[seq([sing,shift[sing]],sing=sings)]
end:

### computes the adjoint operator
adjoint:=proc(dop,Dx,x)
local res, i, r, A, y ;
  r:=degree(dop,Dx);
    res:=0;
    for i from r by -1 to 0 do res:=collect(coeff(dop,Dx,i)*exp(A*x)-diff(res,x),A,normal) od;
    res:=subs(exp(A*x)=1,res);
    subs(A=Dx,res)
end:

### Input:
###   . A   matrix s.t. the derivative of V.Y is (V'+AV).Y
###   . var wrt which derivative is performed
###   . ini (optional) coordinates of the cyclic vector
###   . nbtests (internal), initially 0, counts the number of
###       vectors whose cyclicity has failed
### Output:
###   . P   matrix whose columns are the coordinates of the successive
###       derivatives of the first column (the cyclic vector) in the old basis
###   . C   vector containing the coefficients of the corresponding companion matrix
###
### V'+AV=G is equivalent to Z'+CZ=H with Z=PG, H=PG.
###
cyclic_vec:=proc(A,var)
local dim,V,cycl,i,j,comp,Basis,U,W,rk,rk2;
  dim:=op([1,1],A);
  V:=Vector[column]([1,0$(dim-1)]);
  U,rk,cycl:=try_cyclic_vec(A,var,V);
  do
    if rk=dim then break fi;
    # change init vector, following Churchill-Kovacic 2002.
    for j from 2 to dim do
      U[rk+1,j-1]:=0; U[rk+1,j]:=1;
      if LinearAlgebra['LUDecomposition'](U,'output'='rank')=rk+1 then break fi;
    od;
    if j=dim+1 then error "singular matrix",A fi;
    W:=copy(V);
    for i from 0 to rk do
      W[j]:=V[j]+var^i; # Using 1 as a constant there is not optimal
      U,rk2,cycl:=try_cyclic_vec(A,var,W);
      if rk2>rk then V:=W; rk:=rk2; break fi;
    od
  od;
  if {seq(V[i],i=2..dim)} minus {0}<>{} then
    userinfo(2,'redct',"using cyclic vector:",convert(V,list));
  fi;
  Basis:=Matrix([seq(cycl[i],i=1..dim)]);
  cycl[dim+1]:=map(normal,map(diff,cycl[dim],var)+A.cycl[dim]);
  comp:=LinearAlgebra['LinearSolve'](Basis,cycl[dim+1]);
  Basis,comp
end:

try_cyclic_vec:=proc(A,var,ini)
local dim,cycl,i,UU,rk;
  dim:=op([1,1],A);
  cycl[1]:=ini;
  UU:=Matrix(LinearAlgebra['Transpose'](cycl[1]));
  for i to dim-1 do
    cycl[i+1]:=map(normal,map(diff,cycl[i],var)+A.cycl[i]);
    UU:=<UU,LinearAlgebra['Transpose'](cycl[i+1])>;
    UU,rk:=LinearAlgebra['LUDecomposition'](UU,'output'=['U','rank']);
    if rk<>i+1 then return UU,rk,cycl fi
  od;
  return UU,dim,cycl
end:
