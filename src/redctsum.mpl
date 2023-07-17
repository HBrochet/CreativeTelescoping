
really_lose_info_I_mean_it := proc(mm, $)
  local tv, tvars := mm:-typed_vars;
  local tt := table([seq(tv = mm:-matrices[tv], tv = tvars)]);
  tvars, subs(mm:-subs_set, eval(tt))
end:

_ORDMAX:=20:

#redctsum
# Input:
#   Sum: a sum in the form Sum(expr,var=range) or Sum(expr,var)
#   alg: list of the form [var1::type1,var2::type2,...]
#        where var1,...,vard are names and type1,... are in {diff,shift} or others that
#        Mgfun recognizes
#   optional:
#   certificate: a name 
#   LFSolbasis: a name
# Output:
#   basis: a basis of an ideal canceling the summand modulo the difference operator Delta
#  If certificate <> NUll:
#   the variable with name certificate will contain [basisC,basisDen] where
#   basisC is  a list of vectors representating certificates associated to each basis element and
#   basisDen is a list of multiples of the denominators appearing in the certificates above
#  If LFSolbasis <> NULL:
#   the variable with name LFSolbasis with contain a system of equations representing basis that 
#   can be given as input to the function LFSol_to_matrices.
#
# In this version, the shift,diff,... variables are denoted D[var].

redctsum:=proc(sum,alg,{certificate:=NULL,LFSolbasis:=NULL})
local n,var,vars,matrices,basis,comp,dim,i,Sn::nothing,shiftop,vv,cv,action,X,ini,certif,j;
local mm,ratfun::nothing,F,den;
local pow_mat_Sn,BasisInv,matricesNB,matricesNBden,certD,LFSolb,cert;
  cert:= evalb(certificate <> NULL);
  LFSolb:=evalb(LFSolbasis <> NULL);
  n:=op(2,sum);
  if type(n,`=`) then n:=op(1,n) fi;
  ### translate sum into a GB in matrix form
  F:=op(1,sum);
  if op(0,F)='LFSol' then
    mm := LFSol_to_matrices(F, {n :: 'shift', op(alg)})
  else
    mm := dfinite_expr_to_matrices(F, {n :: 'shift', op(alg)})
  fi;
  vars, matrices := really_lose_info_I_mean_it(mm);

  dim:=op([1,1],matrices[vars[1]]);
  userinfo(1,'redct',"dimension",dim);
  ### Cyclic vector method
  # compute a cyclic vector cv for the shift
  basis,comp:=cyclic_vec_sum(matrices[n::'shift'],n);
  cv:=convert(basis[1..dim,1..1],Vector);

  # compute the adjoint of the minimal operator in the shift annihilating cv
  den:=lcm(seq(denom(comp[i]),i=1..dim));
  shiftop:=OrePoly(seq(-normal(comp[i]*den),i=1..dim),den);
  userinfo(1,'redct',"annihilating operator of the summand",shiftop);

  ### compute the actions on multiples of the cyclic vector
  ### that is maps lambda_i st D_i(R)=lambda_i(R) + Delta(...)
  if cert then 
    BasisInv:=LinearAlgebra['MatrixInverse'](basis);

    for vv in vars do
      var:=op(1,vv);
      if op(2,vv)='shift' then
        matricesNB[vv]:=map(normal,BasisInv.matrices[vv].eval(basis,op(1,vv)=op(1,vv)+1));
      else 
        matricesNB[vv]:=map(normal,BasisInv.(matrices[vv].basis+diff(basis,op(1,vv))));
      fi;
      matricesNBden[vv]:=lcm(seq(seq(primpart(matricesNB[i,j],var),i=1..dim),j=1..dim));
    od;
    pow_mat_Sn[0]:= copy(cv);
    for i from 1 to dim do 
      pow_mat_Sn[i]:=map(normal,matricesNB[n::'shift'].eval(pow_mat_Sn[i-1],n=n+1));
    od;
  fi;

  for vv in vars do
    var:=op(1,vv);
    if var=n then
      if dim=1 then X:=comp else X:=[0,1,0$(dim-2)] fi
    elif op(2,vv)='diff' then
      X:=LinearAlgebra['LinearSolve'](basis,map(diff,cv,var)+matrices[vv].cv);
    elif op(2,vv)='shift' then
      X:=LinearAlgebra['LinearSolve'](basis,matrices[vv].subs(var=var+1,cv));
    else error "two lines missing in the code"
    fi;

    if op(2,vv)='shift' then
      action[op(1,vv)]:=subs(_v=op(1,vv),_n=n,_dim=dim,_X=copy(X),_arg=ratfun,
        proc(_arg) add(subs(_n=_n-i,subs(_v=_v+1,_arg)*_X[i+1]),i=0.._dim-1) end);
    else
      action[op(1,vv)]:=subs(_v=op(1,vv),_n=n,_dim=dim,_X=copy(X),_arg=ratfun,
        proc(_arg) add(subs(_n=_n-i,_arg*_X[i+1]),i=0.._dim-1)+diff(_arg,_v) end);
    fi;

    if cert then 
      if op(2,vv)='shift' then
    
        certif[op(1,vv)]:=subs(_v=op(1,vv),_mat=copy(matricesNB[vv]), _n=n, _X=copy(X), _arg=ratfun, _cv=cv,_dim=dim, _pow_mat_Sn=copy(pow_mat_Sn),
          proc(_arg,_arg2) certif_lagrange_v(_X,_n,eval(_arg,_v=_v+1))+
          add(eval(_arg2[i],_v=_v+1)*_mat._pow_mat_Sn[i-1],i=1.._dim) end);

        certD[op(1,vv)]:= subs(_v=op(1,vv),_tmp=matricesNBden[vv],
          proc(_arg) lcm(eval(_arg,_v=_v+1),_tmp) end );
      else
        certif[op(1,vv)]:=subs(_v=op(1,vv),_mat=copy(matricesNB[vv]), _n=n, _X=copy(X), _arg=ratfun, _cv=cv, _dim=dim, _pow_mat_Sn=copy(pow_mat_Sn),
          proc(_arg,_arg2) certif_lagrange_v(_X,_n,_arg)+map(_i-> if _i=0 then 0 else Diff(_i,_v) fi,_arg2)+
          add(_arg2[i]*(_mat._pow_mat_Sn[i-1] + map(_i-> if _i=0 then 0 else Diff(_i,_v) fi,_pow_mat_Sn[i-1]))     ,i=1.._dim) end);

        certD[op(1,vv)]:= subs(_tmp=matricesNBden[vv],
          proc(_arg) lcm(_arg,_tmp) end );
      fi;
    fi;
  od;

  ### ini satisfies 1 = ini * cyclic vector
  ini:=LinearAlgebra['LinearSolve'](basis,Vector([1,0$(dim-1)]))[1];

  
  scalar_red_ctsum(shiftop,ini,subs(n::'shift'=NULL,vars),eval(action),eval(certif),eval(certD),Dvar=D[n],tvar=n,_options)
end:

#scalar_red_cet
# Input:
#   _shiftop: minimal operator in D[tvar] annihilating the cyclic vector ini.
#   ini: cyclic vector 
#   vars: list of variables of the form [var1::type1,var2::type2,...]
#   action: table storing the morphisms defined in Prop 3. of our paper
#   certif: table storing morphisms computing the certificates associated to the morphisms above
#   CertifDen: table storing morphisms computing a multiple of the certificates computed above
#   certS: Boolean, if true, the certificates and multiple of their denominators are computed
#   LFSolb: Boolean, if true, basisLFS is computed
#   Dvar: operation associated to the summation variable
#   tvar: summation variable
# Output:
#   basis: a basis of an ideal canceling the summand modulo the difference operator Delta
#  If certificate <> NUll:
#   the variable with name certificate will contain [basisC,basisDen] where
#   basisC is  a list of vectors representating certificates associated to each basis element and
#   basisDen is a list of multiples of the denominators appearing in the certificates above
#  If LFSolbasis <> NULL:
#   the variable with name LFSolbasis with contain a system of equations representing basis that 
#   can be given as input to the function LFSol_to_matrices.

 
scalar_red_ctsum:=proc(_shiftop,ini,vars,action,certif,CertifDen,
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      certificate := NULL,
      LFSolbasis := NULL
    })
local denovergg,denquoovergg,rnd,rndpoint,n,HH,quotient,nextmons,mon,
i,basis,lmons,red,var,dvars,diffvars,dvar,prevmons,X::nothing,prev,typevar,
den,num,co,denquo,elementquotient,gg,newelt,newrel,sol,sys,pol,goodfact,
varsres,mat,inds,shiftop, certificates, CertificateDen, tmp1,tmp2,basisC,newrelC,
dim,tmp3,NewRelDen,BasisDen,rec,shiftvars,basisLFS,oper,terms,newop,argdiff,argshift,l,c,t,
LFSolb,cert,certS;
  certS:= evalb(certificate <> NULL);
  LFSolb:=evalb(LFSolbasis <> NULL);
  dvars:=[seq(D[op(1,i)],i=vars)];
  n:=tvar;
  shiftop:=_shiftop;
  dim:=nops(shiftop)-1;
  dvars:=[seq(D[op(1,i)],i=vars)];
  varsres:=map2(op,1,vars);
  for i in vars do typevar[op(1,i)]:=op(2,i) od;
  diffvars:={op(select(has,dvars,map2(op,1,select(has,vars,diff))))};
  shiftvars:={op(select(has,dvars,map2(op,1,select(has,vars,'shift'))))};
  quotient:=[];
  nextmons:=[1];
  certificates[1]:=Vector(dim);
  CertificateDen[1]:=1;
  basis:=[];
  basisLFS:=[];
  basisC:=[];
  BasisDen:=[];
  lmons:={};
  HH:=ini; # initial rational function
  elementquotient:=0;
  denquo:=1;
  pol[1]:=1;
  inds:=indets(shiftop,name) minus {n,D[n]} union {op(varsres)};
  rnd:=rand(-1000..1000);
  rndpoint:=[seq(op(1,i)=rnd(),i=inds)];
  userinfo(4,'redct',"computing exceptional sets at time ",time());
  rec:=InitRed(shiftop,n,certS);
  userinfo(4,'redct',"exceptional sets computed at time",time());

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
      if certS then 
        certificates[mon]:=certif[var](prev,certificates[mon/dvar]);
        CertificateDen[mon]:=CertifDen[var](CertificateDen[mon/dvar]);
      fi;
      HH:=normal(HH);
      if typevar[var]='diff' then
        pol[mon]:=collect(diff(pol[mon/dvar],var)+pol[mon/dvar]*dvar,dvars,expand);
      else # shift
        pol[mon]:=collect(subs(subs(var=var+1,dvar)=dvar,
            subs(var=var+1,pol[mon/dvar]*dvar)),dvars,expand);
      fi;
    fi;

    tmp1,tmp2,tmp3:=Reduction(HH,rec);
    # print("mon",mon,testcert(tmp1-HH,-tmp2,_S,__v));
    red[mon]:=normal(tmp1);
    if certS then
      certificates[mon]:=certificates[mon]+tmp2;
      CertificateDen[mon]:=lcm(CertificateDen[mon],tmp3);
    fi;


    userinfo(2,'redct',"reduction done at time:",time());
    userinfo(4,'redct',"reduces to",red[mon]);
    ########### Find linear relation ############
    den:=primpart(denom(red[mon]),n,'goodfact');
    num:=primpart(numer(red[mon]),n,'co');
    if co=0 then co:=1 fi;

    pol[mon]:=goodfact*pol[mon]/co;
    
    certificates[mon]:=goodfact/co*certificates[mon];

    red[mon]:=num/den;
    gg:=gcd(denquo,den);
    divide(den,gg,'denovergg');
    divide(denquo,gg,'denquoovergg');
    denquo:=denquo*denovergg;
    elementquotient:=expand(denovergg*elementquotient);
    newelt:=expand(denquoovergg*numer(red[mon]));
    sys:={coeffs(elementquotient-newelt,n)} minus {0};
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
      newrel:=primpart(collect(pol[mon]-add(sol[i]*pol[quotient[i]],i=1..nops(quotient)),dvars),dvars,'co');
      if certS then 
        newrelC:=(certificates[mon]-add(sol[i]*certificates[quotient[i]],i=1..nops(quotient)))/co;
        NewRelDen:=lcm(CertificateDen[mon],seq(CertificateDen[quotient[i]],i=1..nops(quotient)));      
        fi;
      userinfo(3,'redct',"relation:",sprintf("%.300a",newrel));
      basis:=[op(basis),collect(newrel,dvars,'distributed')];
      if certS then basisC:=[op(basisC),newrelC]; BasisDen:=[op(BasisDen),NewRelDen] fi;

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

  if LFSolb then 
    for oper in basis do 
      terms:=[coeffs(oper,dvars,'t')];
      t:=[t];
      newop:=0;
      for i from 1 to nops(terms) do 
        argdiff:= NULL;
        argshift:= NULL;
        for l in diffvars do 
          c:= degree(t[i],l);
          if c>0 then argdiff:= argdiff,op(1,l)$c fi;
        od;
        for l in shiftvars do 
          c:= degree(t[i],l);
          if c>0 then argshift:= argshift,op(1,l)=op(1,l)+c fi;
        od;

        if nops([argdiff])> 0 then 
          newop:= newop + terms[i]*eval(diff(__f(op(varsres)),[argdiff]),[argshift]);
        else 
          newop:= newop + terms[i]*eval(__f(op(varsres)),[argshift]);
        fi;
      od;
      basisLFS:= [op(basisLFS),newop];
    od;
    LFSolbasis:=LFSol({op(basisLFS)});
  fi;

  if certS then
    certificate:=[basisC,BasisDen];
  fi;

  basis
end:

#cyclic_vec_sum
# Input:
#   . A   matrix s.t.  Sn(V.Y) = A.V(n+1)Y
#   . var wrt which the shift Sn is performed
#   . ini (optional) coordinates of the cyclic vector
#   . nbtests (internal), initially 0, counts the number of
#       vectors whose cyclicity has failed
# Output:
#   . P   matrix whose columns are the coordinates of the successive
#       shifts of the first column (the cyclic vector) in the old basis
#   . C   vector containing the coefficients of the corresponding companion matrix
#
cyclic_vec_sum:=proc(A,var)
local dim,V,cycl,i,j,comp,Basis,U,W,rk,rk2;
  dim:=op([1,1],A);
  V:=Vector[column]([1,0$(dim-1)]);
  U,rk,cycl:=try_cyclic_vec_sum(A,var,V);
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
      U,rk2,cycl:=try_cyclic_vec_sum(A,var,W);
      if rk2>rk then V:=W; rk:=rk2; break fi;
    od
  od;
  if {seq(V[i],i=2..dim)} minus {0}<>{} then
    userinfo(2,'redct',"using cyclic vector:",convert(V,list));
  fi;
  Basis:=Matrix([seq(cycl[i],i=1..dim)]);
  cycl[dim+1]:=map(normal,A.eval(cycl[dim],var=var+1));
  comp:=LinearAlgebra['LinearSolve'](Basis,cycl[dim+1]);
  Basis,comp
end:

try_cyclic_vec_sum:=proc(A,var,ini)
local dim,cycl,i,UU,rk;
  dim:=op([1,1],A);
  cycl[1]:=ini;
  UU:=Matrix(LinearAlgebra['Transpose'](cycl[1]));
  for i to dim-1 do
    cycl[i+1]:=map(normal,A.eval(cycl[i],var=var+1));
    UU:=<UU,LinearAlgebra['Transpose'](cycl[i+1])>;
    UU,rk:=LinearAlgebra['LUDecomposition'](UU,'output'=['U','rank']);
    if rk<>i+1 then return UU,rk,cycl fi
  od;
  return UU,dim,cycl
end:


# Input:
# - X a linear operator in Sn given as a vector 
# - n the variable associated to Sn
# - u a rational function
#
# Output:
# - The certificate G that satisfies uL(cv)-L*(u)cv = \Delta_n(G(u,cv)) (lagrange identity)
#   where L is the operator represented by X
certif_lagrange_v:=proc(X,n,u)
    local dim,result,i,k;
    dim:=op(1,X);
    result:=Vector(dim);
    result[1]:=add(eval(X[i+1]*u,n=n-i),i=1..dim-1);
    for i from 2 to dim do 
        result[i]:=add(eval(X[k+1]*u,n=n-k+i-1),k=i..dim-1);
    od;
    result
end:

#hypergeomtosum
# Input:
#   l1: a list of integer of length a
#   l2: a list of integer of length b
#   x: a symbol
#   n: a symbol
# Output:
#   the hypergeometric function aFb (op(l1);op(l2);x) where the summation variable is n

HypergeomToSum:=proc(l1,l2,x,n);
  local i;
  Sum(mul(GAMMA(i+n) /GAMMA(i),i=l1)*mul(GAMMA(i)/GAMMA(i+n),i=l2)*x^n/n!,n=0..infinity)
end:

#EvalCert
# Input:
#   S: a sum in the form Sum(expr,var=range) or Sum(expr,var)
#   certt: the certificate returned by redct. It corresponds to an operator in S_var stored as a vector
#   point: point at which the certificate applied to expr will be evaluated
# Output:
#   the certificate applied to expr and evaluated at var=point
#
# It assumes that 1 is cyclic
# !!! The function simplify is used to simplify expr at var = point 

EvalCert:=proc(S,certt,point)
local cert,i,F,var;
    F:=op(1,S);
    var:=op(2,S);
    var:=op(1,var);
    cert:=add(eval(certt[i+1],var=point)*(simplify(eval(F,var=point+i))),i=0..LinearAlgebra['RowDimension'](certt)-1);
    normal(value(cert));
end;


#HeuristicEvalCert
# Input:
#   S: a sum in the form Sum(expr,var=range) or Sum(expr,var)
#   certt: the certificate returned by redct. It corresponds to an operator in S_var stored as a vector
#   point: point at which the certificate applied to expr will be evaluated
#   vars: a list of variables of the form [var1::type1,var2::type2,...]
# Output:
#   an approximation of the certificate applied to expr and evaluated at var=point
#   More precisely, the variable in vars w.r.t. the shift are evaluated at a random non-zero integer 
#   between -1000 and 1000, and diff variables are evaluated at p/q with p and q similarly 
#   random non-zero integer between -1000 and 1000
#
#   It assumes that 1 is cyclic


HeuristicEvalCert:=proc(S,certt,point,vars)
local cert,i,F,var,res,svars,l,dvars,rndspoint,rnddpoint;
    F:=op(1,S);
    var:=op(2,S);
    var:=op(1,var);
    svars:=select(i -> evalb(op(2,i) = 'shift'),vars);
    svars := {seq(op(1,l),l in svars)};
    svars := svars minus {var};
    dvars:=select(i -> evalb(op(2,i) = diff),vars);
    dvars := {seq(op(1,l),l in dvars)};
    rndspoint:=[seq(i=rnd(),i in svars)];
    rnddpoint:=[seq(i=rnd()/rnd(),i in dvars)];
    cert:=add(eval(certt[i+1],var=point)*(eval(F,var=point+i)),i=0..LinearAlgebra['RowDimension'](certt)-1);
    cert:= eval(cert,rndspoint);
    res:= value(cert);

    res:=eval(res,rnddpoint);
    evalf(res,100);
end;
    

#testcert:
# Input:
#   T: a telescoper as returned by redct
#   G: a certificate as returned by redct
#   S: a sum as given in input of redct
#   varss: a list of variable as given in input of redct
# Output:
#   true or false depending on whether the couple (T,G) corresponds to an element 
#   of the annihilator of the summand.
#
# It assumes that 1 is cyclic


TestCert:=proc(T,G,S,varss)
    local Fv,mm,subsvars,GB,Mord,res,polpart,dvars,DeltG,arg,Aring,Gv,n,vars,i,var;
    n:=op(2,S);
    if type(n,`=`) then n:=op(1,n) fi;
    vars:=[n::'shift',op(varss)];

    Fv:=op(1,S);
    if op(0,S)='LFSol' then
        mm := LFSol_to_matrices(Fv, {n :: 'shift', op(vars)})
    else
        mm := dfinite_expr_to_matrices(Fv, {n :: 'shift', op(vars)})
    fi;
    Gv:=value(G);
    Gv:=add(normal(Gv[i+1])*D[n]^i,i=0..op(1,G)-1);
    subsvars:=[seq(D[op(2,op(2,i))]= op(1,op(2,i)),i in mm:-algebra["type_struct"])];
    dvars:=[seq(op(1,op(2,i)),i in mm:-algebra["type_struct"])];
    GB:=mm:-gbasis;
    GB:=map(collect, mm:-gbasis, dvars);
    arg:=seq(op(2,var)=[D[op(1,var)],op(1,var)],var in vars);
    arg:=eval(arg,subsvars);
    Aring:=Ore_algebra['skew_algebra'](arg);
    Mord:=Groebner['MonomialOrder'](Aring,tdeg(op(dvars)));
    GB:=Groebner['Basis'](GB,Mord);
    DeltG:=eval(eval(Gv,n=n+1),D[n+1]=D[n])*D[n]-Gv;
    res:=eval(T-DeltG,subsvars);
    res:= Groebner['NormalForm'](res,GB,Mord);
    evalb(res=0)
end;




#heuristictestcert:proc(TGF,varss)
# Input:
#   T: a telescoper as returned by redct
#   G: a certificate as returned by redct
#   S: a sum as given in input of redct
#   vars: a list of variable as given in input of redct
# Output:
#   a numerical approximation of the equation "telescoper - \Delta_n (certificate)" applied to the summand
#   where the variable in vars w.r.t. the shift are evaluated at a random non-zero integer 
#   between -1000 and 1000, and diff variables are evaluated at p/q with p and q similarly 
#   random non-zero integer between -1000 and 1000
#
# It assumes that 1 is cyclic



HeuristicTestCert:=proc(T,G,S,vars)
    local n,svars,dvars,rndpoint,Fv,Tv,Fvv,resT,tmp,l,i,Gv,v,npoint,DGv;

    n:=op(2,S);
    if type(n,`=`) then n:=op(1,n) fi;
    svars:=select(i -> evalb(op(2,i) = 'shift'),vars);
    svars := {seq(op(1,l),l in svars)};
    svars := svars minus {n};
    dvars:=select(i -> evalb(op(2,i) = diff),vars);
    dvars := {seq(op(1,l),l in dvars)};

    rndpoint:=[seq(i=rnd()/rnd(),i in dvars),seq(i=rnd(),i in svars)];
    npoint := rnd();
    #print("dvars",dvars,svars);
    Fv:=op(1,S);
    Gv:=eval(value(G),rndpoint);
    Gv:=eval(add(Gv[i+1]*eval(Fv,n=n+i),i=0..op(1,G)-1),rndpoint);
    DGv:= eval(eval(Gv,n=n+1)-Gv,n=npoint);

    Tv:=collect(T,[seq(D[i], i in [op(svars),op(dvars)])],'distributed');
    if type(Tv,`+`) then Tv:= [op(Tv)]; else Tv:=[Tv]; fi;
    resT:=0;
    for l in Tv do 
      Fvv:=Fv;
      for v in svars do 
        Fvv:=eval(Fvv,v=v+degree(l,D[v]));
      od;
      for v in dvars do 
        if degree(l,D[v]) > 0 then Fvv:=diff(Fvv,v$degree(l,D[v])) fi;
      od;
      #print("l",l,Fvv);
      tmp:= eval(l,[seq(D[v]=1,v in svars),seq(D[v]=1,v in dvars)]);
      #print(tmp);
      tmp := eval(tmp*Fvv,rndpoint);
      tmp:= eval(tmp,n=npoint);
      resT:= resT + tmp;
    od;
    # print("T",resT);
    # print("DGv",DGv);

    return evalf(resT-DGv,100);
end;


