read "Mgfun_missing.mpl":

macro(translate=PolynomialTools['Translate']);

read "red_difference_op.mpl";

_ORDMAX:=20:

really_lose_info_I_mean_it := proc(mm, $)
  local tv, tvars := mm:-typed_vars;
  local tt := table([seq(tv = mm:-matrices[tv], tv = tvars)]);
  tvars, subs(mm:-subs_set, eval(tt))
end:

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
#   the variable with name certificate will contain a list of operators representing 
#   certificates associated to each basis element
#  If LFSolbasis <> NULL:
#   the variable with name LFSolbasis will contain a system of equations representing a basis that 
#   can be given as input to the function LFSol_to_matrices.
#
# In this version, the shift,diff,... variables are denoted D[var].

redctsum:=proc(sum,alg,{certificate:=NULL,LFSolbasis:=NULL},$)
local n,var,vars,matrices,basis,comp,dim,i,shiftop,vv,cv,X,ini;
local mm,F,den,Xstar,res;
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
  basis,comp:=cyclic_vec_shift(matrices[n::'shift'],n);
  cv:=convert(basis[1..dim,1..1],Vector);

  # compute the adjoint of the minimal operator in the shift annihilating cv
  den:=lcm(seq(denom(comp[i]),i=1..dim));
  shiftop:=OrePoly(seq(-normal(comp[i]*den),i=1..dim),den);
  userinfo(4,'redct',"annihilating operator of the summand:",shiftop);

  for vv in vars do
    var:=op(1,vv);
    if var=n then
      if dim=1 then X[var]:=comp else X[var]:=[0,1,0$(dim-2)] fi
    elif op(2,vv)='diff' then
      X[var]:=LinearAlgebra['LinearSolve'](basis,map(diff,cv,var)+matrices[vv].cv);
    elif op(2,vv)='shift' then
      X[var]:=LinearAlgebra['LinearSolve'](basis,matrices[vv].map(translate,cv,var,1))
    else error "type unknown:",op(2,vv)
    fi;
    if not type(X[var],'list') then X[var]:=convert(X[var],list) fi;
    # X is D(var)(cyclic vector) in the basis [1,Sn,Sn^2,...] (B_i in the article)
    # Xstar is its adjoint
    Xstar[op(1,vv)]:=[op(2,vv),adjoint_shift(X[var],dim,n)]
  od;

  ### ini satisfies 1 = ini * cyclic vector, ie, it contains
  ### the coordinates of 1 in the basis cv, S_n(cv), S_n^2(cv),...
  ini:=LinearAlgebra['LinearSolve'](basis,Vector([1,0$(dim-1)]))[1];

  # alg instead of vars to keep the order given by the user  
  res:=scalar_red_ct_sum(shiftop,ini,subs(n::'shift'=NULL,alg),eval(X),eval(Xstar),mm,cv,'Dvar'=D[n],'tvar'=n,_options);
  forget('Dmon','MulPfrac','normaldag');
  res;
end:

#scalar_red_ct_sum
# Input:
#   shiftop: minimal operator in D[tvar] annihilating the cyclic vector ini.
#   ini: cyclic vector 
#   vars: list of variables of the form [var1::type1,var2::type2,...]
#   Xstar: table storing the B_i^* defined in Prop 3. of our paper
#   CertifDen: table storing morphisms computing a multiple of the certificates computed above
#   mm: output of dfinite_expr_to_matrices or LFSol_to_matrices, used internally to check certificates
#   cv: cyclic vector, also used only in certificate checking internally
#     it is a vector of coordinates in the basis mm:-basis
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
#
#  This code uses partial fraction decompositions wrt n=tvar a lot. These are stored as
#  polynomials in two variables _Pfrac and _Shift. A term
#     c(n,others) * _Pfrac[pol(n,others)]^k * _Shift^m,
#  with pol primitive wrt n (and irreducible?) encodes the partial fraction 
#     c(n,others) / pol(n-m)^k.
#  During intermediate computations, it may happen that degree(c,n) > k * degree(pol,n).
#  This is dealt with in a later stage.
#
scalar_red_ct_sum:=proc(shiftop,ini,vars,X,Xstar,
    mm,cv,
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      certificate := NULL,
      LFSolbasis := NULL
    })
local rnd,rndpoint,n,HH,quotient,nextmons,mon,
i,basis,lmons,red,var,dvars,diffvars,dvar,prevmons,x::nothing,prev,typevar,
co,elementquotient,newelt,newrel,sol,sys,pol,
varsres,mat,inds, certificates, basisC,newrelC,
rec,shiftvars,basisLFS,oper,terms,newop,argdiff,argshift,l,c,t,
LFSolb,cert,certS,ttt:=time(),coHH,cert2,densol, ord;
  certS:= evalb(certificate <> NULL);
  LFSolb:=evalb(LFSolbasis <> NULL);
  dvars:=[seq(D[op(1,i)],i=vars)];
  n:=tvar;

  userinfo(2,'redct',"computing exceptional sets at time ",time()-ttt);
  rec:=InitRed(shiftop,n,certS);
  userinfo(2,'redct',"exceptional sets computed at time",time()-ttt);

  dvars:=[seq(D[op(1,i)],i=vars)];
  varsres:=map2(op,1,vars);
  for i in vars do typevar[op(1,i)]:=op(2,i) od;
  diffvars:={op(select(has,dvars,map2(op,1,select(has,vars,diff))))};
  shiftvars:={op(select(has,dvars,map2(op,1,select(has,vars,'shift'))))};
  quotient:=[];
  nextmons:=[1];
  basis:=[];
  basisLFS:=[];
  basisC:=[];
  lmons:={};
  elementquotient:=0;
  pol[1]:=1;
  inds:=indets(shiftop,name) minus {n,D[n]} union {op(varsres)};
  rnd:=rand(-1000..1000);
  rndpoint:=[seq(op(1,i)=rnd(),i=inds)];
  ord := tdeg(seq(D[op(1,var)], var in vars));


  HH:=ShiftlessDecIrred(ini,rec); # initial rational function
  certificates[1]:=0;coHH:=1;

  # find generators of a D-finite ideal, or a quotient of dimension > _ORDMAX
  # Aim: for each monomial mon we compute pol[mon],red[mon],certificates[mon] s.t.
  #   pol[mon] = red[mon] gamma 
  #                     + Delta_n certificates[mon] gamma modulo Ann(summand).
  # where 
  #   pol[mon] is an operator with mon as its leading monomial and
  #   red[mon] is a rational function.
  while nextmons<>[] and nops(lmons)<_ORDMAX do
    mon:=nextmons[1];
    nextmons:=subsop(1=NULL,nextmons);
    if member(true,map2(divide,mon,lmons)) then next fi;
    userinfo(2,'redct',"dealing with monomial",mon,"at time:",time()-ttt);
    ######### Compute rational function to be reduced ########
    prevmons:=select(has,indets(mon,indexed),dvars);
    if prevmons<>{} then # the other case is when HH=ini
      # give an advantage to differentiation
      if has(prevmons,diffvars) then prevmons:=prevmons intersect diffvars fi;
      dvar:=prevmons[min[index](map(length,[seq(red[mon/i],i=prevmons)]))];
      prev:=red[mon/dvar]; # supposed to be collected in _Pfrac
      var:=op(dvar);
      # D[var] pol[mon/dvar] = HH gamma + Delta_n certificates[mon] gamma
      HH,coHH,certificates[mon]:=PfracAction(
        prev,X[var],Xstar[var],certificates[mon/dvar],var,rec);
      # pol[mon] = D[var] pol[mon/dvar]
      if typevar[var]='diff' then
        pol[mon]:=collect(diff(pol[mon/dvar],var)+pol[mon/dvar]*dvar,dvars,normal);
      else # shift
        pol[mon]:=collect(subs(subs(var=var+1,dvar)=dvar,
            subs(var=var+1,pol[mon/dvar]*dvar)),dvars,normal);
      fi;
    fi;
    # divide pol[mon], HH, certificates[mon] by coHH
#    inds:=indets(HH,specindex(anything,_Pfrac)) union {_Shift,n};
    #HH:=primpart(HH,inds,'coHH');
    #if coHH=0 then coHH:=1 fi;
    pol[mon]:=collect(pol[mon]*coHH,dvars,normal);
    if certS then certificates[mon]:=certificates[mon]*coHH fi;

    userinfo(2,'redct',"entering reduction at time:",time()-ttt);
    # HH = red[mon] + L^*(cert)
    red[mon],cert:=Reduction(HH,rec); 
    userinfo(2,'redct',"reduction done at time:",time()-ttt);
    userinfo(3,'redct',"size of the canonical form:", length(red[mon]));
    userinfo(4,'redct',"reduces to",normal(CanonicalFormToRat(coHH*red[mon],rec)));

    if certS then 
      # L^*(cert) gamma + Delta_n P_L(cert) gamma = cert L gamma = 0 mod I
      cert2:=certif_lagrange_v(shiftop,n,cert);
      certificates[mon] -= cert2;
      ASSERT(internal_test_cert(pol[mon],CanonicalFormToRat(red[mon],rec),certificates[mon],cv,mm,n))
    fi;

    # At this stage,
    #   pol[mon] = red[mon] gamma + Delta_n certificates[mon] gamma mod I

    # pol[mon]:=pol[mon]/co; red[mon]:=red[mon]/co; certificates[mon]:=certificates[mon]/co
    red[mon]:=primpart(red[mon],indets(red[mon],specindex(anything,_Pfrac)) union {n,_Shift},'co');
    if co=0 then co:=1 fi;
    pol[mon]:=collect(pol[mon]/co,dvars,normal);
    certificates[mon]:=certificates[mon]/co;
    ########### Find linear relation ############
    sys:=expand(elementquotient-red[mon]);
    sys:={coeffs(sys,[op(indets(sys,specindex(anything,_Pfrac))),_Shift,n])};
    newelt:=red[mon];
    if remove(has,sys,x)<>{} then sol:=NULL
    else
      mat:=LinearAlgebra['GenerateMatrix'](sys, [seq(x[i],i=quotient)], 'augmented' = true);
      if op([1,1],mat)>=op([1,2],mat) then
      # probabilistic test of consistency first
        try
          sol:=LinearAlgebra['LinearSolve'](eval(mat,rndpoint),'method'='modular')
#          sol:=LinearAlgebra['LinearSolve'](eval(mat,rndpoint))
        catch "system is inconsistent","inconsistent system": sol:=NULL
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
      densol:=lcm(seq(denom(sol[i]),i=1..nops(quotient)));
      sol:=map(normal,sol*densol);
      newrel:=collect(densol*pol[mon]-add(sol[i]*pol[quotient[i]],i=1..nops(quotient)),dvars,normal);
      newrel:=primpart(newrel,dvars,'co');
      if certS then 
        newrelC:=(densol*certificates[mon]-add(sol[i]*certificates[quotient[i]],i=1..nops(quotient)))/co
      fi;
      userinfo(3,'redct',"relation:",sprintf("%.300a",newrel));
      basis:=[op(basis),collect(newrel,dvars,'distributed',normal)];
      if certS then basisC:=[op(basisC),newrelC] fi;
      lmons:=lmons union {mon}
    else
      quotient:=[op(quotient),mon];
      elementquotient:=elementquotient+x[mon]*newelt;
      for var in vars do
        if not member(mon*D[op(1,var)],nextmons) and
          not member(true,map2(divide,mon*D[op(1,var)],lmons)) then
          nextmons:=[op(nextmons),mon*D[op(1,var)]];
          nextmons := sort(nextmons,(a,b) -> Groebner[TestOrder](a,b,ord));
        fi
      od
    fi;
  od;
  userinfo(1,'redct',"dim quotient:",nops(quotient));
#  userinfo(1,'redct',"degree coeffs:",max(op(map(degree,basis,varsres))));

  if LFSolb then 
    for oper in basis do 
      terms:=coeffs(oper,dvars,'t');
      newop:=0;
      for i from 1 to nops([terms]) do 
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

        if argshift = NULL then argshift:= [] fi;
        if nops([argdiff])> 0 then 
          newop:= newop + terms[i]*eval(diff(__f(op(varsres)),argdiff),argshift);
        else 
          newop:= newop + terms[i]*eval(__f(op(varsres)),argshift);
        fi;
      od;
      basisLFS:= [op(basisLFS),newop];
    od;
    LFSolbasis:=LFSol({op(basisLFS)});
  fi;

  if certS then
    certificate:=basisC
  fi;

  basis
end:

# Partial fraction decomposition of D(var)(canform),
# with D(var)(R)=Xstar(R(var+1)) if var is a shift variable
# and D(var)(R)=Xstar(R)+diff(R,var) if it is a diff variable.
PfracAction:=proc(canform,X,Xstar,cert,var,rec)
local res,co,lco,lmon,Bstar,typevar,inds,nn,j,den,i,num,DR,sigmaR,newcert,Dvars;
  nn:=rec:-var;
  typevar:=Xstar[1];
  Bstar:=Xstar[2];
  inds:=indets(canform,specindex(anything,_Pfrac)) union {_Shift};
  lco:=[coeffs(canform,inds,'lmon')];lmon:=[lmon];
  if typevar='diff' then
    DR:=diff(canform,var)+add(lco[i]*Dmon(lmon[i],var,typevar,rec),i=1..nops(lmon));
    sigmaR:=canform
  else
    DR:=0;
    lco:=map(translate,lco,var,1);
    sigmaR:=(add(lco[i]*Dmon(lmon[i],var,typevar,rec),i=1..nops(lmon)));
    # Dmon may introduce new _Pfrac
    inds:=indets(sigmaR,specindex(anything,_Pfrac)) union {_Shift};
    lco:=map(normal,[coeffs(sigmaR,inds,'lmon')]);lmon:=[lmon]
  fi;
  for i from 0 to rec:-r-1 do # B^*(sigmaR)
    den:=primpart(denom(Bstar[i+1]),nn,'co');
    num:=numer(Bstar[i+1])/co;
    res[i]:=num*add(subs(nn=nn-i,lco[j])*MulPfrac(den,
      `if`(has(lmon[j],inds),_Shift^i,1)*lmon[j],rec),j=1..nops(lco))
  end do;
  if rec:-CertB then
    # 1. \partial_i cert
    Dvars:=indets(cert,specindex(name,'D'));
    newcert:=collect(cert,Dvars,'distributed');
    lco:=[coeffs(newcert,Dvars,'lmon')];lmon:=[lmon];
    if typevar='diff' then 
      newcert:=add(diff(lco[i],var)*lmon[i]+lco[i]*lmon[i]*D[var],i=1..nops(lco))
    else 
      newcert:=add(subs(var=var+1,lco[i])*lmon[i]*D[var],i=1..nops(lco))
    fi;
    # 2. P_{B_i}(sigma_i(R_\beta),\gamma)
    newcert += certif_lagrange_v(X,nn,sigmaR)
  fi;
  den:=lcm(denom(DR),seq(denom(res[i]),i=0..rec:-r-1));
  den:=subs([seq(i=1,i=inds)],den);
  den*DR+add(den*res[i],i=0..rec:-r-1),den,newcert
end:

# derivative or shift (depending on typevar) of the monomial mon
# wrt to var
# Recall that 
#     _Pfrac[pol(n,others)]^k * _Shift^m,
#  with pol primitive wrt n encodes the partial fraction 
#     c(n,others) / pol(n-m)^k.
Dmon:=proc(mon,var,typevar,rec)
option remember;
local shft,deg,pole,ind;
  if not has(mon,var) then if typevar=diff then return 0 else return mon fi fi;
  shft:=degree(mon,_Shift);
  ind:=op(indets(mon,specindex(anything,_Pfrac)));
  deg:=degree(mon,ind);
  pole:=op(ind);
  if typevar='diff' then # d/dvar(1/pole(n-shift)^deg)
    -deg*ind^(deg+1)*_Shift^shft*translate(diff(pole,var),rec:-var,-shft)
  else  
    ShiftlessDecIrred(1/subs([var=var+1,rec:-var=rec:-var-shft],pole)^deg,rec)
  fi;
end:

# mon/pol
# could be improved more
MulPfrac:=proc(pol,mon,rec)
option remember;
  if pol=1 then mon 
  else ShiftlessDecIrred(CanonicalFormToRat(mon,rec)/pol,rec)
  fi;
end:

CanonicalFormToRat:=proc(R,rec)
local inds,i,j;
    inds:=indets(R,specindex(anything,_Pfrac));
    add(subs(seq(j=subs(rec:-var=rec:-var-i,1/op(j)),j=inds),coeff(R,_Shift,i)),
      i=ldegree(R,_Shift)..degree(R,_Shift))
end:

#splitdenom
# Input: 
#   . den polynomial
#   . n its variable
# Output:
#   the factors of den are refined by taking pairwise gcds
splitdenom:=proc(den,n)
local listfacts,split,i;
  if not type(den,`*`) then return den fi;
  listfacts:=select(has,[op(den)],n);
  split:=splitlist(listfacts,n);
  subs([seq(listfacts[i]=split[i],i=1..nops(listfacts))],den)
end:

splitlist:=proc(listfacts,n)
local pol, others, g, c1, c2, q;
  if nops(listfacts)<=1 then return listfacts fi;
  pol:=op(1,listfacts);
  others:=thisproc(subsop(1=NULL,listfacts),n);
  for q in others do
    g:=gcd(pol,q,'c1','c2');
    if g<>1 then
      others:=subs(q=g*c2,others);
      pol:=g*c1
    fi
  od;
  [pol,op(others)]
end:

#cyclic_vec
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
cyclic_vec_shift:=proc(A,var)
local dim,V,cycl,i,j,comp,Basis,U,W,rk,rk2;
  dim:=op([1,1],A);
  V:=Vector[column]([1,0$(dim-1)]);
  U,rk,cycl:=try_cyclic_vec_shift(A,var,V);
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
      U,rk2,cycl:=try_cyclic_vec_shift(A,var,W);
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

try_cyclic_vec_shift:=proc(A,var,ini)
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
# - X a linear operator in Sn given as a list or an OrePoly of coefficients
# - n the variable associated to Sn
# - u a rational function (given as a dag, can be huge)
#
# Output:
# - The quotient of the left division of uX by (S_n-1)
certif_lagrange_v:=proc(X,n,u)
local dim,i,j;
    dim:=nops(X)-1;
    add(add(subs(n=n+i-j,op(j+1,X)*u),j=i+1..dim)*D[n]^i,i=0..dim-1)
end:

#hypergeomtosum
# Input:
#   l1: a list of integer of length a
#   l2: a list of integer of length b
#   x: a symbol
#   n: a symbol
# Output:
#   the hypergeometric function aFb (op(l1);op(l2);x) where the summation variable is n

hypergeomtosum:=proc(l1,l2,x,n);
  local i;
  Sum(mul(GAMMA(i+n) /GAMMA(i),i=l1)*mul(GAMMA(i)/GAMMA(i+n),i=l2)*x^n/n!,n=0..infinity)
end:

#EvalCert
# Input:
#   S: a sum in the form Sum(expr,var=range) or Sum(expr,var)
#   certt: the certificate returned by redct.
#   vars: of the form [x::diff, k::shift] as in the input of redct
#   point (optional): list of equalities var=value 
#     defining a point at which the certificate applied to expr will be evaluated
# Output:
#   the certificate applied to expr and evaluated at point
#
EvalCert:=proc(certt,S,varss,point :: list := [],{series :: boolean:=false},$)
local i,F,vars,var,dvars,lco,lmon,valmon,typevars,typev,mon,tosubs,v,vv,res,dvarsalg,mm,varsalg,pointvalue,pointseries;
    var:=op(2,S);
    if type(var,`=`) then var:=op(1,var) fi;
    vars:=[var::'shift',op(varss)];

    if series then
      if not member(var,map2(op,1,point),'i') then
        error "missing point where the expression must be expanded in series wrt",var fi;
      pointseries:=op(i,point);
      pointvalue:=subsop(i=NULL,point)
    else pointvalue:=point
    fi;


    F:=op(1,S);
    if op(0,S)='LFSol' then
        mm := LFSol_to_matrices(F, {var :: 'shift', op(vars)})
    else
        mm := dfinite_expr_to_matrices(F, {var :: 'shift', op(vars)})
    fi;
    dvars:=indets(certt,specindex(anything,D));
    typevars:=[seq(op(1,i)=op(2,i),i=vars)];
    lco:=[coeffs(collect(certt,dvars,'distributed'),dvars,'lmon')];lmon:=[lmon];
    lco:=eval(lco,pointvalue);
    if series then lco:=map(:-series,lco,pointseries) fi;
    varsalg:=map2(op,2,mm:-algebra["type_struct"]);
    dvarsalg:=[seq(D[vv[2]]=vv[1],vv=varsalg)];
    res:=add(lco[i]*Groebner['NormalForm'](subs(dvarsalg,lmon[i]),mm:-gbasis,mm:-ordering),i=1..nops(lco));
    res:=subs([seq(op(2,i)=op(1,i),i=dvarsalg)],res);
    dvars:=indets(res,specindex(anything,D));
    lco:=[coeffs(collect(res,dvars,'distributed'),dvars,'lmon')];lmon:=[lmon];
    lco:=eval(lco,pointvalue);
    if series then lco:=map(:-series,lco,pointseries)
    else lco:=normaldag(lco); forget('normaldag')
    fi;
    for mon in lmon do
      valmon:=F;
      for v in indets(mon) intersect dvars do
        vv:=op(v);
        typev:=subs(typevars,vv);
        if typev='diff' then 
          valmon:=diff(valmon,[vv$degree(mon,v)])
        else # typev=shift
          valmon:=subs(vv=vv+degree(mon,v),valmon)
        fi;
      end do;
      tosubs[mon]:=eval(valmon,pointvalue);
      if series then
        tosubs[mon]:= :-series(tosubs[mon],pointseries)
      fi;
    end do;
    res:=normal(add(lco[i]*tosubs[lmon[i]],i=1..nops(lco)));
    if series then :-series(res,pointseries)
    else res 
    fi
end;

normaldag:=proc(f)
option remember;
  if type(f,{list,`*`,`+`,`^`}) then normal(map(thisproc,f))
  else f
  fi
end:

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
testcert:=proc(telesc,cert,S,vars,point :: list := [])
local n,pointwithoutn,valcert,shiftvalcert,valn;
  n:=op([2,1],S);
  if has(point,n) then
    pointwithoutn,valn:=selectremove(proc(u) op(1,u)<>n end,point)
  else pointwithoutn:=point; valn:=[]
  fi;
  valcert:=EvalCert(cert,S,vars,pointwithoutn);
  shiftvalcert:=EvalCert(subs(D[n+1]=D[n],subs(n=n+1,cert))*D[n],S,vars,pointwithoutn);
  simplify(EvalCert(telesc,S,vars,point)-eval(shiftvalcert-valcert,valn))
end:

### This is way too expensive, as the NormalForm does not
### deal with dags efficiently.
#internal_test_cert:=proc(mon,rat,cert,cyclicvect,mat,nn)
#local gamma,dvars,vv,lcert,deltacert,i;
#  dvars:=[seq(D[vv[2]]=vv[1],vv=map2(op,2,mat:-algebra["type_struct"]))];
#  gamma:=add(cyclicvect[i]*mat:-basis[i],i=1..nops(mat:-basis[i]));
#  lcert:=subs(dvars,cert);
#  lcert:=Ore_algebra['skew_product'](lcert,gamma,mat:-algebra);
#  deltacert:=Ore_algebra['skew_product'](subs(dvars,D[nn]-1),lcert,mat:-algebra);
#  evalb(Groebner['NormalForm'](subs(dvars,mon) - rat*gamma - deltacert,
#      mat:-gbasis,mat:-ordering)=0)
#end:

# Checks that
#   (mon - rat - (D[nn]-1) cert) gamma  (E)
# is in the ideal, by checking it at a random point.
internal_test_cert:=proc(mon,rat,cert,cyclicvect,mat,nn)
local gamma,dvars,vv,deltacert,i,j,p1,p2,lco,lcoval,lmons,zero,vars,rnd,rndpoint,deltagamma;
  vars:=map2(op,2,mat:-algebra["type_struct"]);
  dvars:=[seq(D[vv[2]]=vv[1],vv=vars)];
  # mon
  p1:=Groebner['NormalForm'](subs(dvars,mon),mat:-gbasis,mat:-ordering);
  # rat * gamma
  gamma:=add(cyclicvect[i]*mat:-basis[i],i=1..nops(mat:-basis[i]));

  p2:=rat*gamma;
  # (D[nn] - 1) cert
  deltacert:=subs(dvars,subs(D[nn+1]=D[nn],subs(nn=nn+1,cert))*D[nn]-cert);
  dvars:=map2(op,2,dvars);
  deltacert:=collect(deltacert,dvars,'distributed');
  lco:=[coeffs(deltacert,dvars,'lmons')];lmons:=[lmons];
  # multiplication by gamma on the right
  deltagamma:=map(Ore_algebra['skew_product'],lmons,gamma,mat:-algebra);
  # reduction mod the ideal
  deltagamma:=map(Groebner['NormalForm'],deltagamma,mat:-gbasis,mat:-ordering);
  vars:=map2(op,2,vars);
  rnd:=rand(-1000..1000);
  for i to 5 do 
    rndpoint:=[seq(j=rnd(),j=vars)];
    try lcoval:=eval(lco,rndpoint);
    catch "numeric exception": next
    end try;
    break
  od;
  if i=6 then error "problem with the certificate" fi;
  zero:=eval(p1-p2-add(lcoval[i]*deltagamma[i],i=1..nops(lco)),rndpoint);
  evalb(zero=0)
end:

adjoint_shift:=proc(X,dim,n)
local i;
  map(normal,[seq(subs(n=n-i,X[i+1]),i=0..dim-1)])
end:

# Input: certificate as computed by scalar_red_ct_sum, variable used in the summation
# Output: a square-free polynomial that vanishes at the poles of the certificate wrt var
SingularitiesCertificate:=proc(cert,var)
local res;
   res:=PolynomialTools['SquareFreePart'](singpolmul(args),var);
   if type(res,`*`) then res:=select(has,res,var) fi;
   forget('singpolmul','factpol');
   res
end:

singpolmul:=proc(F,var) option remember;
   if type(F,{name,rational}) then 1
   elif type(F,`+`) then lcm(op(map(thisproc,[op(F)],var)))
   elif type(F,`^`) then
        if op(2,F)>0 then thisproc(op(1,F),var) 
        else factpol(op(1,F),var)
        fi
   elif type(F,`*`) then lcm(op(map(thisproc,select(has,[op(F)],var),var)))
   elif type(F,list) then lcm(op(map(thisproc,F,var)))
   else error "to be completed",F
  fi
end:

factpol:=proc(F,var) option remember;
   if F=var then var
   elif type(F,{name,rational}) then 1
   elif type(F,`*`) then lcm(op(map(thisproc,[op(F)],var)))
   elif not has(F,var) then 1
   elif type(F,`+`) then F
   else error "to be completed", F 
   fi
end:
