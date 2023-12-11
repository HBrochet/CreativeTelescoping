# Copyright (c) 2023, Hadrien Brochet, Bruno Salvy

### InitRed: initialization procedure to execute before reducing rational functions 
###          in n_arg modulo L_arg^*(K(n_arg))
### Input
### - L_arg an operator in S_var, given as an OrePoly
### - n_arg a variable
### - CertBool a boolean coding whether we want to compute the certificate associated to the reduction
InitRed:=proc(L_arg,n_arg,CertBool)
local rec, i;
    rec:=Record(
        'L',            # List of coefficient of the operator in Sn^{-1} w.r.t. which we reduce R
        'var',          # Name of the summation variable
        'RepresDen',    # List of the representative modulo shifts of the irreducible factors encountered so far
        'CertB',        # Boolean, if true the certificate G is computed otherwise it isn't
        'r',            # Order of the operator L 
        'Pr',           # Coefficient of order r of L
        'P0',           # Coefficient of order 0 of L
        'basis',        # Hash table storing a basis of the finite dimensional spaces used in the strong reductions of poles and polynomials, that is []
        'basispol',     # basis of the finite dimensional spaces used in the strong reductions of polynomials
        'sigm',         # Variable used in the indicial equation at infinity: L(n^s)= C(s)(n^{s+sigm} + o(1))
        's',            # variable for the indicial polynomials
        'C',            # See the line above
        'Croot'        # List of non-negative integer roots of C 
    );
    rec:-var:=n_arg; # variable associated to Sn
    rec:-r:=nops(L_arg)-1;  # order of the operator L
    # adjoint operator: the coefficients of powers of S_n^{-1).
    rec:-L:=map(normal,[seq(eval(op(i,L_arg),rec:-var=rec:-var-i+1),i=1..rec:-r+1)]);
    rec:-RepresDen:={}; # set of representatives of the denominators reduced so far 
    rec:-CertB:=CertBool;
    rec:-P0:=rec:-L[1]; # constant coefficient of L
    rec:-Pr:=rec:-L[rec:-r+1]; # leading coefficient of L
    ### compute the degree sigm and the leading coeff C of L(var^s)
    rec:-sigm, rec:-C, rec:-Croot:=IndEqInfty(rec);
    ComputeBasis(rec);
    rec;
end:

# Input is a pfrac in _Pfrac and _Shift,
# collected in _Pfrac
Reduction:=proc(R,rec)
local inds,i,canform, cert, certpol, pol, polpart, ratpart;
    inds:=indets(R,specindex(anything,_Pfrac));
    for pol in inds do
        polpart[pol],ratpart[pol],cert[pol]:=
            LocalReduction(op(pol),add(coeff(R,pol,i)*pol^i,i=1..degree(R,pol)),rec)
    end do;
    polpart:=subs([seq(pol=0,pol=inds)],R)+add(polpart[pol],pol=inds);
    polpart,certpol:=ReductionPolynomial(polpart,rec);
    canform,cert:=
        polpart+add(ratpart[pol],pol=inds),
        certpol+add(cert[pol],pol=inds);
    if rec:-CertB then ASSERT(TestCanonicalForm(R,canform,cert,rec)) fi;
    canform,cert
end:


ReductionPolynomial:=proc(R,rec)
local var:=rec:-var,pol,cert,i,deg,precert,C, c, co, degi, sigm, copol,j;
    pol:=primpart(R,var,'copol');
    if pol=0 then return 0,0 fi;
    sigm:=rec:-sigm;
    C:=rec:-C;
    cert:=0;
    # weak reduction
    for deg from degree(pol,var) by -1 to 0 do
        if deg>=sigm and not member(deg-sigm,rec:-Croot) then 
            co:=coeff(pol,var,deg);
            if co<>0 then
                precert:=var^(deg-sigm)/expand(subs(rec:-s=deg-sigm,C));
                # Subtract rec:-L(cert)
                pol:=collect(pol-co*evalL(precert,rec),var,normal);
                if rec:-CertB then cert += copol*co*precert fi
            fi
        fi
    end do;
    # strong reduction
#   rec:-basispol is a list of [pol,cert], 
#   sorted by decreasing degree of pol
    if assigned(rec:-basispol) then
        for i to nops(rec:-basispol) do
            degi :=degree(rec:-basispol[i][1],var);
            c:=normal(coeff(pol,var,degi)/lcoeff(rec:-basispol[i][1],var));
            if c<>0 then 
#                pol:=collect(pol -c*rec:-basispol[i][1],var,normal);
                pol:=add(coeff(pol,var,j)*var^j,j=degi+1..degree(pol,var))
                    +add(normal(coeff(pol,var,j)-c*coeff(rec:-basispol[i][1],var,j))*var^j,j=0..degi-1);
                if rec:-CertB then cert += c*copol*rec:-basispol[i][2] fi
            fi
        od
    fi;
    pol:=collect(pol*copol,var,normal);
    if rec:-CertB then ASSERT(TestCanonicalForm(R,pol,cert,rec)) fi;
    pol,cert
end:

# Reduce the part with denominators that are shifted versions of pol
LocalReduction:=proc(pol,ratfun,rec)
local polpart,rat,cert,cert2, polpart2, rat2;
    polpart,rat,cert:=WeakReduction(args);
    if rat<>0 then # strong reduction
        polpart2,rat2,cert2:=StrongReduction(pol,rat,rec);
        polpart += polpart2; 
        rat := rat2;
        if rec:-CertB then cert += cert2 fi
    fi;
    if rec:-CertB then ASSERT(TestCanonicalForm(ratfun,polpart+rat,cert,rec)) fi;
    polpart,rat,cert
end:

## This follows the algorithm in section 4.2, with computation of A(n) or A'(n+r)
# s.t. L*(A/pol(n-shift)^sj) removes the pole in pol(n-shift).
# The complexity may be dominated by the extended gcd.
# If this is the case (to be analyzed),
# then it could be more efficient to compute and store the 
# L*(n^ell/pol(n-shift)^sj) for ell=0..sj*deg pol -1,
# and then perform a simple Gaussian reduction.
WeakReduction:=proc(pol,ratfun,rec)
local rat,polpart:=0,var,cert:=0,r:=rec:-r,OrdMult, den,  inds, cop,
      denprecert, lambda, mon, numprecert, ptilde, shift, shiftpol, sj, tmp1,
      shiftpow,newpolpart,corat,colambda;
    var:=rec:-var;
    inds:=[_Pfrac[pol],_Shift];
    rat:=primpart(ratfun,[op(inds),var],'corat');
    do # weak reduction
        newpolpart,rat:=ExtractPolynomialPart(pol,rat,rec);
        polpart += newpolpart;
        shift:=ldegree(rat,_Shift);
        if shift>=0 then
            shift:=degree(rat,_Shift);
            if shift<rec:-r then break fi
        fi;
        mon:=coeff(rat,_Shift,shift);
        # Computation of A & B from Eq. (22) in the article
        den:=translate(pol,var,-shift);
        if shift<0 then OrdMult:=0; tmp1:=rec:-P0; shiftpow:=0
        else OrdMult:=valpol2(rec:-Pr,den,var,'tmp1');shiftpow:=-r
        fi;
        sj:=degree(mon,_Pfrac[pol]);
        lambda:=lcoeff(mon,_Pfrac[pol]);
        lambda:=primpart(lambda,var,'colambda');
        shiftpol:=den^sj;
        ptilde:=rem(tmp1,shiftpol,var);
        ptilde:=primpart(ptilde,var,'cop');
        gcdex(ptilde,shiftpol,var,'numprecert'); # numprecert = A
        numprecert:=rem(numprecert*lambda,shiftpol,var);
        denprecert:=den^(sj+OrdMult);
        if shift>=0 then
            numprecert:=translate(numprecert,var,r);
            denprecert:=translate(denprecert,var,r)
        fi;
        if rec:-CertB then 
            cert += numprecert/denprecert*corat*colambda/cop
        fi;
        # Subtract rec:-L(cert)
        rat:=collect(rat-evalL(normal(colambda/cop*numprecert)*_Pfrac[pol]^(sj+OrdMult)*_Shift^(shift+shiftpow),rec),inds,normal)
    od;
    polpart:=collect(polpart*corat,var,normal);
    rat:=collect(corat*rat,inds,normal);
    if rec:-CertB then ASSERT(TestCanonicalForm(ratfun,polpart+rat,cert,rec)) fi;
    polpart,rat,cert
end:

StrongReduction:=proc(pol,ratfun,rec)
local var,basis,res,i,degshift,co,cobasis,degcobasis,degco,coco,degcobasisvar,cococo,lincomb,cert,polpart;
    cert:=0;
    if not assigned(rec:-basis[pol]) then return 0,ratfun,0 fi;
    var:=rec:-var;
    basis:=rec:-basis[pol];
    res:=ratfun;
    for i to nops(basis) do
        res:=expand(res);
        pol:=basis[i][1];
        degshift:=degree(pol,_Shift);
        co:=coeff(res,_Shift,degshift);
        if co<>0 then
            cobasis:=coeff(pol,_Shift,degshift);
            degcobasis:=degree(cobasis,_Pfrac[pol]);
            degco:=degree(co,_Pfrac[pol]);
            if degcobasis<=degco then
                coco:=coeff(co,_Pfrac[pol],degco);
                cobasis:=cobasis*translate(pol,var,-degshift)^(degco-degcobasis);
                degcobasisvar:=degree(cobasis,var);
                cococo:=coeff(coco,degcobasisvar);
                if cococo<>0 then 
                    lincomb:=cococo/coeff(cobasis,var,degcobasisvar);
                    res:=res-expand(lincomb*basis[i][1]);
                    if rec:-CertB then cert += lincomb*rec:-basis[pol][i][2] fi
                fi
            fi
        fi
    end do;
    polpart:=subs(_Pfrac[pol]=0,res); res:=res-polpart;
    if rec:-CertB then ASSERT(TestCanonicalForm(ratfun,polpart+res,cert,rec)) fi;
    polpart,res,cert
end:

# Split the rational function ratfun into 
# a polynomial part and a part that has poles at pol,
# with numerators of smaller degree than their denominators.
ExtractPolynomialPart:=proc(pol,ratfun,rec)
local i, ld, deg, var:=rec:-var, co, mon, poly;
    ld:=ldegree(ratfun,_Shift);
    deg:=degree(ratfun,_Shift);
    for i from ld to deg do
        co:=coeff(ratfun,_Shift,i); # polynomial in _Pfrac[pol]
        poly[i],mon[i]:=NormalizePfracElement(pol,co,i,var); # poly+lambda*_Pfrac[pol]^expo
    end do;
    ASSERT(normal(CanonicalFormToRat(ratfun-add(poly[i],i=ld..deg)-add(mon[i]*_Shift^i,i=ld..deg),rec))=0);
    collect(add(poly[i],i=ld..deg),rec:-var,normal),add(mon[i]*_Shift^i,i=ld..deg)
end:

# Input: a polynomial shiftedpart in _Pfrac[pol] 
# Output: polynomial and a monomial co(var)*_Pfrac[pol]^expo
#   such that subs(var=var-shift,shiftedpart) == 
#       polynomial + co(var)*_Pfrac[pol]^expo 
#   and degree(co)<expo*degree(pol)
#   and gcd(co,pol(var-shift))=1.
# This corresponds to normalizing the partial fraction element.
NormalizePfracElement:=proc(pol,shiftedpart,shift,var)
local deg,ldeg,shiftedpol,expo,i,newpol,polpart,pvar,co;
    pvar:=_Pfrac[pol];
    if not has(shiftedpart,pvar) then return shiftedpart,0 fi;
    deg:=degree(shiftedpart,pvar);
    ldeg:=ldegree(shiftedpart,pvar);
    shiftedpol:=translate(pol,var,-shift);
    newpol:=(add(coeff(shiftedpart,pvar,i)*shiftedpol^(deg-i),i=ldeg..deg));
    newpol:=primpart(newpol,var,'co');
    polpart:=quo(newpol,shiftedpol^deg,var,'newpol');
    expo:=valpol2(newpol,shiftedpol,var,'newpol');
    collect(co*polpart,var),normal(co*newpol)*pvar^(deg-expo) # is normal useful?
end:

#ComputeBasis
#Input:
#   rec: record as constructed by InitRed
#No Output: It computes bases of the finite dimensional spaces at each singularity.
#           These are used in the strong reductions of poles and polynomials,
#           that is [L(K_Q(rec:-var))]_Q for Q in rec:-RepresDen.
#           For polynomials, the situation is more complicated, as the space to be
#           considered contains not only L(K[rec:-var]) but also the polynomials
#           obtained when reducing the fractions at the poles in rec:-RepresDen. In
#           the end, this means considering
#           [L(K[rec:-var]) +  sum_{pol\in rec:-represDen} [L(K_pol(rec:-var))]_pol\inter K[rec:-var]]_\infty
#           with the notations of our paper.

ComputeBasis:=proc(rec)
local DecP0,DecPr,pol,l,CurRepres,repres,r,P0,Pr,var;

    r:=rec:-r;
    P0:=rec:-P0;
    
    Pr:=rec:-Pr;
    var:=rec:-var;

    DecP0,CurRepres:=MyShiftlessDecFact(rec:-P0,rec);
    repres:={op(CurRepres)};
    DecPr,CurRepres:=MyShiftlessDecFact(rec:-Pr,rec);
    repres:=repres union {op(CurRepres)};
    for pol in repres do 
        if not(type(DecP0[pol],indexed)) then 
            DecP0[pol]:=select(
                l-> evalb(op(1,l)<0 and op(2,l)<=valpol2(P0,eval(pol,var=var-op(1,l)),rec:-var)), 
                DecP0[pol]); 
        else DecP0[pol]:=[] fi;
        if not(type(DecPr[pol],indexed))  then 
            DecPr[pol]:=[seq([l[1]-r,l[2]],l = DecPr[pol])];
            DecPr[pol]:=select(
                l-> evalb(op(1,l)>=0 and op(2,l) <= valpol2(Pr,eval(pol,var=var-op(1,l)-r),rec:-var)),
                DecPr[pol]);
        else DecPr[pol]:=[] fi;
        ComputeBasisSR(pol,DecP0[pol],DecPr[pol],rec)
    od;
    rec:-RepresDen:=repres;
    ComputeBasisSRP(rec)
end:

#ComputeBasisSR
# Input:
#   pol: a polynomial in the list rec:-RepresDen
#   indeltsP0: list of couples (s,o') where s is a shift and o' an order
#              s.t. for o<=o' and ell<o*deg Q, L(n^ell/Q(n-s)^o)
#               might not reduce to 0 by the weak reduction
#               because of a singularity in P0
#   indeltsPr: same as above with Pr in place of P0
#   rec: record as constructed by InitRed
# No Output. Instead the results are stored in rec:-basis[pol] 
#    as a list of [rat,cert] where
#    . rat is a polynomial where
#       _Pfrac[pol]^s*_Shift^i encodes 1/pol(var-i)^s
#    . the rat form a basis of the finite dimensional
#       [L(K_pol(rec:-var))]_pol
#    . cert is a certificate associated to rat

ComputeBasisSR:=proc(pol,indeltsP0,indeltsPr,rec)
local degP,m,s,couple,i,j,ord,l,indelt,var,canform,cert,ratfrac,tored,polpart;

    m:=add(op(2,l),l in indeltsP0) + add(op(2,l), l in indeltsPr);
    if m=0 then return fi;
    var := rec:-var;
    degP:=degree(pol,var);
    indelt:=[op(indeltsP0),op(indeltsPr)];
    s:=0;
    for couple in indelt do
        i,ord:=op(couple);
        for j from 1 to ord do
            for l from 0 to degP-1 do 
                ### initialise with L(var^l/pol(var-i)^j)
                tored:=evalL(var^l*_Pfrac[pol]^j*_Shift^i,rec);
                polpart,canform,cert[s+1]:=WeakReduction(pol,tored,rec);
                canform:=polpart+canform;
                if canform=0 then next fi;
                s:=s+1;
                ratfrac[s]:=canform;
                if rec:-CertB then cert[s] := -cert[s]+var^l/subs(var=var-i,pol)^j fi;
            od
        od
    od;
    if s<>0 then
        rec:-basis[pol]:=RowEchelonForm([seq(ratfrac[i],i=1..s)],[seq(cert[i],i=1..s)],pol,rec)
    fi
end;

#ComputeBasisSRP
# Input:
#   rec: record as constructed by InitRed
# No Output: It computes an echelon basis of the finite dimensional space
#           [L(K[rec:-var]) +  sum_{pol\in rec:-represDen} [L(K_pol(rec:-var))]_pol\inter K[rec:-var]]_\infty
#   The elements of the basis are monic.
ComputeBasisSRP:=proc(rec)
local i,pol,s,var,M,j,canform,cert,deg,lincomb,listpols,co;
    var := rec:-var;
    s:=0;
    ### roots of the indicial polynomial at infinity
    for i in rec:-Croot do
        s:=s+1;
        canform[s],cert[s]:=Reduction(evalL(var^i,rec),rec)
    od;
    ### polynomial relations from singularities
    for pol in rec:-RepresDen do
        if type(rec:-basis,indexed) or not assigned(rec:-basis[pol]) then next fi;
        M:=rec:-basis[pol];
        for i to nops(M) while has(M[i][1],_Pvar) do od;
        if i=nops(M)+1 then next fi;
        for j from i to nops(M) do
            s:=s+1;
            canform[s],cert[s]:=op(rec:-basis[pol][j])
        end do;
        rec:-basis[pol]:=rec:-basis[pol][1..i-1];
        if rec:-basis[pol]=[] then unassign('rec:-basis[pol]'); next fi;
    od;
    if s=0 then return fi;
    deg:=max(map(degree,[seq(canform[i],i=1..s)],var));
    M:=Matrix(s,deg+1,(i,j)->coeff(canform[i],var,deg-j+1));
    M:=<M|LinearAlgebra['IdentityMatrix'](s)>;
    M:=LinearAlgebra['GaussianElimination'](M);
    lincomb:=M[1..s,-s..-1];
    listpols:=[seq(add(M[i,j]*var^(deg-j+1),j=1..deg+1),i=1..s)];
    if rec:-CertB then
        cert:=convert(lincomb . Vector([seq(cert[i],i=1..s)]),list)
    fi;    
    for s from s by -1 while listpols[s]=0 do od;
    ## New variant where we avoid that normalization
    #for i to s do 
    #    co:=lcoeff(listpols[i],var);
    #    listpols[i]:=collect(listpols[i]/co,var,normal);
    #    if rec:-CertB then cert[i]:=cert[i]/co fi
    #od;
    ## Still, we make them primitive.
    for i to s do
        listpols[i]:=primpart(listpols[i],var,'co');
        if rec:-CertB then cert[i]:=cert[i]/co fi
    end do;
    # Do *not* try to put the basis in strong echelon form.
    # It tends to make the reductions more costly, as the 
    # strong echelon form has actually larger "length".
    if rec:-CertB then
        for i to s do
            ASSERT(normal(listpols[i]-evalLcert(cert[i],rec))=0)
        od
    fi;
    rec:-basispol:=[seq([listpols[i],cert[i]],i=1..s)]
end:

#MyShiftlessDecFact
# Input:
#   P: a univariate polynomial in rec:-var
#   rec: record as constructed by InitRed
# Output:
#   Pdec: a table containing the shiftless decomposition of P 
#         (see ?PolynomialTools[ShiftlessDecomposition] for a definition)
#       Pdec[pol] is a list of pairs [shift,exponent] for pol in CurRepres
#   CurRepres: a list of representatives of the factors of Pdec modulo the shifts
MyShiftlessDecFact:=proc(P,rec)
local pol,Pdec,Pvar,i,shiftpol,factP,ord,l,var,P0,Pr,CurRepres;
local j,toremove,listint, _;

    var:=rec:-var;
    P0:= rec:-P0;
    Pr:=rec:-Pr;
    Pvar:=P;
    CurRepres:=[];

    ### check whether P has a factor in RepresDen. If so, begin to compute the decomposition
    for pol in rec:-RepresDen do
        listint:=RootDifferInt(Pvar,pol,var);
        if listint=[] then next fi;
        CurRepres:=[op(CurRepres),pol];
        Pdec[pol]:=[];
        for i in listint do
            shiftpol:=translate(pol,var,i);
            ord:=valpol2(Pvar,shiftpol,rec:-var,'Pvar');
            Pdec[pol]:=[op(Pdec[pol]),[-i,ord]]
        od;
    od;
    if has(Pvar,var) then
        userinfo(5,'red',"starting factorisation at", time());
        _,factP:=op(factors(Pvar));
        userinfo(5,'red',"factorization done at", time());
        # remove the factors that do not depend on var
        factP:=select(has,factP,var)
    else factP:=[]
    fi;

    while factP<>[] do
        pol:=primpart(factP[1,1],var);

        # add pol to RepresDen
        l:=min(RootDifferInt(pol,P0,var));
        if l=infinity then l:=max(RootDifferInt(pol,Pr,var)) fi;
        if l=-infinity then l:=0;
        else pol:=translate(pol,var,-l)
        fi;
        rec:-RepresDen:=rec:-RepresDen union {pol}; 
        CurRepres:=[op(CurRepres),pol];

        Pdec[pol]:=[[-l,factP[1,2]]];

        toremove:= [1]; # list of indices of elements of factP that are processed during this loop

        for j from 2 to nops(factP) do
            if degree(pol,var)=degree(factP[j,1],var) then
                for i in RootDifferInt(pol,factP[j,1],var) do
                    # test if fact[j,1] is of the form pol(n+i)
                    if expand(pol-translate(factP[j,1],var,-i-l))=0 then
                        Pdec[pol]:=[op(Pdec[pol]),[-i-l,factP[j,2]]];
                        toremove:=[op(toremove),j];
                        break
                    fi
                od
            fi
        od;
        factP:=subsop(seq(j=NULL,j=toremove),factP);
    od;
    Pdec,CurRepres
end proc;

rnd:=proc()
local t,rnd;
    rnd:=rand(-1000..1000);
    do
        t:=rnd();
        if t<>0 then return t fi
    od 
end;

# ShiftlessDecIrred
# Input: 
#   R:  a rational function in n
#   rec: record as constructed by InitRed
# Output: The partial fraction decomposition of R
#     The decomposition is stored in the form
#       R = P + sum_i sum_j P_ij*_Shift^j*_Pfrac[Q_i(n)]^r_ij 
#     with the Q_i shift-coprime, that is gcd(Q_i(n+k),Q_j(n))=1 for all k.
#     This represents
#       P + sum_i sum_j P_ij/(Q_i(n)-j)^r_ij.
#     The polynomials Q_i belong to rec:-Repres.
#     
ShiftlessDecIrred:=proc(R,rec)
local pol,i,shiftpol,shiftpol_,ord,A,newnum,tmp2,pfrac;
local Q,var,co,CurRepres,Qdec,ff,polpart;

    var:=rec:-var;

    Q:=denom(R);
    if type(Q,`*`) then Q,co:=selectremove(has,Q,var) 
    elif not has(Q,var) then co:=Q; Q:=1
    else co:=1
    fi;

    newnum:=numer(R);
    ### compute the polynomial part of R
    polpart:=quo(newnum,Q,var,'newnum')/co;
    # no non-polymial part
    if Q=1 then polpart fi;

    Qdec,CurRepres:=MyShiftlessDecFact(Q,rec);
    # Qdec[pol] is a list of pairs [shift,exponent] for pol in CurRepres
    for pol in CurRepres do
        for ff in Qdec[pol] do
            i,ord:=op(ff);
            shiftpol_:=translate(pol,var,-i);
            shiftpol:=shiftpol_^ord;
            Q:=quo(Q,shiftpol,var);
            # Bezout relation : Rvar*Q*shiftpol = newnum = A*Q + B*shiftpol 
            gcdex(Q,shiftpol,var,'A'); # 1 = A * Q + V * shiftpol
            tmp2:=rem(newnum,shiftpol,var,'newnum');
            A:=collect(rem(A*tmp2,shiftpol,var),var,normal); # newnum = A * Q + B * shiftpol
            pfrac[pol,ff]:=A/co*_Pfrac[pol]^ord*_Shift^i;
            newnum:=newnum-quo(A*Q,shiftpol,var) # B
        od
    od;
    pfrac:=polpart+add(add(pfrac[pol,ff],ff=Qdec[pol]),pol=CurRepres);
    ASSERT(normal(CanonicalFormToRat(pfrac,rec)-R)=0);
    pfrac
end:

#RootDifferInt
# Input:
#   P,Q two polynomials in var
#   var a variable
# Output: 
#   a list of integers i such that there exists alpha root of P and beta root of Q such that alpha=beta-i
# !!!!! Non-deterministic
RootDifferInt:= proc(P,Q,var)
local i::nothing,inds,rndpoint,PP,QQ,degP,degQ,R;
    if P=0 or Q=0 then error "computing dispersion with 0 polynomial" fi;
    degP:=degree(P,var);degQ:=degree(Q,var);
    if degP=0 or degQ=0 then return [] fi;
    inds:=(indets(P) union indets(Q)) minus {var};
    do
        rndpoint:=[seq(i=rnd()/rnd(),i=inds)];
        PP:=eval(primpart(P,var),rndpoint);
        QQ:=eval(primpart(Q,var),rndpoint);
        if degP<>degree(PP,var) or degQ<>degree(QQ,var) then next fi;
        if length(PP)<=length(QQ) then
            R:=roots(resultant(translate(PP,var,-i),QQ,var),i)
        else
            R:=roots(resultant(PP,translate(QQ,var,i),var),i)
        fi;
        R:=select(type,map2(op,1,R),integer);
        if remove(has,[seq(gcd(translate(P,var,-i),Q),i=R)],var)=[] then return R fi
    od;
end proc;

#IndEqInfty
# Input:
#   rec: record as constructed by InitRed
# Output:
#   an integer m
#   a polynomial C in rec:-s
#   a list of non-negative integer Croot
#   such that L(var^s) = C(s)(n^{s+m} + o(1)) where L,var,s are defined in rec

IndEqInfty:=proc(rec)
local C,Croot,m,p,o,i;
    m:=max(seq(degree(p,rec:-var),p in rec:-L))+1;
    C:=0; #leading term of L(n^s)
    while C= 0 do
        m:=m-1;
        C:=add(add(coeff(rec:-L[o],rec:-var,i)*expand(binomial(rec:-s,i-m))*(-o)^(i-m),i=m..degree(rec:-L[o],rec:-var)),o=1..rec:-r+1);
    od;
    Croot:=RootDifferInt(rec:-s,C,rec:-s);
    Croot:=select(proc(e) type(e,integer) and e>=0 end,Croot);
    m, lcoeff(C,rec:-var), Croot
end;

## Copy-pasted from red.mpl
# return the largest l st Q^l | P
# and store the quotient in co
valpol2:=proc(
    P :: depends(polynom(anything, t)),
    Q :: depends(polynom(anything, t)),
    t :: name, co
              )
local i,q,p,cont,newp;
    p:=P;q:=primpart(Q,t,'cont');
    if normal(P)=0 then return infinity fi;
    if type(p,polynom(rational)) and type(q,polynom(rational)) then
        for i while divide(p,q,'p') do od
    else
        for i do if rem(p,q,t,'newp')=0 then p:=newp else break fi od
    fi;
    if nargs=4 then
        co:=p/cont^(i-1)
    fi;
    i-1
end:

# Input: 
#   u:  sequence given as a polynomial in _Pfrac[] and _Shift
#   rec: record created by InitRed
# Output:
#   add(L[i+1]*u(var-i),i=0..r)
evalL:=proc(u,rec)
local lco,lmon,i,j,polpart,polind;
    lco:=[coeffs(u,[_Shift,op(indets(u,specindex(anything,_Pfrac)))],'lmon')]; lmon:=[lmon];
    if member(1,lmon,'polind') then
        polpart:=add(rec:-L[i+1]*translate(lco[polind],rec:-var,-i),i=0..rec:-r);
        lco:=subsop(polind=NULL,lco);
        lmon:=subsop(polind=NULL,lmon)
    else polpart:=0
    fi;
    polpart+add(add(rec:-L[i+1]*translate(lco[j],rec:-var,-i)*lmon[j]*_Shift^i,i=0..rec:-r),j=1..nops(lco))
end:

#evalL:=proc(u,rec)
#local lco,lmon,i,j,polpart,polind,var,rr,degshift,pol,deg;
#    lco:=[coeffs(u,[_Shift,op(indets(u,specindex(anything,_Pfrac)))],'lmon')]; lmon:=[lmon];
#    var:=rec:-var;
#    if member(1,lmon,'polind') then
#        polpart:=add(rec:-L[i+1]*translate(lco[polind],rec:-var,-i),i=0..rec:-r);
#        lco:=subsop(polind=NULL,lco);
#        lmon:=subsop(polind=NULL,lmon)
#    elif nops(lmon)=1 then # this is what happens during the weak reduction
#        lmon:=op(lmon);lco:=op(lco);
#        degshift:=degree(lmon,_Shift);
#        pol:=op(op(indets(lmon,specindex(anything,_Pfrac))));
#        deg:=degree(lmon,_Pfrac[pol]);
#        for i from 0 to rec:-r do
#            polpart[i]:=quo(rec:-L[i+1]*translate(lco,var,-i),subs(var=var-i-degshift,pol)^deg,var,rr[i])
#        end do;
#        return add(polpart[i],i=0..rec:-r)+add(rr[i]*_Pfrac[pol]^deg*_Shift^(degshift+i),i=0..rec:-r)
#    else polpart:=0
#    fi;
#    polpart+add(add(rec:-L[i+1]*translate(lco[j],var,-i)*lmon[j]*_Shift^i,i=0..rec:-r),j=1..nops(lco))
#end:


evalLcert:=proc(u,rec)
local i;
    add(rec:-L[i+1]*subs(rec:-var=rec:-var-i,u),i=0..rec:-r)
end:

SplitFrac:=proc(u)
local inds,i,polpart,ratpart;
    inds:=indets(u,specindex(_Pfrac));
    polpart:=subs([seq(i=0,i=inds)],u);
    ratpart:=expand(u-polpart);
    polpart,ratpart
end:

# Input:
#   . list of normalized rational fractions (check) in the form 
#       of polynomials in _Shift and _Pfrac[pol]
#   . corresponding list of certificates
#   . polynomial involved in _Pfrac[pol]
#   . rec 
# Output: 
#   list of 3 elements:
#   . basis: an ordered list of rational fractions
#   . cert: corresponding list of certificates
# The elements of basis are stored as polynomials
# with terms c(var)*_Pfrac[pol]^k*_Shift^m
# where deg c < k*deg pol and gcd(c,pol(var-m))=1.
# the list is sorted by decreasing degree in _Shift,
# then decreasing degree in _Pfrac[pol], then in var.
RowEchelonForm:=proc(lrat,lcert,pol,rec)
local s,basis,i,j,u,cert, co, coj, dddu, 
      dddv, ddu, ddv, du, dv, lcu, lcv, lind, llcu, llcv, pvar, var;
    var:=rec:-var;pvar:=_Pfrac[pol];
    basis:=lrat;cert:=lcert;
    s:=nops(lrat);
    for i to s do 
        # 1. find pivot
        lind:=[i];
        u:=basis[i];
        du:=degree(u,_Shift);ddu:=-1;dddu:=-1;
        for j from i+1 to s do
            dv:=degree(basis[j],_Shift);
            if dv=0 then next fi;
            if du>dv then next fi;
            if du<dv then lind:=[j]; u:=basis[j]; du:=dv; ddu:=-1; dddu:=-1; next fi;
            if ddu=-1 then
                lcu:=coeff(u,_Shift,du);
                ddu:=degree(lcu,pvar);
            fi;
            lcv:=coeff(basis[j],_Shift,du);
            ddv:=degree(lcv,pvar);
            if ddu>ddv then next fi;
            if ddu<ddv then lind:=[j]; u:=basis[j]; lcu:=lcv; du:=dv; ddu:=ddv; dddu:=-1; next fi;
            if dddu=-1 then
                llcu:=coeff(lcu,pvar,ddu);
                dddu:=degree(llcu,var)
            fi;
            llcv:=coeff(lcv,pvar,ddu);
            dddv:=degree(llcv,var);
            if dddu>dddv then next fi;
            if dddu<dddv then lind:=[j]; u:=basis[j]; lcu:=lcv; llcu:=llcv; du:=dv; ddu:=ddv; dddu:=dddv; next fi;
            lind:=[op(lind),j]
        end do;
        # 2. swap rows if necessary
        j:=lind[1];
        if i<>j then
            basis[i],basis[j]:=basis[j],basis[i];
            cert[i],cert[j]:=cert[j],cert[i]
        fi;
        if du=0 then break fi; # only polynomials left
        if nops(lind)>1 then
            # 3. pivot rows that require it
            co:=coeff(llcu,var,dddu);
            for j in subsop(1=NULL,lind) do
                coj:=coeff(coeff(coeff(basis[j],_Shift,du),pvar,ddu),var,dddu);
                coj:=normal(coj/co);
#                basis[j]:=expand(basis[j]-coj*basis[i]);
                basis[j]:=collect(basis[j]-coj*basis[i],[_Shift,pvar,var],'distributed',normal);
                if rec:-CertB then cert[j]:=cert[j]-coj*cert[i] fi
            end do
        fi
    od;
    for i to s do 
        basis[i]:=primpart(basis[i],[_Shift,pvar,var],'co');
        if rec:-CertB then cert[i]:=cert[i]/co fi;
    od;
    [seq([basis[i],cert[i]],i=1..s)]
end:

# R = canform + L^*(cert)
TestCanonicalForm:=proc(R,canform,cert,rec)
local i;
    evalb(normal(CanonicalFormToRat(R-canform,rec) - 
        add(rec:-L[i+1]*subs(rec:-var=rec:-var-i,cert),i=0..rec:-r))=0)
end:

