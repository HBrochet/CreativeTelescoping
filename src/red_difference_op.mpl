### InitRed: initialization procedure to execute before reducing rational functions 
###          in n_arg modulo L_arg^*(K(n_arg))
### Input
### - L_arg an operator in S_var, given as an OrePoly
### - n_arg a variable
### - CertBool a boolean coding whether we want to compute the certificate associated to the reduction
InitRed:=proc(L_arg,n_arg,CertBool)
local rec, i;
    rec:=Record(
        'denG',         # Multiple of the denominator of the certificate G currently computed
        'G',            # Current certificate 
        'decR',         # Hash table storing the decomposition of the rational function R,
                        # the ith entry is the element 
        'L',            # List of coefficient of the operator in Sn^{-1} w.r.t. which we reduce R
        'var',          # Name of the summation variable
        'RepresDen',    # List of the representative modulo shifts of the irreducible factors encountered so far
        'CertB',        # Boolean, if true the certificate G is computed otherwise it isn't
        'r',            # Order of the operator L 
        'Pr',           # Coefficient of order r of L
        'P0',           # Coefficient of order 0 of L
        'CurRepres',    # List of the representative modulo shifts of the irreducible factors encountered since the
                        #                                       previous computation of a shiftless decomposition
        'basis',        # Hash table storing a basis of the finite dimentional spaces used in the strong reductions of poles and polynomials, that is []
        'sigm',         # Variable used in the indicial equation at infinity: L(n^s)= C(s)(n^{s+sigm} + o(1))
        's',            # variable for the indicial polynomials
        'C',            # See the line above
        'Croot'         # List of non-negative integer roots of Croot 
    );
    rec:-denG:=1;
    rec:-var:=n_arg; # variable associated to Sn
    rec:-r:=nops(L_arg)-1;  # order of the operator L
    # adjoint operator: the coefficients of powers of S_n^{-1).
    rec:-L:=map(normal,[seq(eval(op(i,L_arg),rec:-var=rec:-var-i+1),i=1..rec:-r+1)]);
    rec:-RepresDen:=[]; # list of representatives of the denominators reduced so far 
    rec:-CertB:=CertBool;
    rec:-P0:=rec:-L[1]; # constant coefficient of L
    rec:-Pr:=rec:-L[rec:-r+1]; # leading coefficient of L
    ### compute the degree sigm and the leading coeff C of L(var^s)
    rec:-sigm, rec:-C, rec:-Croot:=IndEqInfty(rec);
    ComputeBasis(rec);
    rec;
end:

## Reduction
# Input:
#   R:  rational function in rec:-var
#   rec: record as constructed by InitRed
# Output: 
#   the reduction of R mod rec?
#   the certificate G (if rec:-CertB=false returns a vector of 0)
#   a multiple of the denominator of G (if rec:-CertB=false returns 1))
Reduction:=proc(R,rec)
local pol,i,r,var;
    r:=rec:-r;
    rec:-G:=Vector(r); # certificate
    rec:-denG:=1;
    var:=rec:-var;
    unassign('rec:-decR');
    userinfo(3,'red',"decomposing the rational function at time", time());
    MyShiftlessDecIrred(R,rec);
    userinfo(3,'red',"starting the weak reduction at time", time());
    for pol in rec:-CurRepres do weakreduction(pol,rec) od;
    userinfo(3,'red',"starting the strong reduction at time", time());
    for pol in rec:-CurRepres do strongreduction(pol,rec) od;
    userinfo(3,'red',"starting the weak reduction of the polynomial part at time", time());
    rec:-decR[0]:=weakreducpol(rec:-decR[0],rec);
    userinfo(3,'red',"starting the strong reduction of the polynomial part at time", time());
    rec:-decR[0]:=strongreducpol(rec:-decR[0],rec);

    rec:-decR[0] + add(add(rec:-decR[pol][i][1]/eval(pol,var=var-i)^rec:-decR[pol][i][2],i=0..r-1),
        pol in rec:-CurRepres),
        rec:-G,rec:-denG
end proc;

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
    rec:-RepresDen :={};

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
            DecPr[pol]:=[seq([l[1]-r,l[2]],l in DecPr[pol])];
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
#   indeltsP0: list of couple (s,o') where s is a shift and o' an order
#              s.t. for o<o', it may happen that L(1/Q(n-s)^o) does not reduce to 0 by the weak reduction 
#              because of a singularity in P0
#   indeltsPr: same as above with Pr in place of P0
#   rec: record as constructed by InitRed
# No Output. Instead the results are stored in rec:-basis[pol] as a sequence composed of:
#    a matrix containing the basis of the finite dimensional [L(K_pol(rec:-var))]_pol (without the polynomial basis elements)
#    a list of the polynomial basis elements
#    a list of the certificates associated to the polynomial basis elements
#    a list of multiples of the denominators of the associated certificates

ComputeBasisSR:=proc(pol,indeltsP0,indeltsPr,rec)
local degP,m,vectG,vectpol,ExcepEqs,s,couple,i,j,ord,l,shiftpol,o,re,p,num,ordmax,maxi,indelt,q,denGrel,var,r,L,coefnumer,qu;

    var := rec:-var;
    r:= rec:-r;
    L:= rec:-L;

    degP:=degree(pol,var);
    m:=add(op(2,l),l in indeltsP0) + add(op(2,l), l in indeltsPr);
    maxi:=max(add(op(2,l),l in indeltsP0), add(op(2,l), l in indeltsPr));
    ordmax:=max(seq(op(2,l),l in indeltsP0),seq(op(2,l),l in indeltsPr));
    indelt:=[op(indeltsP0),op(indeltsPr)];

    if m=0 then return fi;

    vectG:=Vector(m*degP);
    vectpol:=Vector(m*degP);
    ExcepEqs:=Matrix(1..m*degP,1..(ordmax+maxi)*degP*r+m*degP);
    s:=1;
    for couple in indelt do
        i,ord:=op(couple);
        for j from 1 to ord do
            for l from 0 to degP-1 do 
                ### initialise rec:-decR with L(var^l/pol(var-poles[i])^j)
                if rec:-CertB then rec:-G:=certif_lagrange(var^l/eval(pol,var=var-i)^j,rec) else rec:-G:= 0 fi;
                rec:-decR[0]:=0;
                rec:-decR[pol]["min"]:=i;
                rec:-decR[pol]["max"]:=i+r;
                for o from min(i,0) to max(i+r,r-1) do
                    rec:-decR[pol][o]:=0,0
                od;
                for o from 0 to r do 
                    shiftpol:=eval(pol,var=var-(i+o))^j;
                    re:=rem(L[o+1]*(var-o)^l,shiftpol,var,'qu');
                    rec:-decR[pol][i+o]:= re,j;
                    rec:-decR[0]:=rec:-decR[0]+qu
                od;
                weakreduction(pol,rec);
                ### fill the s line of the matrix ExcepEqs with the coefficients of rec:-decR in the basis var^l/pol(var-i)^(ordmax+maxi)
                for o from 0 to r-1 do 
                    shiftpol:=eval(pol,var=var-o);
                    num:=rec:-decR[pol][o][1];
                    for p from (ordmax+maxi)-1 by -1 to 0 do 
                        num:=quo(num,shiftpol,var,'coefnumer');
                        for q from degP-1 by -1 to 0 do 
                            ExcepEqs[s,o+1+((ordmax+maxi-1-p)*degP)*r]:=coeff(coefnumer,var,q);
                        od;
                    od;
                od;
                vectG[s]:=rec:-G;
                vectpol[s]:=rec:-decR[0];
                unassign('rec:-decR');
                s:=s+1;
            od;
        od;
    od;

    # augmented matrix
    for i from 1 to m*degP do 
        ExcepEqs[i,i+(ordmax+maxi)*degP*r]:=1
    od;

    ExcepEqs:=LinearAlgebra['ReducedRowEchelonForm'](ExcepEqs); 
    vectpol:=LinearAlgebra['Multiply'](LinearAlgebra['SubMatrix'](ExcepEqs,1..m*degP,(ordmax+maxi)*degP*r+1..(ordmax+maxi)*degP*r+m*degP),vectpol);
    vectpol:=map(collect,vectpol,var);
    if rec:-CertB then 
        vectG:= LinearAlgebra['Multiply'](LinearAlgebra['SubMatrix'](ExcepEqs,1..m*degP,(ordmax+maxi)*degP*r+1..(ordmax+maxi)*degP*r+m*degP),vectG);
        denGrel:=Vector(m*degP);
        for i to m*degP do denGrel[i]:=lcm(seq(primpart(denom(vectG[i][j]),var),j=1..r)) od; ## !!! Can be expensive
    fi;
    rec:-basis[pol]:=[LinearAlgebra['SubMatrix'](ExcepEqs,1..m*degP,1..(ordmax+maxi)*degP*r),vectpol,vectG,denGrel]
end;

#addlistSRP
# Input:
#   PolRels: a list of univariate polynomials in rec:-var in echelon form 
#   PolRelsG: a list of their associated certificates
#   PolRelsdenG: a list of multiple of the denominators of the associated certificates
#   npol_: a new polynomial to reduce by the echelon form and eventually add to the list
#   nG_: its certificate
#   Gden_: a multiple of its denominator
#   rec: record as constructed by InitRed
# Output:
#   PolRels: the updated list
#   PolRelsG: the updated list
#   PolRelsdenG: the updated list

addlistSRP:=proc(PolRels,PolRelsG,PolRelsdenG,npol_,nG_,Gden_,rec)
local npol,nG,dnp,resG,i,c,Gden,resGden,var;

    var:=rec:-var;
    npol:=npol_;
    nG:=nG_;
    Gden:=Gden_;
    
    if npol=0 then return PolRels,PolRelsG,PolRelsdenG fi;

    dnp := degree(npol,var);
    resG:=[];
    for i to nops(PolRels) do
        if degree(PolRels[i],var) = dnp then 
            c:= coeff(npol,var,dnp);
            npol:= collect(npol - PolRels[i]*c,var,normal);
            if rec:-CertB then nG:=nG - PolRelsG[i]*c; Gden:=lcm(Gden,primpart(PolRelsdenG[i],var)); fi;
            return addlistSRP(PolRels,PolRelsG,PolRelsdenG,collect(npol,var,normal),nG,Gden,rec);
        fi;
        if degree(PolRels[i],var) > dnp then 
            c:=coeff(npol,var,dnp);
            nG:=nG/c;
            npol:=collect(npol/c,var,normal);
            if rec:-CertB then
                resG:=[op(1..i-1,PolRelsG),nG,op(i..nops(PolRels),PolRelsG)];
                resGden:=[op(1..i-1,PolRelsdenG),Gden,op(i..nops(PolRels),PolRelsdenG)]
            fi;
            return [op(1..i-1,PolRels),npol,op(i..nops(PolRels),PolRels)],resG,resGden;
        fi;
    od;
    c:=coeff(npol,var,dnp);

    npol:=collect(npol/c,var,normal);
    nG:=nG/c;
    return [op(PolRels),npol],[op(PolRelsG),nG],[op(PolRelsdenG),Gden];
end;

#ComputeBasisSRP
# Input:
#   rec: record as constructed by InitRed
# No Output: It computes an echelon basis of the finite dimensional space
#           [L(K[rec:-var]) +  sum_{pol\in rec:-represDen} [L(K_pol(rec:-var))]_pol\inter K[rec:-var]]_\infty

ComputeBasisSRP:=proc(rec);
local PolRels,PolRelsG,i,pol,s,j,cdim,rdim,tmp,PolRelsdenG,Gden,var,L,r;
    var := rec:-var;
    r:= rec:-r;
    L:= rec:-L;

    PolRels:=[];
    PolRelsG:=[];
    PolRelsdenG:=[];

    for i in rec:-Croot do 
        rec:-G:=0;
        tmp:=weakreducpol(add(L[j+1]*(var-j)^i,j=0..r),rec);
        Gden:=1;
        PolRels,PolRelsG,PolRelsdenG:=addlistSRP(PolRels,PolRelsG,PolRelsdenG,tmp,rec:-G,Gden,rec)
    od;

    ### retrieve polynomial relations from basis
    for pol in rec:-RepresDen do
        if type(rec:-basis,indexed) or type(rec:-basis[pol],indexed) then next fi;
        rdim,cdim:=LinearAlgebra['Dimension'](rec:-basis[pol][1]);

        s:=1;
        i:=1;
        while s < rdim+1 do
            while i < cdim+1 and rec:-basis[pol][1][s,i]=0 do
                i:=i+1
            od;
            if i = cdim+1 then break fi;
            s:=s+1;
        od;

        if i = cdim+1 then
            while s< rdim+1 and rec:-basis[pol][2][s]<>0 do 
                PolRels,PolRelsG,PolRelsdenG:=addlistSRP(PolRels,PolRelsG,PolRelsdenG,collect(rec:-basis[pol][2][s],var,normal),rec:-basis[pol][3][s],rec:-basis[pol][4][s],rec);
                s:=s+1;
            od;
        fi;
    od;
    rec:-basis[0]:=PolRels,PolRelsG,PolRelsdenG
end:


# Weak reduction of poles
# Input: 
#   pol: a polynomial in the list rec:-represDen
#   rec: record as constructed by InitRed
# no Output: instead modify the rational function stored in table rec:-decR and being reduced.
#   A weak reduction w.r.t. the polynomial pol is performed.
#   At the end, if the denominator of decR is divisible by some pol(n-i), then i is in [0,r-1].
weakreduction:=proc(pol,rec)
local i,imin,imax,shiftpol,shiftpol_,Rcoeff,ord,j,PolPart,OrdMult,ordj,d,tmp1,var,r,L,P0,Pr,
    numcert,cert,co1,co2,dencert,pt,ptilde,tmp;
    var:=rec:-var;
    r:=rec:-r;
    L:=rec:-L;
    P0:=rec:-P0;
    Pr:=rec:-Pr;

    imin:=rec:-decR[pol]["min"];
    imax:=rec:-decR[pol]["max"];
    userinfo(4,'red',"representative for the weak reduction:",pol,"dispersion:",imax-imin);

    for i in [seq(j,j=imin..-1),seq(imax-j,j=0..imax-r)] do
        shiftpol_:=eval(pol,var=var-i);
        Rcoeff,ord:=rec:-decR[pol][i]; # Rcoeff is the coeff of 1/shiftpol^ord in the PFD of Rvar
        if Rcoeff=0 then next fi;
        # Computation of A & B from Eq. (20) in the paper
        shiftpol:=shiftpol_^ord;
        if i<0 then ptilde:=P0; OrdMult:=0; tmp1:=P0
        else # max integer st pol(var-i) | Pr
            OrdMult:=valpol2(Pr,shiftpol_,rec:-var,'tmp1')
        fi;
        ptilde:=rem(tmp1,shiftpol,var);
        # Compute equation (20)
        # gcdex(ptilde,shiftpol,Rcoeff,var,'numcert','dummy');
        # faster in two steps:
        gcdex(ptilde,shiftpol,var,'numcert');
        numcert:=rem(numcert*Rcoeff,shiftpol,var);
        dencert:=shiftpol_^(ord+OrdMult);
        # Update certificate
        if rec:-CertB then 
            cert:=numcert/dencert;
            if i>=0 then cert:=eval(cert,var=var+r) fi;
            rec:-G:=rec:-G - certif_lagrange(cert,rec)
        fi;
        # Subtract rec:-L(cert)
        for j from 0 to r do 
            if i<0 then pt:=i+j else pt:=i+j-r fi;
            ordj:=rec:-decR[pol][pt][2]; # order of pol(var-pt) in the denom of R
            shiftpol_:=collect(subs(var=var-pt,pol),var);
            if ordj < ord+OrdMult then co1:=shiftpol_^(ord+OrdMult-ordj); co2:=1
            else co1:=1; co2:=shiftpol_^(ordj-ord) fi;
            rec:-decR[pol][pt]:=co1*rec:-decR[pol][pt][1]-co2*L[j+1]*eval(numcert,var=var+i-pt);
            PolPart:=quo(rec:-decR[pol][pt],shiftpol_^max(ord+OrdMult,ordj),var,'tmp');
#if tmp=0 then lprint("= 0",i,pt,j,ordj) fi;
            if PolPart<>0 then rec:-decR[0]:=rec:-decR[0]+PolPart; rec:-decR[pol][pt]:=tmp fi;
            if rec:-decR[pol][pt]=0 then rec:-decR[pol][pt]:=0,0
            else
                d:=valpol2(rec:-decR[pol][pt],shiftpol_,rec:-var,'tmp');
                rec:-decR[pol][pt]:=tmp,max(ord+OrdMult,ordj)-d
            fi
        od
    od
end proc;

# weakreducpol
# Input: 
#   P: a polynomial in rec:-var to be reduced
#   rec: record as constructed by InitRed
# Output:
#   a polynomial reduced by the weak reduction of polynomial 
#   At the end if its coefficient of degree i is non-zero then i is in rec:-Croot of i is smaller than rec:-sigma
weakreducpol:=proc(P,rec)
	local Pvar, Pnosimpl, tmp1, tmp2,j,var,r,L,sigm,C;

    var:=rec:-var;
    r:=rec:-r;
    L:=rec:-L;
    sigm:=rec:-sigm;
    C:=rec:-C;

    Pvar:=collect(P,var,normal);
    Pnosimpl:=0; # polynomial part that cannot be reduced by the weak reduction

	while degree(Pvar,var)>=sigm do
        if not(degree(Pvar,var) in rec:-Croot) then
            tmp1,tmp2:=lcoeff(Pvar,var),degree(Pvar,var);
            Pvar:=collect(Pvar-tmp1*add(L[j+1]*eval(var^(tmp2-sigm)/eval(C,rec:-s=tmp2-sigm),var=var-j),j=0..r),var,normal);
            if rec:-CertB then rec:-G:= rec:-G - certif_lagrange(tmp1*var^(tmp2-sigm)/eval(C,rec:-s=tmp2-sigm),rec) fi;
        else
            tmp1:=lcoeff(Pvar,var)*var^degree(Pvar,var);
            Pnosimpl:=Pnosimpl+tmp1;
            Pvar:=collect(Pvar-tmp1,var,normal);
        fi;
    od;
    Pvar+Pnosimpl;
end proc;

#strongreduction
# Input:
#   pol: a polynomial in the list rec:-represDen
#   rec: record as constructed by InitRed
# no Output: instead modify the rational function stored in table rec:-decR being reduced.
#   the string reduction w.r.t. pol is performed. That is it reduces rec:-decR 
#   with the echelon basis of [L(K_pol(rec:-var))]_pol computed by ComputeBasisSR and stored in rec

strongreduction:=proc(pol,rec)
local rdim,cdim,degP,s,i,o,ord,k,coeffR,j,shiftpol,var,r,l;

    var:=rec:-var;
    r:=rec:-r;

    if type(rec:-basis[pol],indexed) then return fi;
    rdim,cdim:=LinearAlgebra['Dimension'](rec:-basis[pol][1]);
    degP:=degree(pol,var);
    s:=1;
    i:=1;
    while s < rdim+1 do
        while i < cdim+1 and rec:-basis[pol][1][s,i]=0 do
            i:=i+1
        od;
        if i = cdim+1 then break fi;

        o:=irem(i,r,'ord'); 
        ord:=irem(ord,degP,'l'); # basis[pol][1][s,i] contains the coeff of n^l/pol(n-o)^ord
        k:=rec:-decR[pol][o][2];
        if k>=ord then
            shiftpol:=eval(pol,rec:-var=rec:-var-o);
            coeffR:=quo(rec:-decR[pol][o][1],shiftpol^(k-ord),var);
            if coeffR<>0 then 
                 # use row s to reduce
                for j from i to cdim do 
                    o:=irem(i,r,'ord'); 
                    ord:=irem(ord,r,'l'); # basis[pol][1][s,j] contains the coeff of n^l/pol(n-o)^ord
                    shiftpol:=eval(pol,rec:-var=rec:-var-o);
                    rec:-decR[pol][o]:=normal(rec:-decR[pol][o][1]-coeffR*rec:-basis[pol][1][s,j]*rec:-var^l/shiftpol^ord);
                    rec:-decR[pol][o]:=rec:-decR[pol][o],valpol2(rec:-decR[pol][o],shiftpol,rec:-var);
                od;
                if rec:-CertB then
                    rec:-G:=rec:-G-coeffR*rec:-basis[pol][3][s];
                    rec:-denG:=lcm(rec:-denG,primpart(rec:-basis[pol][4][s],var))
                fi;
            fi;
        fi;
        s:=s+1;   
    od;
end;

#strongreducpol
# Input:
#   P: a univariate polynomial in rec:-var to be reduced 
#   rec: record as constructed by InitRed
# Output: 
#   the reduction of P by the echelon basis of
#   [L(K[rec:-var]) +  sum_{pol\in rec:-represDen} [L(K_pol(rec:-var))]_pol\inter K[rec:-var]]_\infty
#   computed in ComputeBasisSRP

strongreducpol:=proc(P,rec)
local Pvar,i,degi,c,var;
    var:=rec:-var;
    Pvar:=P;
    for i from nops(rec:-basis[0][1]) by -1 to 1 do 
        degi :=degree(rec:-basis[0][1][i],var);
        c:=coeff(Pvar,var,degi);
        if c<>0 then 
            Pvar:=collect(Pvar - c*rec:-basis[0][1][i],var,normal);
            if rec:-CertB then rec:-G:=rec:-G-c*rec:-basis[0][2][i]; rec:-denG:=lcm(rec:-denG,primpart(rec:-basis[0][3][i],var)) fi;
        fi;
    od;
    Pvar;
end;

#MyShiftlessDecFact
# Input:
#   P: a univariate polynomial in rec:-var
#   rec: record as constructed by InitRed
# Output:
#   Pdec: a table containing the shiftless decomposition of P 
#         (see ?PolynomialTools[ShiftlessDecomposition] for a definition)
#   CurRepres: a list of representatives of the factors of Pdec modulo the shifts

MyShiftlessDecFact:=proc(P,rec)
local pol,Pdec,Pvar,i,shiftpol,factP,ord,l,var,P0,Pr,CurRepres;
local j,IntDiffer,toremove,listint, _;

    var:=rec:-var;
    P0:= rec:-P0;
    Pr:=rec:-Pr;
    Pvar:=P;
    CurRepres:=[];

    ### check whether P has a factor in RepresDen. If so, begin to compute the decomposition
    for pol in rec:-RepresDen do
        listint:=RootDifferInt(P,pol,var);
        if listint=[] then next fi;
        CurRepres:=[op(CurRepres),pol];
        Pdec[pol]:=[];
        for i in listint do
            shiftpol:=eval(pol,var=var+i);
            ord:=valpol2(Pvar,shiftpol,rec:-var,'Pvar');
            Pdec[pol]:=[op(Pdec[pol]),[-i,ord]]
        od;
    od;    
    userinfo(5,'red',"starting factorisation at", time());
    _,factP:=op(factors(Pvar));
    userinfo(5,'red',"factorization done at", time());
    # remove the factors that don't depend on n
    toremove:= [];
    for i to nops(factP) do
        if degree(factP[i,1],var)=0 then
            toremove:=[op(toremove),i]
        fi;
    od;
    toremove:=seq( `if` (i in toremove, NULL,i), i=1..nops(factP)); # compute the mirror of the list, ie the indices of factP to keep
    factP:=factP[[toremove]]; # update factP
    IntDiffer:=RootDifferInt(P,P,var);

    while not(factP=[]) do
        pol:=factP[1,1];

        # add pol to RepresDen
        l:=min(RootDifferInt(pol,P0,var));
        if l=infinity then l:=max(RootDifferInt(pol,Pr,var)) fi;
        if l=-infinity then l:=0;
        else pol:=eval(pol,var=var-l);  fi;
        rec:-RepresDen:=rec:-RepresDen union {pol}; 
        CurRepres:=[op(CurRepres),pol];

        Pdec[pol]:=[[-l,factP[1,2]]];

        toremove:= [1]; # list of indices of elements of factP that are processed during this loop

        for j from 2 to nops(factP) do
            for i in IntDiffer do
                # test if fact[j,1] is of the form pol(n+i)
                if expand(pol-eval(factP[j,1],var=var-i-l))=0 then
                    Pdec[pol]:=[op(Pdec[pol]),[-i-l,factP[j,2]]];
                    toremove:=[op(toremove),j];
                    break
                fi;
            od;
        od;
        toremove:=seq( `if` (i in toremove, NULL,i), i=1..nops(factP)); # compute the mirror of the list, ie the indices of factP to keep
        factP:=factP[[toremove]] # update factP
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

# MyShiftlessDecIrred
# Input: 
#   R:  a rational function in n
#   rec: record as constructed by InitRed
# no Output: instead store the partial fraction decomposition of R computed in the table rec:-decR.
#     The decomposition is R = P + sum_i sum_j P_ij/Q_i(n-j)^r_ij with the Q_i shift-coprime, that is gcd(Q_i(n+k),Q_j(n))=1 for all k
#     It is stored in a hash table rec:-decR, where P is stored in rec:-decR[0] and P_ij,r_ij are stored in rec:-decR[Q_i][j]

MyShiftlessDecIrred:=proc(R,rec)
local pol,Rvar,i,shiftpol,factQ,ord,l,tmp2,AAAAA,AAAA;
local j,IntDiffer,toremove,listint,Q,_,var,P0,Pr,r;

    var:=rec:-var;
    P0:= rec:-P0;
    Pr:=rec:-Pr;
    r:=rec:-r;

#    Q:=primpart(denom(R),var,'co');
    Q:=denom(R);
    rec:-CurRepres:=[];

    ### compute the polynomial part of R
    rec:-decR[0]:=quo(numer(R),Q,var);
    Rvar:=normal(R-rec:-decR[0]);
    ### check if Q has a factor in RepresDen and if so, begin to compute its decomposition
    for pol in rec:-RepresDen do
        listint:=RootDifferInt(Q,pol,var);
        if listint=[] then next fi;
        rec:-CurRepres:=[op(rec:-CurRepres),pol];
        rec:-decR[pol]["min"]:=infinity;
        rec:-decR[pol]["max"]:=-infinity;

        for i in listint do
            shiftpol:=collect(eval(pol,var=var+i),var,normal);
            ord:=valpol2(Q,shiftpol,rec:-var,'Q'); # denom(Rvar)=shiftpol*Q
            shiftpol:=shiftpol^ord;
            # Bezout relation : Rvar=A*Q + B*shiftpol 
            tmp2:=normal(Rvar*Q*shiftpol);
            tmp2:=rem(tmp2,shiftpol,var);
            gcdex(Q,shiftpol,var,'AAAAA'); 
            AAAA:=rem(AAAAA*tmp2,shiftpol,var);
            rec:-decR[pol][-i]:=AAAA,ord; 
            Rvar:=normal(Rvar-rec:-decR[pol][-i][1]/shiftpol);
            rec:-decR[pol]["min"]:=min(rec:-decR[pol]["min"],-i);
            rec:-decR[pol]["max"]:=max(rec:-decR[pol]["max"],-i);
        od;
    od;  
    for pol in rec:-CurRepres do 
        for i from min(rec:-decR[pol]["min"],0) to max(rec:-decR[pol]["max"],r-1) do
            if type(rec:-decR[pol][i][1],indexed) then 
                rec:-decR[pol][i]:=0,0
            fi;
        od;
    od;
    userinfo(5,'red',"starting factorisation at", time());
    _,factQ:=op(factors(Q));
    userinfo(5,'red',"factorisation done at", time());
    #remove the factors that don't depend on n 
    toremove:= [];
    for i to nops(factQ) do
        if degree(factQ[i,1],var)=0 then
            toremove:=[op(toremove),i]
        fi;
    od;
    toremove:=seq( `if` (i in toremove, NULL,i), i=1..nops(factQ)); # compute the mirror of the list, ie the indices of factQ to keep
    factQ:=factQ[[toremove]]; # update factQ

    IntDiffer:=RootDifferInt(Q,Q,var);
    while not(factQ=[]) do
        pol:=factQ[1,1];
        Q:=normal(Q/pol^factQ[1,2]);
        gcdex(Q,pol^factQ[1,2],normal(Rvar*Q*pol^factQ[1,2]),var,'AAAAA','BBBBB'); # Bezout relation : P=A*Q/F^r_0 + B*F^r_0

        # add pol to RepresDen
        l:=min(RootDifferInt(pol,P0,var));
        if l=infinity then l:=max(RootDifferInt(pol,Pr,var)) fi;
        if l= -infinity then l:=0;
        else pol:=eval(pol,var=var-l) fi;
        rec:-RepresDen:=[op(rec:-RepresDen),pol]; 
        rec:-CurRepres:=[op(rec:-CurRepres),pol];
        rec:-decR[pol]["min"]:=-l;
        rec:-decR[pol]["max"]:=-l;

        rec:-decR[pol][-l]:=AAAAA,factQ[1,2]; # add P_0/F(n)^(r_0)
        Rvar:=normal(Rvar-rec:-decR[pol][-l][1]/pol^factQ[1,2]);
        Q:=denom(Rvar);
        toremove:= [1]; # list of indices of elements of factQ that are processed during this loop
        # test if the factors in factQ are equal to some shift of pol, if so add them to the decomposition

        for j from 2 to nops(factQ) do
            for i in IntDiffer do
                # test if fact[j,1] is of the form pol(n+i)

                if expand(pol-eval(factQ[j,1],var=var-i-l))=0 then
                    Q:=normal(Q/factQ[j,1]^factQ[j,2]);
                    gcdex(Q,factQ[j,1]^factQ[j,2],normal(Rvar*Q*factQ[j,1]^factQ[j,2]),var,'AAAA','BBBB'); # Bezout relation : 1=A*Q/F(n-i)^r_i + B*F(n-i)^r_i
                    rec:-decR[pol][-i-l]:=AAAA,factQ[j,2];  # compute P_i/F(n-i)^(r_i)

                    Rvar:=normal(Rvar-rec:-decR[pol][-i-l][1]/factQ[j,1]^factQ[j,2]);
                    Q:=denom(Rvar);
                    toremove:=[op(toremove),j];
                    rec:-decR[pol]["min"]:=min(rec:-decR[pol]["min"],-i-l);
                    rec:-decR[pol]["max"]:=max(rec:-decR[pol]["max"],-i-l);
                    break
                fi;
            od;
        od;

        toremove:=seq( `if` (i in toremove, NULL,i), i=1..nops(factQ)); # compute the mirror of the list, ie the indices of factQ to keep
        factQ:=factQ[[toremove]] # update factQ
    od;

    for pol in rec:-CurRepres do 
        for i from min(rec:-decR[pol]["min"],0) to max(rec:-decR[pol]["max"],r-1) do
            if type(rec:-decR[pol][i][1],indexed) then 
                rec:-decR[pol][i]:=0,0
            fi;
        od;
    od;
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
    inds:=(indets(P) union indets(Q)) minus {var};
    degP:=degree(P,var);
    degQ:=degree(Q,var);
    do
        rndpoint:=[seq(i=rnd()/rnd(),i=inds)];
        PP:=eval(primpart(P,var),rndpoint);
        QQ:=eval(primpart(Q,var),rndpoint);
        if degP=degree(PP,var) and degQ=degree(QQ,var) then break fi
    od;
    R:=roots(resultant(eval(PP,var=var-i),QQ,var),i);
    select(type,map2(op,1,R),integer)
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
local i,q,p,cont,r;
    p:=P;q:=primpart(Q,t,'cont');
    if normal(P)=0 then return infinity fi;
    if type(p,polynom(rational)) and type(q,polynom(rational)) then
        for i while divide(p,q,'p') do od
    else
        for i do
            r:=rem(p,q,t,'p');
            if r<>0 then p:=r; break fi 
        od
    fi;
    if nargs=4 then
        co:=p/cont^(i-1)
    fi;
    i-1
end:


### Input
### - X a linear operator in Sn given as a vector or an Orepoly in Sn
### - Sn the variable of the previous polynomial
### - n the variable associated to Sn
### - u a rational fraction
###
### Output
### - G(n)(u,cv) such that uL(cv)-L*(u)cv = G(n+1)(u,cv)-G(n)(u,cv) (lagrange identity)
###

#Certif_lagrange
# Input:
#   u: a rational function in rec:-var
#   rec: record as constructed by InitRed
# Output:
#   result: a vector containing the certificate associated to the lagrange identity 
#           L_2(u) -L(1)u = \Delta_n(result) where L_2 is the antecedent of L by the adjoint operator 
certif_lagrange:=proc(u,rec)
local  result,i,k,var,r;
    var:=rec:-var;
    r:=rec:-r;
    result:=Vector(r);
    for i to r do 
        result[i]:=add(eval(rec:-L[k+1],var=var+i-1)*eval(u,var=var-k+i-1),k=i..r)
    od;
    rec:-denG:=lcm(rec:-denG,seq(primpart(denom(normal(result[i])),var),i=1..r));
    result
end:
