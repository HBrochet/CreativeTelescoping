Copyright (c) 2018, Alin Bostan, Frédéric Chyzak, Pierre Lairez, Bruno Salvy

### INDICIAL EQUATION

valpol:=proc(
    P :: depends(polynom(anything, t)),
    Q :: depends(polynom(anything, t)),
    t :: name, co
              )
local i,q,p,cont,valco;
    p:=P;q:=primpart(Q,t,'cont');
    if normal(P)=0 then return infinity fi;
    if type(p,polynom(rational)) and type(q,polynom(rational)) then
        for i while divide(p,q,'p') do od
    else
        for i while rem(p,q,t,'p')=0 do od
    fi;
    if nargs=4 then
        valco:=rem(p,q,t)/cont^(i-1);
#        ASSERT(expand(rem(normal(P/Q^(i-1)),Q,t)-valco)=0);
        co:=valco
    fi;
    i-1
end:

intsols := proc(pol, s :: name)
local fpol;

    fpol := factor(pol);
    if fpol = 0 then
        return {s};
    elif type(fpol, `*`) then
        fpol := select(p -> indets(p) = {s}, fpol);
    elif indets(fpol) <> {s} then
        fpol := 1;
    fi;
    return map(subs, {isolve(fpol)}, s);

end proc:

indicialeq0 := proc(
    L :: depends(polynom(anything, [Dvar, tvar])),
    pol :: depends(Or(identical(infinity), polynom(anything, tvar))),
    var,
    { Dvar :: name := NULL,
      tvar :: name := NULL })

local retshift, lvals, co, i, j, res, dq, pow, q, cont;

    if L = 0 then
        return 1, -infinity;
    fi;

    lvals:=[seq(i-valpol(coeff(L,Dvar,i),pol,tvar,co[i]),i=0..degree(L,Dvar))];
    retshift:=max(op(lvals));
    q:=primpart(pol,tvar,'cont');
    res:=0;dq:=diff(q,tvar);pow:=1;
    for i from 0 to degree(L,Dvar) do
        if i>=1 then pow:=rem(pow*dq,q,tvar) fi;
        if lvals[i+1]=retshift then res:=res+cont^i*rem(pow*co[i],q,tvar)*mul(-var-j,j=0..i-1) fi
    od;

#    ASSERT(map(expand,[oldindicialeq0(args)])=map(expand,[res,retshift]));
    res,retshift

end proc:

indicialeq0inf := proc(
    L :: depends(polynom(anything, [Dvar, tvar])),
    var,
    { Dvar :: name := NULL,
      tvar :: name := NULL })

local q, r, v, lc, shift, retshift, retlc;

    if L = 0 then
        return 1, -infinity;
    fi;

    r := rem(L, Dvar, Dvar, 'q');

    v := degree(r, tvar);
    lc, shift := thisproc(q, var-1, _options);

    retshift := max(shift-1, v);
    retlc := 0;

    if v = retshift then
        retlc := lcoeff(r, tvar);
    fi;

    if shift-1 = retshift then
        retlc := retlc + lc*var;
    fi;

    return retlc, retshift;
end proc:

# input:
#   L, diff. op. in Dvar and tvar
#   pol, a polynomial in tvar, or infinity (think pol=1/tvar)
#   var, a variable name
# output:
#   - a set of integers
#   - the corresponding formal leading coeff Q(s, tvar),
#   - the shift
# They satisfy
#   L(1/pol^s) = Q/pol^(s+shift)
# and the set of integers are the values of s for which Q is not invertible
# modulo pol.
indicialeq1 := proc(
    L :: depends(polynom(anything, [Dvar, tvar])),
    pol :: depends(Or(identical(infinity), polynom(anything, tvar))),
    var :: name,
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      dofactor :: boolean := false })

option remember;
local lc, shift, indeq, integers;

    if pol = infinity then
        lc, shift := indicialeq0inf(L, var, _options);
    else
        lc, shift := indicialeq0(L, pol, var, _options);
    fi;

    if dofactor or pol = infinity then
        # we can assume that pol is irreducible
        indeq := foldl(gcd, coeffs(collect(lc, tvar), tvar));
    else
        indeq := resultant(lc, pol, tvar);
    fi;
    integers := intsols(indeq, var);

    userinfo(3,'redct',sprintf("integral exponents at %.300a: % a",pol,integers));
    userinfo(3,'redct',sprintf("shift there: % a",shift));
    return integers, normal(lc), shift
end proc:

# Returns pol as a product of L-irreducible polynomials.
splitpol := proc(
    pol :: depends(polynom(anything, tvar)),
    L :: depends(polynom(anything, [Dvar, tvar])),
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      dofactor :: boolean := true })

option remember;
local sing, Q, Qev, _, p1, p2, sval;

    # La factorisation semble beaucoup plus rapide que splitpot...
    if dofactor then
        return factor(pol);
    fi;

    if type(pol, `*`) then
        return map(splitpol, pol, L, _options)
    elif type(pol,`^`) then
        return splitpol(op(1,pol),L,_options)^op(2,pol)
    elif degree(pol, tvar) <= 0 then
        return pol;
    fi;

    sing, Q, _ := indicialeq1(L, pol, indvar_, _options);

    for sval in sing do
        Qev := normal(subs(indvar_ = sval, Q));
        if Qev <> 0 then
            ASSERT(degree(Qev, tvar) > 0);
            p1 := gcd(pol, numer(Qev));
            p2 := normal(pol/p1);
            ASSERT(degree(p1, tvar) < degree(pol, tvar));
            ASSERT(degree(p2, tvar) < degree(pol, tvar));
            return thisproc(p1, L, _options)*thisproc(p2, L, _options);
        fi;
    end do;

    return pol;

end proc:

# Returns a right multiple of L such that the shift associated to any factor of
# singp is null.
zeroshift := proc(
    L :: depends(polynom(anything, [Dvar, tvar])),
    singp,
    { Dvar :: name := NULL,
      tvar :: name := NULL })

option remember;
local s, f, Lden, Lnum, facts, shiftpol, shift, splsing, _;

    Lden := denom(normal(L));
    Lnum := numer(normal(L));
#    singp := Lden * lcoeff(collect(Lnum, Dvar), Dvar);

    splsing := splitpol(singp, Lnum, _options);
    _, facts := op(sqrfree(splsing, tvar));

    shiftpol := 1;
    for f in facts do
        _, _, shift := indicialeq1(Lnum, f[1], s, _options);
        shiftpol := shiftpol*f[1]^(shift+valpol(Lden, f[1], tvar));
    end do;

    return DETools['mult'](L, shiftpol, [Dvar,tvar]), shiftpol;
end proc:


# Returns L(A)
applydop := proc(
    A,
    L :: depends(polynom(anything, [Dvar,tvar])),
    { Dvar :: name := NULL,
      tvar :: name := NULL
    })
local Lc, fn, ret, k;

    Lc := PolynomialTools['CoefficientVector'](L, Dvar);

    fn := A;
    ret := 0;
    for k from 1 to LinearAlgebra['Dimension'](Lc) do
        ret := ret + Lc[k]*fn;
        fn := diff(fn, tvar);
    od;

    return normal(ret);
end:


# If A = B + C*CERT, checks that B + L(C) = 0
checkcert := proc(
    A,
    L :: depends(polynom(anything, [Dvar, tvar])),
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      cert :: name := 0 })

local lhs,rhs, res;

    lhs := subs(cert=0, A);
    rhs := coeff(A, cert);

    res := lhs + applydop(rhs, L, _options);

    return evalb(normal(res) = 0);

end proc:


rembezout := proc(P, Q, t)
option remember;
local A, B;
    gcdex(P, Q, t, A, B);
    return A, B;
end proc:

# return A such that
# A*P*Q + B*R = S
# for some B
customgcdex := proc(P, Q, R, S, t)

local U, V, ret;
    U, V := rembezout(P, R, t);
    ASSERT(normal(U*P+V*R-1)=0);

    ret := powmod(Q, -1, R, t);
    ret := rem(U*rem(rem(S, R, t)*ret, R, t), R, t);
    ASSERT(rem(ret*P*Q - S, R, t) = 0);

    return ret;

end proc:

# Input:
#    - A, a rational function
#    - denfact, a polynomial
#    - L, a differential operator
# Output
#    U, V, C
#    where A = U + V + L(C),
#    U is the reduced part, V is the part to be reduced further and C is the certificate.
localreduction_base := proc(
    A,
    denfact,
    L :: depends(polynom(anything, [Dvar, tvar])),
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      cert :: anything := 0,
      absolute :: boolean := false })

local sing, lcgen, shift, den, exponent, lcev, redpart, redA, num, R, U, reductor, ccert, g, invden;

    sing, lcgen, shift := indicialeq1(L, denfact, indvar_, _options);
    if indvar_ in sing then
        error "Split %1 or shift the operator %2.", denfact, L;
    fi;

    den := denom(normal(A));
    exponent := valpol(den, denfact, tvar);

    if exponent = 0 then
        return A, 0, 0;
    fi;

    lcev := normal(subs(indvar_ = exponent - shift, lcgen));

    redA := normal(A*denfact^exponent);
    num := numer(redA);
    den := denom(redA);
    invden:=powmod(den,-1,denfact,tvar);

    ASSERT(degree(gcd(den, denfact), tvar) = 0);

    if exponent - shift in sing then
        if lcev <> 0 then
            error "Please split the denominator.";
        fi;

        if absolute then
            # Compute U such that A = diff(U/P,t$(exponent-1)) + O(P^(-exponent + 1))
            U := rem( num*invden*powmod(-diff(denfact, tvar), -exponent+1, denfact, tvar)/(exponent-1)!, denfact, tvar );

            if exponent = 1 then
                redpart := U/denfact;
            else
                redpart := diff(U/denfact, tvar$(exponent-1));
            fi;

        else
            U := rem(invden*rem(num, denfact, tvar), denfact, tvar);
            redpart := U/denfact^exponent;
        fi;

        ASSERT(valpol(denom(normal(A - redpart)), denfact, tvar) < exponent);
        return normal(redpart), normal(A-redpart), 0;

    else
#        gcdex(den*lcev, denfact, num, tvar, 'R', 'U');
        g:=gcdex(lcev, denfact, tvar, 'R');
        ASSERT(g=1);
#        R:=rem(R*invden*num,denfact,tvar);
        R:=rem(R*rem(invden*rem(num,denfact,tvar),denfact,tvar),denfact,tvar);
        ASSERT(degree(R, tvar) < degree(denfact, tvar));

        ccert := R/denfact^(exponent - shift);
        reductor := applydop(ccert, L, _options);

        ASSERT(valpol(denom(normal(A - reductor)), denfact, tvar) < exponent);

        return 0, normal(A-reductor), ccert;

    end if;

end proc:




localreduction := proc(
    A,
    denfact,
    L :: depends(polynom(anything, [Dvar, tvar])),
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      cert :: Or(identical(0), name) := 0 })
local red, C, V, U, Cpart;

    red := 0;
    C := 0;
    V := normal(A);
    while V <> 0 do
        U, V, Cpart := localreduction_base(V, denfact, L, _options);
        red := red + U;
        C := C + Cpart;
    end do;

    return normal(red), C;

end proc:



# Performs the localreduction on the factors of the denominator.
hermitered0 := proc(
    A,
    L :: depends(polynom(anything, [Dvar, tvar])),
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      cert := 0,
      dofactor :: boolean := true
    })

local splpol, sqfden, _, red, C, f, Cpart;

    splpol := splitpol(denom(A), L, _options);

    _, sqfden := op(sqrfree(splpol));   # NB: sqrfree preserves factorization as much as possible
    sqfden := select(has, sqfden, tvar);

    red := A;
    C := 0;
    for f in sqfden do
        red, Cpart := localreduction(red, f[1], L, _options);
        C := C + Cpart;
    od;

    return red, C;

end proc:


# Hermite reduction at infinity.
hermitered1 := proc(
    A,
    L :: depends(polynom(anything, [Dvar, tvar])),
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      cert := 0
    })

local numq, numr, An, sing, lcgen, shift, red, ccert, deg, lcnumq, lcev, reductor;

    An := normal(A);
    numr := rem(numer(An), denom(An), tvar, 'numq');
    sing, lcgen, shift := indicialeq1(L, infinity, indvar_, _options);

    red := 0;
    ccert := 0;
    while numq <> 0 do
        deg := degree(numq, tvar);
        lcnumq := lcoeff(numq, tvar);
        if not deg - shift in sing and deg >= shift then
            lcev := subs(indvar_ = deg - shift, lcgen);

            reductor := applydop(lcnumq/lcev*tvar^(deg - shift), L, _options);

            ccert := ccert + lcnumq/lcev*tvar^(deg - shift);
            numq := normal(numq - reductor);
        else
            numq := normal(numq - lcnumq*tvar^deg);
            red := red + lcnumq*tvar^deg
        fi;
        ASSERT(degree(numq, tvar) < deg);
    end do;

    return numr/denom(An) + red, ccert;

end proc:


hermitered := proc(
    A,
    L :: depends(polynom(anything, [Dvar, tvar])),
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      cert := 0
    })

local red, C0, C1;

    red, C0 := hermitered0(A, L, _options);
    red, C1 := hermitered1(red, L, _options);

    return red + cert*(C0+C1);

end proc:



exceptionalbasis := proc(
    L :: depends(polynom(anything, [Dvar, tvar])),
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      cert :: Or(identical(0), name) := 0,
      liouvilleform :: boolean := false })

option remember;
local lc, sqflc, basis, f, sing, Q, shift, Qev, g, cden, pbasis, new, num, den, co1, co2, newbasis, _, s, k, R, st;
    st:=time();
    userinfo(2,'redct',"entering exceptionalbasis at time",time());

    basis := {};

    if not liouvilleform then
    lc := splitpol(lcoeff(normal(numer(L)), Dvar), L, _options);

    _, sqflc := op(sqrfree(lc));
    sqflc := select(has, sqflc, tvar);

    for f in sqflc do
        sing, Q, shift := indicialeq1(L, f[1], indvar_, _options);
        for s in select(`>`, sing, 0) do
            Qev := subs(indvar_ = s, Q);
            g := normal(f[1]/gcd(f[1], Qev)); # Qev*h = 0 mod f iff h is divided by g.
            ASSERT(degree(g, tvar) < degree(f[1], tvar)); # Otherwise s is not really a singularity
            basis := basis union {seq(tvar^k*g/f[1]^s, k=0..degree(f[1], tvar)-degree(g, tvar)-1)};
        end do;
        for s in {seq(s, s=1..-shift)} do
            Qev := subs(indvar_ = s, Q);
            g := normal(f[1]/gcd(f[1], Qev)); # Qev*h = 0 mod f iff h is divided by g.
            ASSERT(type(applydop(R, L, _options), polynom(anything, tvar)));
            basis := basis union {seq(tvar^k/f[1]^s, k=0..degree(f[1], tvar)-1)};
        end do;
    end do;
    fi;

    sing, Q, shift := indicialeq1(L, infinity, indvar_, _options);
    basis := basis union {seq(tvar^s, s in select(`>=`, sing, 0))};

    for R in basis do
        new:=normal(hermitered(applydop(R, L, _options), L, _options));
        if new=0 then newbasis[R]:=NULL
        else
            num:=primpart(numer(new),tvar,'co1');
            den:=primpart(denom(new),tvar,'co2');
            newbasis[R]:=num/den-co2/co1*cert*R
        fi
    od;
    basis:={seq(newbasis[R],R=basis)};

#    basis:={seq(hermitered(applydop(R, L, _options), L, _options)-cert*R,R=basis)};

    cden := lcm(seq(denom(
        `if`(type(cert, name), normal(subs(cert=0, R)), R)
                         ), R in basis));

    pbasis := [seq(
        `if`(type(cert, name), collect(cden*R, cert, normal), normal(cden*R))
        , R in basis)];

    pbasis:=echelonpols(pbasis, _options);
    if pbasis<>[] then
        userinfo(2,'redct',"dimension of the exceptional set",nops(pbasis));
        userinfo(2,'redct',"degrees of its elements",(map(degree,pbasis,tvar)));
        userinfo(2,'redct',"sizes of its elements",(map(length,pbasis)));
    fi;
    userinfo(2,'redct',"exceptional basis computed in ",time()-st,"sec.");

    return cden, pbasis

end proc:


echelonpols := proc(
    pols :: list,
    { tvar :: name := NULL,
      cert :: Or(identical(0), name) := 0 })
local npols, imax, echelon, rpol, spol, co;

    if nops(pols) <= 1 then
        return pols;
    fi;

    if type(cert, name) then
        npols := map(normal, subs(cert=0, pols));
    else
        npols := map(normal, pols);
    fi;
    ASSERT(type(npols, list(polynom(anything, tvar))));

    imax := max[index](map(degree, npols, tvar));
    echelon := echelonpols(subsop(imax=NULL, pols), _options);
    rpol := redmodpols(pols[imax], echelon, _options);

    if type(cert,'name') then spol:=coeff(rpol,cert,0) else spol:=rpol fi;
    spol:=primpart(spol,tvar,'co');
    if type(cert,'name') then spol:=spol+coeff(rpol,cert,1)/co fi;

    return remove(`=`, [spol, op(echelon)], 0);
end proc:

redmodpols := proc(
    p,
    pols :: list,
    { tvar :: name := NULL,
      cert :: Or(identical(0), name) := 0 })

local spol, L, degs, deg, j, ccert, certL, lc;

    L:=pols;

    spol := p;

    if type(cert, name) then
        ccert := coeff(spol,cert);
        spol:=subs(cert=0,spol);
        certL:=map(coeff,L,cert);
        L:=subs(cert=0,L)
    else
        ccert:=0
    fi;

    degs:=map(degree,L,tvar);

    while L<>[] do
        j:=max['index'](degs);
        deg:=degs[j];
        lc:=coeff(spol,tvar,deg);
        if lc<>0 then
            spol:=collect(spol-lc*L[j]/coeff(L[j],tvar,deg),tvar,normal);
            if type(cert,name) then
              ccert:=ccert-lc/coeff(L[j],tvar,deg)*certL[j]
            fi;
        fi;
        degs:=subsop(j=NULL,degs);
        L:=subsop(j=NULL,L);
        if type(cert,name) then certL:=subsop(j=NULL,certL) fi
    end do;

    return spol + cert*ccert;

end proc:

redmodfracs := proc(
    A,
    cden,
    basis,
    { tvar :: name := NULL,
      cert :: Or(identical(0), name) := 0 })

local numq, B, numr;

    B := normal(A*cden);
    numr := rem(numer(B), denom(B), tvar, 'numq');

    numq := redmodpols(numq, basis, _options);

    return numq/cden + numr/cden/denom(B);

end proc:


reduction := proc(
    A,
    L :: depends(polynom(anything, [Dvar, tvar])),
    { Dvar :: name := NULL,
      tvar :: name := NULL,
      cert := 0
    })

local cden, basis, red;

    cden, basis := exceptionalbasis(L, _options, _rest);
    red := hermitered(A, L, _options, _rest);
    red := redmodfracs(red, cden, basis, _options, _rest);

    return normal(red);
end proc:
