libname := libname, "../.";
with(CreativeTelescoping);
kernelopts(opaquemodules=false): ## needed for now but should be removed in the future

#easy example 
st := time():
CreativeTelescoping(Sum(LegendreP(n, x)*z^n, n = 0 .. infinity), [x::diff, z::diff], certificate = 'c');
CreativeTelescoping(Sum(binomial(n, k)^2*binomial(n + k, k)^2, k = 0 .. n), [n::shift], certificate = 'c'):
CreativeTelescoping(Sum(binomial(n, k)*binomial(m + n - k, n), k = 0 .. n), [m::shift, n::shift], certificate = 'c'):
CreativeTelescoping(Sum(2^k*binomial(m, k)*binomial(n, k), k = 0 .. n), [m::shift, n::shift], certificate = 'c'):
CreativeTelescoping(Sum(HermiteH(n, x)*HermiteH(n, y)*u^n/n!, n = 0 .. infinity), [x::diff, y::diff, u::diff], certificate = 'c'):
CreativeTelescoping(Sum(BesselJ(n, x)^2, n = 1 .. infinity), [x::diff], certificate = 'c'):
CreativeTelescoping(Sum(BesselJ(2*n + 1/2, x), n = 0 .. infinity), [x::diff], certificate = 'c'):
CreativeTelescoping(Sum(BesselJ(n, z)*u^n, n = -infinity .. infinity), [z::diff, u::diff], certificate = 'c'):
CreativeTelescoping(Sum((1/2 - x/2)^q*GAMMA(-2*n + q)*GAMMA(2*n + 2*a + 1 + q)*GAMMA(a + 1)/(q!*GAMMA(-2*n)*GAMMA(2*n + 2*a + 1)*GAMMA(a + 1 + q)), q = 0 .. infinity), [n::shift, a::shift, x::diff], certificate = 'c'):
CreativeTelescoping(Sum((-x^2 + 1)^s*GAMMA(-n + s)*GAMMA(n + a + 1/2 + s)*GAMMA(a + 1)/(s!*GAMMA(-n)*GAMMA(n + a + 1/2)*GAMMA(a + 1 + s)), s = 0 .. infinity), [n::shift, a::shift, x::diff], certificate = 'c'):
CreativeTelescoping(Sum(x^s*GAMMA(a + s)*GAMMA(b + s)*GAMMA(c)/(s!*GAMMA(a)*GAMMA(b)*GAMMA(c + s)), s = 0 .. infinity), [a::shift, b::shift, c::shift, x::diff], certificate = 'c'):
CreativeTelescoping(Sum((x/(x - 1))^n*GAMMA(n + a)*GAMMA(-b + c + n)*GAMMA(c)/((1 - x)^a*n!*GAMMA(a)*GAMMA(-b + c)*GAMMA(c + n)), n = 0 .. infinity), [a::shift, b::shift, c::shift, x::diff], certificate = 'c'):
CreativeTelescoping(Sum(z^n*GAMMA(2*A + n)*GAMMA(b + n)*GAMMA(2*b)/(n!*GAMMA(2*A)*GAMMA(b)*GAMMA(2*b + n)), n = 0 .. infinity), [A::shift, b::shift, z::diff], certificate = 'c'):
CreativeTelescoping(Sum((z^2/(-z + 2)^2)^n*GAMMA(A + n)*GAMMA(A + 1/2 + n)*GAMMA(b + 1/2)/((1 - z/2)^(2*A)*n!*GAMMA(A)*GAMMA(A + 1/2)*GAMMA(b + 1/2 + n)), n = 0 .. infinity), [A::shift, b::shift, z::diff], certificate = 'c'):
CreativeTelescoping(Sum(z^n*GAMMA(3*a + n)*GAMMA(3*a + 1/2 + n)*GAMMA(4*a + 2/3)/(n!*GAMMA(3*a)*GAMMA(3*a + 1/2)*GAMMA(4*a + 2/3 + n)), n = 0 .. infinity), [a::shift, z::diff], certificate = 'c'):
CreativeTelescoping(Sum((27*z^2*(z - 1)/(9*z - 8)^2)^n*GAMMA(n + a)*GAMMA(n + a + 1/2)*GAMMA(2*a + 5/6)/((-1/8)^(2*a)*n!*GAMMA(a)*GAMMA(a + 1/2)*GAMMA(2*a + 5/6 + n)), n = 0 .. infinity), [a::shift, z::diff], certificate = 'c'):
CreativeTelescoping(Sum(z^n*GAMMA(n + a)*GAMMA(n + a + 1/2)*GAMMA(2*a + 1)/(n!*GAMMA(a)*GAMMA(a + 1/2)*GAMMA(2*a + 1 + n)), n = 0 .. infinity), [a::shift, z::diff], certificate = 'c'):
CreativeTelescoping(Sum((-z^2)^s*GAMMA(M + N + 1/2 + s)*GAMMA(M + N + 1 + s)*GAMMA(2*M + 1)*GAMMA(2*N + 1)*GAMMA(2*M + 2*N + 1)/(s!*GAMMA(M + N + 1/2)*GAMMA(M + N + 1)*GAMMA(2*M + 1 + s)*GAMMA(2*N + 1 + s)*GAMMA(2*M + 2*N + 1 + s)), s = 0 .. infinity), [M::shift, N::shift, z::diff], certificate = 'c'):
CreativeTelescoping(Sum(z^n*GAMMA(2*a + n)*GAMMA(2*b + n)*GAMMA(a + b + n)*GAMMA(a + b + 1/2)*GAMMA(2*a + 2*b)/(n!*GAMMA(2*a)*GAMMA(2*b)*GAMMA(a + b)*GAMMA(a + b + 1/2 + n)*GAMMA(2*a + 2*b + n)), n = 0 .. infinity), [a::shift, b::shift, z::diff], certificate = 'c'):
CreativeTelescoping(Sum((-1)^(n - v)*binomial(nn - x, n - v)*binomial(x, v)*p^(n - v)*(1 - p)^v, v = 0 .. n), [p::diff, n::shift, nn::shift, x::shift], certificate = 'c'):
CreativeTelescoping(Sum(t^n*sqrt(2)*BesselJ(n - 1/2, x)/(2*n!*sqrt(x)), n = 0 .. infinity), [t::diff, x::diff], certificate = 'c'):
time() - st;


###
t1:={j*(j - n - 1)*(m + n)*(2*n + x - 1)*(2*n + x)*f(n+1,j,i) +
(2*j - 1)*n*(j - m)*(2*n + x)*(j - n - x + 1)*f(n,j+1,i)+
n*(j + n + x - 1)*(4*j^2*n - (m^2 + 4*n^2 - m)*j
- 2*m*n + (2*j^2 - 4*j*n - m)*x - j*x^2)*f(n,j,i),
j*(j - m + 1)*(j + n + 1)*(j - n - x + 2)*f(n,j+2,i)
+ (2*j^4 + 4*j^3 - j^2*m^2 - 2*j^2*n^2 - 2*j^2*n*x + 2*j^2*n - j^2*x^2 + 2*j^2*x + 2*j^2 - j*m^2
- 2*j*n^2 - 2*j*n*x + 2*j*n - j*x^2 + 2*j*x - m*n^2 - m*n*x + m*n)*f(n,j+1,i)
+ (j + 1)*(j + m)*(j - n)*(j + n + x - 1)*f(n,j,i),f(n,j,i+1)-f(n,j,i)}:
t2:=dfinite_expr_to_sys(binomial(m+x,m-i+j),f(n::shift,j::shift,i::shift)):

t:=LFSol(`sys*sys`(t1,t2)):
S:=Sum(t,j=0..n):
tt:=time():
CreativeTelescoping(S,[n::shift,i::shift],certificate='c'): 
time()-tt;

###
st:=time():
CreativeTelescoping(Sum(GegenbauerC(n, k, x)*GegenbauerC(n, k, y)*u^n/n!, n = 0 .. 10),[k::shift,x::diff,y::diff,u::diff],certificate='c'):
time()-st;


###
st:=time():
res:=CreativeTelescoping(Sum(BesselJ(n, x)*GegenbauerC(n,k,y)*u^n/n!, n = 0 .. 10),[k::shift,x::diff,y::diff,u::diff],certificate='c'):
time()-st;

###
S:=Sum((-1)^k*(4*k+1)*BesselJ(2*k+1/2,w)*LegendreP(2*k,z),k=0..infinity):
tt:=time(): CreativeTelescoping(S,[w::diff,z::diff],certificate='c');time()-tt;

###
st:=time():
CreativeTelescoping(Sum((4*n + 1)*(2*n)!*sqrt(Pi/x/2)*BesselJ(2*n + 1/2, x)*LegendreP(2*n, u)/(2^(2*n)*(n!)^2), n = 0 .. infinity),[x::diff,u::diff],certificate='c'):
time()-st;

###
S:=Sum(GAMMA(a + b + 1+k)/GAMMA(a+b+1)/GAMMA(a + 1+k)*GAMMA(a+1)/GAMMA(b + 1+k)*GAMMA(b+1)*JacobiP(k, a, b, x)*JacobiP(k, a, b, y),k=0..infinity):

tt:=time():st:=CreativeTelescoping(eval(S,[a=1/2]),[b::shift,x::diff,y::diff],certificate='c'):time()-tt;
tt:=time():st,sc,den:=CreativeTelescoping(S,[a::shift,b::shift,x::diff,y::diff],certificate='c'):time()-tt;

###
S:=Sum(LegendreP(n,x)*LegendreP(n,y)*LegendreP(n,z),n=0..infinity):

tt:=time():st:=CreativeTelescoping(eval(S,[z=1/2]),[x::diff,y::diff],certificate='c'): time()-tt;
tt:=time():timelimit(3600,CreativeTelescoping(S,[x::diff,y::diff,z::diff])):time()-tt;

###
P:= (4*x + 2)/(45*x + 5*y + 10*z + 47)/(45*x + 5*y + 10*z + 2)/(63*x - 5*y + 2*z + 58)/(63*x - 5*y + 2*z - 5);
tt:=time():
CreativeTelescoping(S, [x::shift,z::shift], certificate='c'):
time()-tt;

###
S:=Sum((-1)^k*(r*n-(r-1)*k)!*r!^k/(n-k)!^r/k!,k=0..n):
for r from 6 to 10 do
  tt:=time(): CreativeTelescoping(S,[n::shift],certificate='c'): print(time()-tt);
od:






