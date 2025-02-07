with(PolynomialTools):

inversemod_xgcd := proc(a,b,p)
description "find a^(-1) mod b with xgcd method":
local s,t:
    Gcdex(b,a,x,'s','t') mod p:
    return t:
end proc:

reciprocal := proc(a,n,x)
description "compute the reciprocal r of a with deg(r) = n":
local r,v, m, i:
    m := degree(a,x):
    v := CoefficientList(a,x):
    v := [op(v), seq(0, i=1..n-m)]:
    return FromCoefficientList(v, x, termorder = reverse):
end proc:

truncate_naive := proc(a, m, n, x)
description "remove the terms of degree >= n and shift the terms <=m":
local v, nv:
    v := CoefficientList(a, x):
    if n > nops(v) then nv := nops(v) else nv:=n: end if:
    return FromCoefficientList(v[m+1..nv],x):
end proc:

extension_tellegen := proc(a, r, n, p)
description "Extend r with the relation a at order n, algorithm from tellegen's principle "
    "into practice Bostan, Lecerf, Schost":
local alpha, reca, mid, mid2,  m:
    m := degree(a):
    reca := reciprocal(a, m, x) mod p:
    alpha := inversemod_xgcd(reca, x^(n-m+1), p):
    mid := truncate_naive(reca*r, m, n+1, x) mod p:
    mid2 := truncate_naive(mid*alpha, 0, n-m+1,x):
    return expand(r - x^m*mid2) mod p:
end proc:

Extension_univariate := proc(r,g, n)
description "Extend r in K[x] with deg(r) >= deg(g)-1 and compute the first 2deg(g) "
    "terms of the sequence v with initial terms r and with relation g":
local v, vi, vect_g, d, i,j:
    v := CoefficientList(r, x, termorder = reverse):
    vect_g := CoefficientList(g, x):
    d := degree(g):
    for i from d to n do
        vi := 0:
        for j from 1 to d do
            vi := vi - v[j+i-d]*vect_g[j] mod p:
        end do:
        v := [op(v), vi]:
    end do:
    return FromCoefficientList(v, x, termorder = reverse):
end proc:

p := 97:
fib := x^2 -x -1:
extension_tellegen(fib, x+1, 10, p);
Extension_univariate(x+1, fib, 10);



m := 10:
a := x^m + randpoly(x, coeffs = rand(0..p-1), dense, degree = m-1):
r := randpoly(x,coeffs = rand(0..p-1), dense, degree = m-1):
n := 20:


extension_tellegen(a, reciprocal(r,m-1,x), 20, p);

Extension_univariate(r, a, 20);
