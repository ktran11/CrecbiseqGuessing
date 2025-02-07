read "guessing.mpl":
with(Groebner):
with(PolynomialTools):
with(LinearAlgebra[Modular]):

# General context
p := 65537;                             #prime
n := 20:                                #polynomial degree
l := 4:                                 #gcd degree


Truncated_Euclidean_algorithm := proc(r0, r1)
description "Perform the euclidean algorithm on (r0,r1) with deg(r0)>= deg(r1), iteratively compute (ri,ui,vi) that"
    "verifies ri = ui r0 + vi r1 and stop when deg(ri) < deg(vi) and returns the triplet "
    "(r,u,v) with r = (ri), u = (ui), v = (vi)":
local r,u,v,qi,i:
    r := [r0,r1]:
    u := [1,0]:
    v := [0,1]:
    for i from 2 to degree(r0)+1 while degree(r[i]) >= degree(v[i]) do
        qi := Quo(r[i-1], r[i], x) mod p:
        r := [op(r), expand(r[i-1] - qi*r[i]) mod p]:
        u := [op(u), expand(u[i-1] - qi*u[i]) mod p]:
        v := [op(v), expand(v[i-1] - qi*v[i]) mod p]:
    end do:
    return r,u,v:
end proc:

BM_Euclid := proc(P,Dx)
description "Berlekamp Massey algorithm with naive EEA":
local r0,r1,r,u,v:
    r0 := x^(Dx):
    r1 := P:
    r,u,v:= Truncated_Euclidean_algorithm(r0,r1):
    # seq(print(degree(r[i]),degree(v[i])), i=1..nops(v)):
    # return r,u,v:
    if degree(v[-1]) < Dx then
        return v[-1]/lcoeff(v[-1]) mod p:
    else
        return 0:
    end if:
end proc:


truncate := proc(r, n)
description "compute the polynomial formed by the n first coefficients of high degree "
    "of r":
local L, m , res:
    res := r:
    if (1 > n) then
        return res:
    end if:
    L := CoefficientList(res,x, termorder = reverse):
    m := min(n, degree(res)):
    res := FromCoefficientList(L[1..m+1], x , termorder = reverse):
    return res:
end proc:

half_gcd := proc(r0, r1, k)
description "Half gcd algorithm for normal case";
local d, dstar, r0_trunc, r1_trunc, rd, rdm1, rd1, rd_trunc, rd1_trunc, qd, Qd, S, R, v:
    if k = 0 then return Matrix([[1,0],[0,1]]):
    end if:
    d := ceil(k/2):
    r0_trunc := truncate(r0, 2*(d-1)):
    r1_trunc := truncate(r1, 2*(d-1)-1):

    R := half_gcd(r0_trunc, r1_trunc, d-1):
    v := R.Vector([[r0],[r1]]) mod p:
    rdm1, rd := expand(v[1]) mod p, expand(v[2]) mod p:

    if (degree(rdm1) <> degree(rd) + 1) then return R end if: #track that we still are in normal case

    qd, rd1 := Quo(rdm1, rd, x) mod p, Rem(rdm1, rd, x) mod p:
    Qd := Matrix([[0,1],[1, -qd]]) mod p:
    if (rd1 = 0) or (degree(rd) <> degree(rd1) + 1) then #gcd founded or track normal case
        return map(expand, Qd.R) mod p:
    end if:

    dstar := floor(k/2):
    rd_trunc :=  truncate(rd, 2*dstar):
    rd1_trunc := truncate(rd1, 2*dstar -1):
    S := half_gcd(rd_trunc, rd1_trunc, dstar):

    return map(expand, S.Qd.R) mod p:
end proc:


xgcd_from_halfgcd := proc(r0, r1)
description "Compute (g,u,v) s.t. u r0 + v r1 = g with g = gcd(r0,r1), done with "
    "the half-gcd subroutine and with input in normal case":
local k,P,u,v,g,c:
    k := max(degree(r0), degree(r1)):
    P := half_gcd(r0, r1, k):
    u := P[1,1]:
    v := P[1,2]:
    g := expand(u*r0+v*r1) mod p:
    c := lcoeff(g);
    return (g/c mod p, u/c mod p, v/c mod p):
end proc:

BM_halfgcd := proc(P,Dx)
description "find a relation on P with the half gcd method":
local R:
    R := half_gcd(x^(Dx+1), P, Dx+1):
    if degree(R[2,2]) < Dx then
        return R[2,2]/lcoeff(R[2,2]) mod p:
    else
        return 0:
    end if:
end proc:

#######################
###     Context     ###
#######################

##################
# Computing xgcd #
##################
h := x^l + randpoly(x, coeffs = rand(0..p-1), dense, degree = l-1);
r0 := randpoly(x, coeffs = rand(0..p-1), dense, degree = n-l) * h mod p:
r1 := randpoly(x, coeffs = rand(0..p-1), dense,  degree = n-1-l) * h mod p:
(g,u,v) := xgcd_from_halfgcd(r0,r1);
if g=h and g = expand(u*r0 + v*r1) mod p then
    print("xgcd ok")
else
    print("xgcd not ok"):
end if;

############################
#     Computing sequence   #
############################

######################
# Build the sequence #
######################
r := randpoly(x, coeffs = rand(1..p-1), dense, degree = n):
G := [r*LeadingCoefficient(r, plex(x))^(-1) mod p];
Dx := 2*degree(G[1]):
Tab := fromGbToRandomSequence(G, [x], plex(x), p):
mon := sortListMon ([seq (x^i,i=0..Dx-1)], plex(x)):
P := from1SetToMirrorTruncatedGeneratingSeries (Tab,[x],mon):

####################
# Via naive method #
####################
#trace(BM_Euclid):
rstar := BM_Euclid(P,Dx):
if (rstar = G[1]) then
          print("BM_Euclid ok"):
else
    print("BM Euclid not ok"):
end if:

################
# Via half-gcd #
###############
rstar := BM_halfgcd(P, Dx):
if (rstar = G[1]) then
    print("BM_halfgcd ok"):
else
    print(rstar, G[1], "BM_halfgcd not ok"):
end if:

###############
# Limit case  #
###############
# P := 1:
# Dx := 0:

# r_euclid := BM_Euclid(P, Dx):
# r_halfgcd := BM_halfgcd(P,Dx):

# if r_euclid = 0 then
#     print("BM_Euclid ok for sequence (1,0,0,....)"):
# else
#     print("BM_Euclid not ok for sequence (1,0,0,....)"):
# end if:

# if r_halfgcd = 0 then
#     print("BM_halfgcd ok for sequence (1,0,0,....)"):
# else
#     print("BM_halfgcd not ok for sequence (1,0,0,....)"):
# end if:


# G := [0]:
# P := 0:
# Dx := 1:                #Dx = 0 or 1?


# rE := BM_Euclid(P,Dx);
# if (rE = 0) then
#     print("BM_Euclid limitcase ok"):
# else
#     print("BM_Euclid limitcase not ok"):
# end if:

# rhg := BM_halfgcd(P,Dx);
# if (rhg = G[1]) then
#     print("BM_halfgcd limit case ok"):
# else
#     print("BM_halfgcd limit case not ok"):
# end if:
