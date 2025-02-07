read "guessing.mpl":
read "EMGCD.mpl":
read "univariate.mpl":
read "bivariate_iterative.mpl":
read "lazard.mpl":
with(Groebner):
with(PolynomialTools):

truncate_y := proc(r, n)
description "compute the polynomial formed by the n first coefficients of high degree "
    "of r":
local L, m , res:
    res := r:
    if (1 > n) then
        return res:
    end if:
    L := CoefficientList(res, y, termorder = reverse):
    m := min(n, degree(res)):
    res := FromCoefficientList(L[1..m+1], y, termorder = reverse):
    return res:
end proc:

half_gcd_twovar := proc(r0, r1, k, Gx)
description "Extension of Half gcd for two variables ":
local d, dstar, r0_trunc, r1_trunc, rd, rd1, rd_trunc, rd1_trunc, gd, Q1, Qd, S, R, v, G1, rdm1, Rd, Q2, G2:
    if (k = 0) then return Matrix([[1,0],[0,1]]), [], Gx:
    end if:
    d := ceil(k/2):
    # 1st recursive call
    r0_trunc := truncate_y(r0, 2*(d-1)):
    r1_trunc := truncate_y(r1, 2*(d-1)-1):

    R, Q1, G1 := half_gcd_twovar(r0_trunc, r1_trunc, d-1, Gx):

    # Update r0,r1 -> rd-1, rd
    v := R.Vector([[r0],[r1]]) mod p:
    rdm1, rd := sort(expand(v[1]) mod p, order = ord), sort(expand(v[2]) mod p, order = ord):

    rdm1 := sort(expand(Extraction_xaxis(rdm1,degree(Gx[1]))) mod p, order = ord):
    rd := sort(expand(Extraction_xaxis(rd,degree(Gx[1]))) mod p, order = ord):

    rdm1 := sort(expand(Extension_twovar_onerelation(rdm1,Gx[1])) mod p, order = ord):
    rd := sort(expand(Extension_twovar_onerelation(rd,Gx[1])) mod p, order = ord):
    if (degree(rdm1,y) <> degree(rd,y) + 1) then return R, Q1, G1 end if: #track that we still are in normal case

    Qd, gd := Quo_twovar(rdm1, rd):
    Rd := map(proc(t) Rem(t, Gx[1], x) mod p end proc, Qd.R):
    v := Rd.Vector([[r0],[r1]]) mod p:
    rd, rd1 := v[1], v[2]:
    rd :=  sort(expand(Extraction_xaxis(rd,degree(Gx[1]))) mod p, order = ord):
    rd1 :=  sort(expand(Extraction_xaxis(rd1,degree(Gx[1]))) mod p, order = ord):

    rd := sort(expand(Extension_twovar_onerelation(rd,Gx[1])) mod p, order = ord):
    rd1 := sort(expand(Extension_twovar_onerelation(rd1,Gx[1])) mod p, order = ord):
    if (rd1 = 0) or (degree(rd,y) <> degree(rd1,y) + 1) then #gcd founded or track normal case
        return Rd, [op(Q1), Qd], [op(G1), gd]:
    end if:

    dstar := floor(k/2):
    rd_trunc := truncate_y(rd, 2*dstar):
    rd1_trunc := truncate_y(rd1, 2*dstar-1):
    S, Q2, G2 := half_gcd_twovar(rd_trunc, rd1_trunc, dstar, [op(G1), gd]):
    return map(proc(t) Rem(t, Gx[1], x) mod p end proc, S.Rd), [op(Q1), Qd, op(Q2)], G2:
end proc:


balanced_prod := proc(Qy, f)
description "Compute the product R_k = Q_k...Q_1 with divide and conquer method "
    "for balanced degree computation, with Qy = [Q_1,Q_2,..., Qk]":
local d, k, R,S:
    k := nops(Qy):
    if k = 1 then
        return Qy[1]:
    end if:
    d := floor(k/2):
    R := balanced_prod(Qy[1..d], f):
    S := balanced_prod(Qy[(d+1)..k], f):
    return map(proc(t) Rem(t, f, x) mod p end proc, S.R):
end proc:

BM_halfgcd_twovar := proc(P, Dy)
description "P in (K^N)[y] representing a C-recursive sequence u_{i,j}, the function computes "
    "the reduced Gröbner basis of the ideal of relation I(u) via an extension to "
    "bivariate of the half gcd algorithm. The polynomial P has cofficients on "
    "a (Dx,Dy)-parallelotope with Dx >= 2dx and Dy >= 2dy and x^(dx), y^(dy) in lm(G)":
local r0, r1, degGx, Qy, Gx, G, i, k, Q1, g1, v, r2, R,Q, l:
    r0 := y^(Dy+1):
    r1 := P:
    Q1, g1 := Quo_twovar(r0, r1):
    Gx := [g1]:
    v := Q1.Vector([[r0],[r1]]):
    r2 := v[2]:
    r2 := sort(expand(Extraction_xaxis(r2,degree(Gx[1]))) mod p, order = ord):
    r2 := sort(expand(Extension_twovar_onerelation(r2,Gx[1])) mod p, order = ord):
    R, Qy, Gx := half_gcd_twovar(r1, r2, Dy, Gx):
    Qy := [Q1, op(Qy)]:
    R := R.Q1:
    Gx := [op(Gx), 1]:
    G := [Gx[1]]:
    Qy := [Matrix([[1,0],[0,1]]), op(Qy)]:
    l := degree(Gx[1]):
    for i from 2 to nops(Gx) do
        if (l <> degree(Gx[i])) then
            Q := balanced_prod(Qy[1..i], Gx[1]):
            G := [op(G), Q[2,2]*Gx[i]]:
            l := degree(Gx[i]):
        end if:
    end do:
    return G;
   # return Basis(G, ord, characteristic = p);
end proc:


####################################
###            Context           ###
####################################
p := 65537:
vars := [x,y]:
ord := plex(y,x):                        # y > x
F := [seq(randpoly(vars, dense, degree=1)^5, i=1..2)]:
# Gu := Groebner:-Basis (F,ord, characteristic = p);
leadm := [x^30, x*y,y^10]:
Gu := gblex(leadm, p):
Gux := [seq(lcoeff(Gu[i], y), i = 1..nops(Gu))]:
LMGu := LeadingMonomial(Gu, ord):
Dx:= 2*degree(LMGu[1]):                 #LMGu[1] = x^dx
Dy:= 2*degree(LMGu[-1]):                #LMGu[-1] = y^dy
M:= x^Dx*y^Dy;
Tab := fromGbToRandomSequence(Gu, vars, ord, p):
mon:= sortListMon ([seq (seq (x^i*y^j,j=0..Dy),i=0..Dx)], ord):
P:=from1SetToMirrorTruncatedGeneratingSeries (Tab,vars,mon):

# ###############################
# # Compute the reduced Gröbner #
# # basis of (u_{i,j})          #
# ###############################
v := Matrix([[y^(Dy+1)],[P]]):
Gres := BM_halfgcd_twovar(P, Dy):
Gres := Basis(Gres,ord, characteristic=p):
if Gu = Gres then
    print("BM_halfgcd_twovar ok"):
else
    print("BM_halfgcd_twovar not ok"):
end if:

