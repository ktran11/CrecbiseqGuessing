read "guessing.mpl":
read "EMGCD.mpl":
read "univariate.mpl":
read "bivariate_iterative.mpl":
read "lazard.mpl":
with(Groebner):
with(PolynomialTools):

harpoon_y := proc(r, k)
description "compute r harpoon_y k = r quo y^{deg_y(r) - k}" :
local L, m, res:
    res := r:
    L := CoefficientList(res, y, termorder = reverse):
    m := min(k, degree(res, y)):
    res := FromCoefficientList(L[1..m+1], y, termorder = reverse):
    return res:
end proc:

half_gcd_seq := proc(rm1, r0, f0, k)
description "Extension of Half gcd for two variables ":
local d, dstar, rm1_trunc, r0_trunc, R, T, F0, v, rdm2, rdm1, Qdm1, fdm1, Rd, rd, rdm1_trunc, rd_trunc, S, U, F1, DDx:
    if (k = 0) then return Matrix([[1,0],[0,1]]), [], []:
    end if:
    DDx := degree(rm1, x):
    d := ceil(k/2):
    dstar := k-d:
    # 1st recursive call
    rm1_trunc := harpoon_y(rm1, 2*(d-1)):
    r0_trunc := harpoon_y(r0, 2*(d-1)-1):

    R, T, F0 := half_gcd_seq(rm1_trunc, r0_trunc, f0, d-1):

    # Update r0,r1 -> rd-1, rd
    v := R.Vector([[rm1],[r0]]) mod p:

    rdm2 := Extension_twovar_onerelation(Extraction_xaxis(v[1],degree(f0,x), DDx), f0, 2*degree(f0,x)):
    rdm1 := Extension_twovar_onerelation(Extraction_xaxis(v[2],degree(f0,x), DDx), f0, 2*degree(f0,x)):

    if (degree(rdm2,y) <> degree(rdm1,y) + 1) then return R, T, F0 end if:

    Qdm1, fdm1 := Quo_twovar(rdm2, rdm1):
    Rd := map(proc(t) Rem(t, f0, x) mod p end proc, Qdm1.R):
    v := Rd.Vector([[rm1],[r0]]) mod p:

    rd := Extension_twovar_onerelation(Extraction_xaxis(v[2],degree(f0,x), DDx), f0, 2*degree(f0,x)):

    rdm1_trunc := harpoon_y(rdm1, 2*dstar):
    rd_trunc := harpoon_y(rd, 2*dstar-1):

    S, U, F1 := half_gcd_seq(rdm1_trunc, rd_trunc, f0, dstar):

    return map(proc(t) Rem(t, f0, x) mod p end proc, S.Rd), [op(T), Qdm1, op(U)], [op(F0), fdm1, op(F1)]:
end proc:


RecursiveMatrixProduct := proc(T, f0)
description "Compute the product R_k = Q_k...Q_0 with divide and conquer method "
    "for balanced degree computation, with T = [Q_0,Q_1,..., Qk]":
local d, k, R,S:
    k := nops(T):
    if k = 1 then
        return T[1]:
    end if:
    d := floor(k/2):
    R := RecursiveMatrixProduct(T[1..d], f0):
    S := RecursiveMatrixProduct(T[(d+1)..k], f0):
    return map(proc(t) Rem(t, f0, x) mod p end proc, S.R):
end proc:

GuessingBivar := proc(P)
description "P in K[x,y] representing a C-recursive sequence v_{i,j}, the function computes "
    "a minimal Gröbner basis of the ideal of relation I(v) via an extension to "
    "bivariate of the half gcd algorithm. The polynomial P has cofficients on "
    "a (Dx,Dy)-parallelotope with Dx >= 2dx and Dy >= 2dy and x^(dx), y^(dy) in lm(G)":
local Dx, Dy, k, v0, rdm1, r0, f0, R, T, Gx, f, d, j, G, Rj:
    Dx := degree(P,x):
    Dy := degree(P,y):
    k := floor(Dy/2):
    v0 := coeff(P, y^Dy):
    rdm1 := v0*y^(Dy+1):
    r0 := P:
    f0 := GuessingUnivar(v0):
    R, T, Gx := half_gcd_seq(rdm1, r0, f0, k):
    G := [f0]:
    d := degree(f0,x):
    j := 1:
    for f in Gx do
        if (degree(f,x) < d) then
            Rj := RecursiveMatrixProduct(T[1..j], f0):
            G := [op(G), Rem(Rj[1,2]*f, f0, x) mod p]:
            d := degree(f,x):
        end if:
        j := j+1:
    end do:
    G := [op(G), R[2,2]]:
    return G:
end proc:


####################################
###            Context           ###
####################################
p := 65537:
vars := [x,y]:
ord := plex(y,x):                        # y > x
F := [seq(randpoly(vars, dense, degree=1)^5, i=1..2)]:
# Gu := Groebner:-Basis (F,ord, characteristic = p);
leadm := [x^10, x*y,y^5]:
Gu := gblex(leadm, p):
Gux := [seq(lcoeff(Gu[i], y), i = 1..nops(Gu))]:
LMGu := LeadingMonomial(Gu, ord):
Dx:= 10*degree(LMGu[1]):                 #LMGu[1] = x^dx
Dy:= 10*degree(LMGu[-1]):                #LMGu[-1] = y^dy
M:= x^Dx*y^Dy;
Tab := fromGbToRandomSequence(Gu, vars, ord, p):
mon:= sortListMon ([seq (seq (x^i*y^j,j=0..Dy),i=0..Dx)], ord):
P:=from1SetToMirrorTruncatedGeneratingSeries (Tab,vars,mon) mod p:

# ###############################
# # Compute the reduced Gröbner #
# # basis of (u_{i,j})          #
# ###############################
Gres := GuessingBivar(P):
Gres := Basis(Gres,ord, characteristic=p):
if Gu = Gres then
          print("BM_halfgcd_twovar ok"):
else
    print("BM_halfgcd_twovar not ok"):
end if:

