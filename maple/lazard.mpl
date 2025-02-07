with(Groebner):
with(PolynomialTools):

gblex := proc(mon, p)
description "Gblex from Lazard thm":
local k, dx, dy, dxp, G, F, H,  Hi, i, j, f:
    k := nops(mon):
    dx := [seq(degree(mon[i], x), i = 1..nops(mon))]:
    dy := [seq(degree(mon[i], y), i = 1..nops(mon))]:
    dxp := [seq(dx[i] - dx[i+1], i = 1..nops(dx)-1), dx[nops(dx)]]:
    G := [seq(randpoly(x, coeffs = rand(0..p-1), dense, degree = dxp[i]), i=1..nops(dxp))]:
    H := [1]:
    F := [expand(mul(G)) mod p]:
    for i from 2 to k do
        Hi := y^(dy[i] - dy[i-1])*H[i-1] + randpoly(y, coeffs = proc() randpoly(x, coeffs = rand(0..p-1), dense) end proc, dense, degree = dy[i] - dy[i-1] -1)* H[i-1]:
        for j from max(i-1, nops(H)-4) to nops(H) -1 do
            Hi := randpoly(y, coeffs = proc() randpoly(x, coeffs = rand(0..p-1), dense) end proc, dense, degree = dy[i] - dy[j] -1)*F[j]:
        end do:
        H := [op(H), Rem(Hi, F[1],x) mod p]:
        f := Rem(mul(G[i..nops(G)])*Hi, F[1], x)  mod p:
        F := [op(F), f]:
    end do:
    return Groebner:-Basis(F, plex(y,x), characteristic = p):
end proc:

p := 65537:
vars := [x,y]:
ord := plex(y,x):
mon := [x^6, y*x^5, y^2*x^4, y^3*x^3, y^4*x^2, y^5*x, y^6];
Gb := gblex(mon, p);


# deltax := [seq(30 + 20*i, i=0..7)]:
# GGsimplex := []:
# for j in deltax do
#     mon := []:
#     for i in [seq(k,k=0..j)] do
#         mon := [x^i*y^(j-i), op(mon)]:
#     end do:
#     # dx := degree(mon[1]):
#     # dy := degree(mon[-1]):
#     # print(nops(mon)*dx*dy):
#     Gb := gblex(mon, p):
#     LMGb := [seq(LeadingMonomial(Gb[i], plex(y,x)), i=1..nops(Gb))]:
#     if (mon = LMGb) then print("gblex ok"): else print("gblex not ok"): end if:
#     GGsimplex := [op(GGsimplex), Gb]:
# end do:


# GGL2shape := []:
# deltax := [seq(60 + 80*i, i=0..10)]:
# for j in deltax do
#     mon:= [x^j, x*y, y^(2*j)]:

#     # dx := degree(mon[1]):
#     # dy := degree(mon[-1]):
#     # print(nops(mon)*dx*dy):
#     Gb := gblex(mon,p):
#     GGL2shape := [op(GGL2shape), Gb]:

#     LMGb := [seq(LeadingMonomial(Gb[i], plex(y,x)), i=1..nops(Gb))]:

#     if (mon = LMGb) then print("gblex ok"): else print("gblex not ok"): end if:
# end do:

# GGL3shape := []:
# deltax := [seq(60 + 60*i, i=0..10)]:
# for j in deltax do
#     mon := [x^j, x*y, y^(3*j)]:
#     # dx := degree(mon[1]):
#     # dy := degree(mon[-1]):
#     # print(nops(mon)*dx*dy):

#     Gb := gblex(mon,p):
#     GGL3shape := [op(GGL3shape), Gb]:

#     LMGb := [seq(LeadingMonomial(Gb[i], plex(y,x)), i=1..nops(Gb))]:

#     if (mon = LMGb) then print("gblex ok"): else print("gblex not ok"): end if:
# end do:
