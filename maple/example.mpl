read "bivariate_recursive.mpl":

####################################
###            Context           ###
####################################
p := 97;
vars := [x,y];
ord := plex(y,x);                        # y > x

lmGu:= [x^5, x^3*y, x^2*y^2, y^3]:
Gu := gblex(lmGu, p):
lprint(map(proc(i) sort(i, order = ord) end proc, Gu)):
dx := 5;
dy := 3;
Dx := 2*dx;
Dy := 2*dy;
mon := sortListMon ([seq (seq (x^i*y^j,j=0..Dy),i=0..Dx)], ord):
Tab := fromGbToRandomSequence(Gu, vars, ord, p):


# pseudo-Euclidean algorithm

# Input of Algorithm 3 GuessingBivar(𝒖)
r0 := sort(from1SetToMirrorTruncatedGeneratingSeries (Tab,vars,mon) mod p, order = ord):
lprint(FromCoefficientList(CoefficientList(r0,y,termorder=reverse), y, termorder=reverse)):
rm1 := lcoeff(r0, y)*y^(Dy+1);

# # Compute the C-relation f_0 on the first slice u_{\ast, 0}
lr0 := lcoeff(r0,y):
f0 :=  GuessingUnivar(lr0):
lprint(f0):
d0 := degree(f0,x):

# # partial pseudo-Euclidean division a_0 = -1
a0 := -1;
r1temp := expand(y*r0 + a0 * rm1) mod p;
lprint(FromCoefficientList(CoefficientList(r1temp,y,termorder=reverse), y, termorder=reverse)):

# # use Hankel solver to find b_0
lr1temp := lcoeff(r1temp,y):
vectr0 := [seq(coeff(lr0, x, degree(lr0,x) - i), i=0..2*(d0 -1))]:
vectr1 := [seq(coeff(lr1temp, x, degree(lr1temp,x) - i), i=0..d0-1)]:
vectb0 := HankelADT(d0-1, vectr0, vectr1, x, p):
b0 := 0:
for i from 1 to d0 do
           b0 := b0 + vectb0[i] * x^(i-1) mod p:
end do:

Q0 := Matrix([[0, 1], [a0 mod p, y-b0 mod p]]);

r1 :=  Extraction_xaxis((y-b0)*r0+a0*rm1 mod p, d0, Dx):
r1 := sort(expand(Extension_twovar_onerelation(r1, f0, Dx)) mod p, order = ord);
lprint(FromCoefficientList(CoefficientList(r1,y,termorder=reverse), y, termorder=reverse)):

lr1 := lcoeff(r1,y):

Q1,f1 := Quo_twovar(r0, r1);
r2 := Extraction_xaxis(Q1[2,1]*r0 + Q1[2,2]*r1, d0,Dx):
r2 := sort(expand(Extension_twovar_onerelation(r2, f0, Dx) mod p), order = ord);
lprint(FromCoefficientList(CoefficientList(r2,y,termorder=reverse), y, termorder=reverse)):


Q2,f2 := Quo_twovar(r1, r2);
r3 := Extraction_xaxis(Q2[2,1]*r1 + Q2[2,2]*r2, d0,Dx):
r3 := sort(expand(Extension_twovar_onerelation(r3, f0, Dx) mod p), order = ord);
lprint(FromCoefficientList(CoefficientList(r3,y,termorder=reverse), y, termorder=reverse)):


Q10 := map(proc(t) sort(expand(Rem(t, f0, x) mod p), order = ord) end proc, Q1.Q0):
t1 := Q10[1,2];
g1 := sort(expand(Rem(t1*f1, f0, x) mod p), order = ord);

Q20 := map(proc(t) sort(expand(Rem(t, f0, x) mod p), order = ord) end proc, Q2.Q1.Q0):
t2 := Q20[1,2];
g2 := sort(expand(Rem(t2*f2, f0, x) mod p), order = ord);

tdy := Q20[2,2];

G := [f0, g1, g2, tdy];

Gb := Basis(G, ord, characteristic = p);
