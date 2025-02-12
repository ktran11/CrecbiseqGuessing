read "bivariate_iterative.mpl":
read "bivariate_recursive.mpl":
read "guessing.mpl":
read "lazard.mpl":
#infolevel[Groebner]:=5:
kernelopts(printbytes=false):
kernelopts(numcpus=1):


####################################
###            Context           ###
####################################
p := 65521;
vars := [x,y];
ord := plex(y,x);                        # y > x
size_Gu := 0:
time_scalar := []:
time_mourrain := []:
time_polscalar := []:
time_BMS := []:
time_half := []:
mon := []:
for i in [seq(k,k=0..50)] do
    mon := [x^i*y^(50-i), op(mon)]:
end do:
Gu := gblex(mon, p):
LMGb := [seq(LeadingMonomial(Gu[i], plex(y,x)), i=1..nops(Gu))]:
if (mon = LMGb) then print("gblex ok"): else print("gblex not ok"): end if:


for k in [seq(10*j, j=1..5)]do
    Tab  := fromGbToRandomSequence(Gu, vars, ord, p);
    Su := StaircasefromGb(Gu, vars, ord):
    lmG := [seq(LeadingMonomial(Gu[i], ord),i=1..nops(Gu))]:
    dx := degree(lmG[1]):
    dy := degree(lmG[-1]):
    Dx:= k*dx:                 #LMGu[1] = x^dx
    Dy:= k*dy:                #LMGu[-1] = y^dy
    word := wdeg([dx+1,1], ['y','x']);
    mon:= sortListMon ([seq (seq (x^i*y^j,j=0..Dy),i=0..Dx)], ord);
    ord := plex(y,x);
    P:=from1SetToMirrorTruncatedGeneratingSeries (Tab,vars,mon);


    # # Call to 'Adpatative Matrix Scalar FGLM'

    # scalar_time := time();
    # r_scalar := AdaptiveMatrixScalarFGLM(Tab, vars, word, nops(Su) +1, p, false):
    # time_scalar := [op(time_scalar), time()- scalar_time];

# # #############################
# # ###    AGbb Mourrain      ###
# # #############################
#     agbb_time := time():
#     AGbb(Tab,vars,mon,word,p):
#     time_mourrain := [op(time_mourrain), time() - agbb_time]:
# # # # ##############################################
# # # # ###    Context  Polynomial ScalarFGLM      ###
# # # # ##############################################
#     polscalar_time := time();
#     AdaptivePolynomialScalarFGLM(Tab, vars, ord, nops(Su) +1,  p, false):
#     time_polscalar := [op(time_polscalar), time() - polscalar_time];

# # # #########################
# # # ###    Context BMS    ###
# # # #########################
#     BMS_time := time():
#     r_bms := BerlekampMasseySakata(Tab, [x,y], word, y^dy, p, true):
#     time_BMS := [op(time_BMS), time() - BMS_time]:
#     # print(time_BMS[-1]):
# #
# # ####################################
# # ###    Context  Polynomial       ###
# # ####################################

# # # # Call to 'Euclid
#     euclid_time := time():
#     G_euclid := BM_Euclid_twovar(P, Dy):
#     time_euclid := [op(time_euclid), time() - euclid_time]:
#     print(time_euclid[-1]):

# Call to 'half-gcd'
    half_time := time();
    G_half := BM_halfgcd_twovar(P, Dy);
    time_half := [op(time_half), time() - half_time];


    print(nops(Gu)*dx*dy, Dx*Dy, sizeGu, time_half[-1]):

end do:


