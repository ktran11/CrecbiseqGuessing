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

time_scalar_adaptative := []:
time_BMS := []:
time_mourrain := []:
time_half := []:
size_Gu := 0:
size_stair := []:

#############
#  Simplex  #
#############

deltax := [seq(30 + 20*i, i=0)]:
GGsimplex := []:
for j in deltax do
    mon := []:
    for i in [seq(k,k=0..j)] do
        mon := [x^i*y^(j-i), op(mon)]:
    end do:
    # dx := degree(mon[1]):
    # dy := degree(mon[-1]):
    # print(nops(mon)*dx*dy):
   Gb := gblex(mon, p):
 	LMGb := [seq(LeadingMonomial(Gb[i], plex(y,x)), i=1..nops(Gb))]:
  # if (mon = LMGb) then print("gblex ok"): else print("gblex not ok"): end if:
   GGsimplex := [op(GGsimplex), Gb]:
end do:

############
#  Lshape2 #
############
# GGL2shape := []:
# deltax := [seq(60 + 80*i, i=0..5)]:
# for j in deltax do
#     mon:= [x^j, x*y, y^(2*j)]:

#     # dx := degree(mon[1]):
#     # dy := degree(mon[-1]):
#     # print(nops(mon)*dx*dy):
#     Gb := gblex(mon,p):
#     GGL2shape := [op(GGL2shape), Gb]:

#     LMGb := [seq(LeadingMonomial(Gb[i], plex(y,x)), i=1..nops(Gb))]:

#     #   if (mon = LMGb) then print("gblex ok"): else print("gblex not ok"): end if:
# end do:

GGset := [op(GGsimplex), op(GGL2shape)]:

for Gu in GGsimplex do
    sizeGu:= 0 :
    for f in Gu do
        sizeGu := sizeGu + nops(f):
    end do:
    Tab  := fromGbToRandomSequence(Gu, vars, ord, p);
    lmG := [seq(LeadingMonomial(Gu[i], ord),i=1..nops(Gu))]:
    Su := fromGbToStaircase(vars, lmG, ord):
    size_stair := [op(size_stair), nops(Su)]:

    dx := degree(lmG[1]):
    dy := degree(lmG[-1]):
    Dx:= 2*dx:                 #LMGu[1] = x^dx
    Dy:= 2*dy:                #LMGu[-1] = y^dy
    word := wdeg([dx+1,1], ['y','x']);
    mon:= sortListMon ([seq (seq (x^i*y^j,j=0..Dy),i=0..Dx)], ord);
    P:=from1SetToMirrorTruncatedGeneratingSeries (Tab,vars,mon);
    atemp := [op(Su), op(lmG)]:
    a := sortListMon([op({seq(seq(atemp[i]*atemp[j], i=1..j), j=1..nops(atemp))})],ord):

#     ####################################
#     ###      Context  Linear         ###
#     ####################################

    # # Call to 'Adpatative Matrix Scalar FGLM'

#     scalar_time := time();
#      AdaptiveMatrixScalarFGLM(Tab, vars, word, nops(Su) +1, p, false):
# #    print(r_scalar):
#      time_scalar_adaptative := [op(time_scalar_adaptative), time()- scalar_time];

# #############################
# ###    AGbb Mourrain      ###
# #############################
    agbb_time := time():
    b,c,p,m,q,k,d := AGbb(Tab,vars,a,ord,p):
    time_mourrain := [op(time_mourrain), time() - agbb_time]:
# ##############################################
# ###    Context  Polynomial ScalarFGLM      ###
# ##############################################
    # polscalar_time := time();
    # AdaptivePolynomialScalarFGLM(Tab, vars, ord, nops(Su) +1,  p, false):
    # time_polscalar := [op(time_polscalar), time() - polscalar_time];


# # #########################
# # ###    Context BMS    ###
# # #########################
    # BMS_time := time():
    # BerlekampMasseySakata(Tab, [x,y], word, y^dy, p, false):
    # time_BMS := [op(time_BMS), time() - BMS_time]: #


# # ####################################
# # ###    Context  Polynomial       ###
# # ####################################

# # # # # Call to 'Euclid'
# # # #     euclid_time := time():
# # # #     G_euclid := BM_Euclid_twovar(P, Dy):
# # # #     time_euclid := [op(time_euclid), time() - euclid_time]:


#    Call to 'half-gcd'
    # half_time := time();
    # G_half := GuessingBivar(P);
    # time_half := [op(time_half), time() - half_time];

    print(nops(Gu)*dx*dy, Dx*Dy, sizeGu, time_mourrain[-1]):
end do:


