with(LinearAlgebra):
with(Groebner):


EMGCD:= proc (P0,P1,var:='t',p:=65521)
description "Fastly computes the half-gcd matrix of P0 and P1.";
local P2,m,n,B0,C0,B1,C1,M1,DD,EE,QQ,FF,k,G0,H0,G1,H1,M2;
    # if (P1 = 0) then   return <<P0,0>|<1,0>|<0,1>>;
    # elif (P0 = 0) then return <<P1,0>|<0,1>|<1,0>>;
    # end if:
    n := degree (P0,var);
    k := degree (P1,var);
    # if (n < k)   then return <<0,1>|<1,0>>.thisproc (P1,P0,var,p);
    # elif (n = k) then
    #     P2:= Rem (P0,P1,var,'QQ') mod p;
    #     return <<QQ,1>|<1,0>>.EMGCD (P1,P2,var,p);
    # end if:
    m := ceil (n/2);
    if (k < m) then
        return map (expand,<<P0,P1>|<1,0>|<0,1>>) mod p;
    end if:
    B0:= Quo (P0,var^m,var,'C0') mod p;
    B1:= Quo (P1,var^m,var,'C1') mod p;
    M1:= thisproc (B0,B1,var,p);
    DD:= map (expand,M1[1..2,1]*var^m + M1[1..2,2..3].<C0,C1>) mod p;
    EE:= DD[2];
    DD:= DD[1];
    if (degree (EE,var) < m) then
        return map (expand,<<DD,EE>|M1[1..2,2..3]>) mod p;
    end if:
    QQ:= Quo (DD,EE,var,'FF') mod p;
    k := 2*m - degree (EE,var);
    G0:= Quo (EE,var^k,var,'H0') mod p;
    G1:= Quo (FF,var^k,var,'H1') mod p;
    M2:= thisproc (G0,G1,var,p);
    return map (expand, (<M2[1..2,1]*var^k+M2[1..2,2..3].<H0,H1>|
                         M2[1..2,2..3].<<0,1>|<1,-QQ>>.M1[1..2,2..3]>)) mod p;
end proc:

# MD2:= proc (NN,SS,CC,DD,var:='t')
# local k,n,m,M1,EE,FF,M2;
#     if (NN+SS <= 0) then return [0,1,coeff (CC,var,0),coeff (DD,var,0)];
#     end if:
#     k := floor (NN/2);
#     n := NN-k;
#     m := n+SS-1;
#     M1:= thisproc (m,1-SS,rem (DD,var^(NN+SS+1),var),rem (CC,var^(NN+SS+1),var));
#     EE:= rem (expand ((M1[2]*DD-M1[1]*CC)/var^(m+n)),var^(NN+1),var);
#     FF:= rem (expand ((M1[4]*DD-M1[3]*CC)/var^(m+n+1)),var^(NN+1),var);
#     M2:= thisproc (k,0,FF,EE);
#     return expand ([rem (M1[4]*M2[2]-var*M1[2]*M2[1],var^(NN+SS),var),
#                     rem (M1[3]*M2[2]-var*M1[1]*M2[1],var^(NN+1),var),
#                     rem (M1[4]*M2[4]-var*M1[2]*M2[3],var^(NN+SS+1),var),
#                     rem (M1[3]*M2[4]-var*M1[1]*M2[3],var^(NN+1),var)]);
# end proc:

# MD:= proc (n,A,var:='t')
# description "Returns the (n,n) Padé approximant to a (n,n)-normal power "
#     "series or a polynomial of degree 2n.";
#     return MD2 (n,0,A,1,var)[3..4];
# end proc:

AD:= proc (n,a,var:='t',p:=65521)
option remember;
local R0,R1,M,x,y,i;
description "Fastly computes a structured representation of the inverse "
    "of the Toeplitz matrix of size n+1 given by sequence a.\n"
    "If the first coefficient of this matrix is not 0, this representation "
    "is its first column and its first row.";
    R0:= var^(2*n+1);
    R1:= add (a[i+1]*var^i,i=0..2*n);
    M := EMGCD (R0,R1,var,p);
    if (degree (M[2,1],var) < n) then
        error "T is singular";
    end if:
    if (coeff (M[2,3],var,0) <> 0) then
        userinfo (2,AD,"normal case");
        x := [op(PolynomialTools[CoefficientList](LeadingCoefficient
                                                  (M[2,1],tdeg(var))^(-1)*M[2,3],
                                                  var)),
              seq (0,i=1..n+1-degree(M[2,3],var))] mod p;
        R0:= var^(2*n+1);
        R1:= add (a[2*n-i+1]*var^i,i=0..2*n);
        M := EMGCD (R0,R1,var,p);
        y := [op(PolynomialTools[CoefficientList](LeadingCoefficient
                                                  (M[2,1],tdeg(var))^(-1)*M[2,3],
                                                  var)),
              seq (0,i=1..n+1-degree(M[2,3],var))] mod p;
        return x,y;
    else
        userinfo (2,AD,"exceptional case\n");
        R0:= var^(2*n+3);
        R1:= 1+add (a[i+1]*var^(i+1),i=0..2*n)+var^(2*n+2);
        M := EMGCD (R0,R1,var,p);
        if (degree (M[2,1],var) = n+1) then
            userinfo (2,AD,"beta = 1 ok\n");
            x := [op(PolynomialTools[CoefficientList](LeadingCoefficient
                                                      (M[2,1],tdeg(var))^(-1)*M[2,3],
                                                      var)),
                  seq (0,i=1..n+1-degree(M[2,3],var))] mod p;
            R0:= var^(2*n+3);
            R1:= 1+add (a[2*n-i+1]*var^(i+1),i=0..2*n)+var^(2*n+2);
            M := EMGCD (R0,R1,var,p);
            y := [op(PolynomialTools[CoefficientList](LeadingCoefficient
                                                      (M[2,1],tdeg(var))^(-1)*M[2,3],
                                                      var)),
                  seq (0,i=1..n+1-degree(M[2,3],var))] mod p;
            return x,y;
        else
            userinfo (2,AD,"beta = -1 ok\n");
            R0:= var^(2*n+3);
            R1:= 1+add (a[i+1]*var^(i+1),i=0..2*n)-var^(2*n+2);
            M := EMGCD (R0,R1,var,p);
            x := [op(PolynomialTools[CoefficientList](LeadingCoefficient
                                                      (M[2,1],tdeg(var))^(-1)*M[2,3],
                                                      var)),
                  seq (0,i=1..n+1-degree(M[2,3],var))] mod p;
            R0:= var^(2*n+3);
            R1:= -1+add (a[2*n-i+1]*var^(i+1),i=0..2*n)+var^(2*n+2);
            M := EMGCD (R0,R1,var,p);
            y := [op(PolynomialTools[CoefficientList](LeadingCoefficient
                                                      (M[2,1],tdeg(var))^(-1)*M[2,3],
                                                      var)),
                  seq (0,i=1..n+1-degree(M[2,3],var))] mod p;
            return x,y;
        end if:
    end if:
end proc:

ToeplitzSolve:= proc (n,x,y,b,var:='t',p:=65521)
description "Fastly computes z=Ub where U, the inverse of a Toeplitz "
    "matrix of size n+1, is given by the structured representation x and "
    "y, see AD.";
local X,Y,B,P,Q,Z,Xr,Yr,Br,Pr,Qr,i;
    # X := add (x[i+1]*var^i,i=0..n+1);
    # Y := add (y[i+1]*var^i,i=0..n+1);
    # B := add (b[i+1]*var^i,i=0..n);
    # Xr:= add (x[n+2-i]*var^i,i=0..n+1);
    # Yr:= add (y[n+2-i]*var^i,i=0..n+1);
    # Br:= add (b[n+1-i]*var^i,i=0..n);
    X := PolynomialTools:-FromCoefficientList (x,var);
    Y := PolynomialTools:-FromCoefficientList (y,var);
    B := PolynomialTools:-FromCoefficientList (b,var);
    Xr:= PolynomialTools:-FromCoefficientList (x,var,termorder=reverse);
    Yr:= PolynomialTools:-FromCoefficientList (y,var,termorder=reverse);
    Br:= PolynomialTools:-FromCoefficientList (b,var,termorder=reverse);
    P := Rem (expand (Xr*Br),var^(n+1),var) mod p;
    Q := Rem (expand (Y*Br),var^(n+1),var) mod p;
    Pr:= expand (subs ({var=1/var},P)*var^n) mod p;
    Qr:= expand (subs ({var=1/var},Q)*var^n) mod p;
    # Pr:= PolynomialTools:-FromCoefficientList (
    #     PolynomialTools:-CoefficientList (P,var),var,termorder=reverse);
    # Qr:= PolynomialTools:-FromCoefficientList (
    #     PolynomialTools:-CoefficientList (Q,var),var,termorder=reverse);
    Z := Rem (expand ((X*Qr-Yr*Pr)/x[1]),var^(n+1),var) mod p;
    return [op(PolynomialTools[CoefficientList](Z,var)),
            seq (0,i=1..n-degree(Z,var))];
end proc:

ToeplitzInverse:= proc (x,y,t,d,p)
local s1,s2,s3,s4,i;
    s1:= ToeplitzMatrix ([seq (0,0..d-1),seq (coeff (x,t,i),i=0..d)]);
    s2:= ToeplitzMatrix ([seq (coeff (y,t,d-i),i=0..d),seq(0,0..d-1)]);
    s3:= ToeplitzMatrix ([seq (0,0..d),seq (coeff (y,t,d-i),i=0..d-1)]);
    s4:= ToeplitzMatrix ([seq (coeff (x,t,i),i=1..d),seq(0,0..d)]);
    return expand ((s1.s2-s3.s4)/coeff(x,t,0)) mod p;
end proc:

# MDT:= proc (n,a,b,var:='t')
# description "Fastly solves the linear system Tz=b where T is the Toeplitz matrix "
#     "of size n+1 given by sequence a and b is a vector.\n"
#     "Can only work if the polynomial given by a is a (n,n)-normal power "
#     "series, see MD.";
# local UV,x,y,ar,i;
#     UV:= MD (n,add (a[i+1]*t^i,i=0..2*n),var);
#     try
#         x := [op(PolynomialTools[CoefficientList]
#                  (UV[2]/LeadingCoefficient(UV[1],tdeg(var)),var)),0];
#     catch "numeric exception: division by zero":
#         error "not (n,n)-normal";
#     catch:
#         print ("fail");
#     end try:
#     ar:= ListTools[Reverse](a);
#     UV:= MD (n,add (ar[i+1]*t^i,i=0..2*n),var);
#     try
#         y := [op(PolynomialTools[CoefficientList]
#                  (UV[2]/LeadingCoefficient(UV[1],tdeg(var)),var)),0];
#     catch "numeric exception: division by zero":
#         error "not (n,n)-normal";
#     catch:
#         print ("fail");
#     end try:
#     return ToeplitzSolve (n,x,y,b,var);
# end proc:

# testMDT:= proc ()
# local ab,n,T,v,zc,bool;
#     bool:= true;
#     for ab in [[[1,1,2],[3,4]],[[1,1,2,6,24],[0,1,0]],[[1,1,1,2,3,4,5],[5,8,10,14]],
#                [[2,0,0,1,4],[2,1,5]],[[3,0,0,4,10/3],[12,12,12]]] do
#         n := (nops(ab[1])-1)/2;
#         T := ToeplitzMatrix (ab[1]);
#         v := Vector[column] (ab[2]);
#         try
#             zc:= MDT (n,ab[1],ab[2],'t',65521);
#             if (not Equal (T.Vector[column](zc) mod 65521,v))
#             then
#                 printf ("MDT: FAIL Matrix %a and vector %a of size %a\n",T,v,n+1);
#                 bool:= false;
#             end if:
#         catch "not (n,n)-normal":
#             printf (cat(lasterror,"\n"));
#             next;
#         end try:
#     end do;
#     if (bool) then printf ("MDT: SUCCEED\n");
#     end if:
# end proc:

ADT:= proc (n,a,b,var:='t',p:=65521)
description "Fastly solves the linear system Tz=b where T is the Toeplitz matrix "
    "of size n+1 given by sequence a and b is a vector.\n";
local x,y;
    x,y:= AD (n,a,var,p);
    return ToeplitzSolve (n,x,y,b,var,p);
end proc:

testADT:= proc ()
local ab,n,T,v,zc,bool;
    bool:= true;
    for ab in [[[1,1,2],[3,4]],[[1,1,2,6,24],[0,1,0]],[[1,1,1,2,3,4,5],[5,8,10,14]],
               [[2,0,0,1,4],[2,1,5]],[[3,0,0,4,10/3],[12,12,12]]] do
        n := (nops(ab[1])-1)/2;
        T := ToeplitzMatrix (ab[1]);
        v := Vector[column](ab[2]);
        zc:= ADT ((nops(ab[1])-1)/2,ab[1],ab[2],'t',65521);
        if (not Equal (T.Vector[column](zc) mod 65521,v))
        then
            printf ("ADT: FAIL Matrix %a and vector %a of size %a\n",T,v,n+1);
            bool:= false;
        end if:
    end do;
    if (bool) then printf ("ADT: SUCCEED\n");
    end if:
end proc:

HankelADT:= proc (n,a,b,var:='t',p:=65521)
description "Fastly solves the linear system Hz=b where H is the Hankel matrix "
    "of size n+1 given by sequence a and b is a vector.\n";
local x,y;
    return ListTools[Reverse](ADT (n,a,b,var,p));
end proc:

testHankelADT:= proc ()
local ab,n,T,v,zc,bool;
    bool:= true;
    for ab in [[[1,1,2],[3,4]],[[1,1,2,6,24],[0,1,0]],[[1,1,1,2,3,4,5],[5,8,10,14]],
               [[2,0,0,1,4],[2,1,5]],[[3,0,0,4,10/3],[12,12,12]]] do
        n := (nops(ab[1])-1)/2;
        T := HankelMatrix (ab[1]);
        v := Vector[column](ab[2]);
        # zc:= HankelADT ((nops(ab[1])-1)/2,ab[1],ab[2],'t',65521);
        zc:= ListTools[Reverse](ADT ((nops(ab[1])-1)/2,ab[1],ab[2],'t',65521));
        if (not Equal (T.Vector[column](zc) mod 65521,v))
        then
            printf ("ADT: FAIL Matrix %a and vector %a of size %a\n",T,v,n+1);
            bool:= false;
        end if:
    end do;
    if (bool) then printf ("ADT: SUCCEED\n");
    end if:
end proc:
