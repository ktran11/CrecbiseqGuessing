with(LinearAlgebra):
with(Groebner):
truediff:=false:
kernelopts(printbytes=false):


########################
# Secondary procedures #
########################

redp:= proc (x,p)
description "Reduces x mod p if p <> 0, does nothing otherwise.";
    if (p = 0) then return x;
    else return x mod p;
    end if;
end proc:

listVar:= proc (n, s:='x')
description "Makes a list of n variables from string s.";
local i:
    ASSERT (n > 0, "n must be positive");
    if (n = 1) then return [s];
    else return [seq (cat (s,i), i=1..n)];
    end if:
end proc:

orderComparison:= proc (mon_ord)
description "Makes a monomial comparison function from monomial ordering "
    "mon_ord.";
    return (a,b) -> TestOrder (a,b,mon_ord);
end proc:

sortListMon:= proc (L, mon_ord)
description "Sorts the list of monomials L for mon_ord.";
    return sort (L, orderComparison (mon_ord));
end proc:

listMonLessOrEqualThan:= proc (var,mon_ord,max_mon)
description "Makes a sorted list of all the monomials in var up to max_mon for "
    "mon_ord. \n"
    "Parameter mon_ord should not be an elimination ordering!";
local L,LL,M,i,cmp,m,x:
    M:= Matrix (MatrixOrder (mon_ord,var));
    for i from 1 to nops(var) do
        ASSERT (M[1,i] > 0, "No elimination ordering!");
    end do:
    L  := [];
    LL := [1];
    cmp:= orderComparison (mon_ord);
    while (LL <> {}) do
        L := {op(L),op(LL)};
        LL:= {seq (seq (`if` (cmp (m*x,max_mon),m*x,NULL), x in var),
                   m in LL)}:
    end do:
    return sortListMon ([op(L)], mon_ord);
end proc:

listMonOfDegreeLessOrEqualThan:= proc (var,mon_ord,max_deg)
description "Makes a sorted list of all the monomials in var of degree "
    "up to max_deg for mon_ord.";
local L,LL,i,cmp,m,x:
    L  := [];
    LL := [1];
    while (LL <> {}) do
        L := {op(L),op(LL)};
        LL:= {seq (seq (`if` (degree (m,var)<max_deg,m*x,NULL), x in var),
                   m in LL)}:
    end do:
    return sortListMon ([op(L)], mon_ord);
end proc:

MinkowskiSum:= proc (mon_ord,set_mon1,set_mon2:=set_mon1)
description "Makes the sorted for mon_ord MinkowskiSum of the two sets of terms "
    "set_mon1 and set_mon2.";
local L,t,u;
    L:= {seq (seq (t*u, u in set_mon2), t in set_mon2)};
    return sortListMon ([op(L)], mon_ord);
end proc:

firstIndependentRows:= proc (M,p:=0,max_rank:=min(Dimension(M)))
option remember:
description "Returns the first independent rows of M with a naive "
    "complexity in O(n^3).";
local N, i, j, k, col_pivot, inv_pivot, m, n, r, rows;
    userinfo (1,firstIndependentRows,`*** Matrix`, convert (M,string),
              `in charistic`, p, `***`);
    m,n:= Dimension (M);
    N:= redp (Matrix (M),p);
    col_pivot:= Array ([seq (0, i=1..m)]);
    r:= 0; i:=1;
    while (r <> max_rank and i <= m) do
        j:= 1;
        while (j <= n and N[i,j] = 0) do j:= j+1;
        end do:
        if (j <= n) then
            userinfo (2,firstIndependentRows,`***\t New independent row`, i,
                      `***`);
            col_pivot[i]:= j; inv_pivot:= redp (N[i,j]^(-1),p);
            r:= r+1;
            for k from i+1 to m do
                N[k,1..n]:= redp (N[k,1..n]-(inv_pivot*N[k,j])*N[i,1..n],p);
            end do:
        end if:
        i:= i+1;
    end do:
    rows:= Array ([seq (`if` (col_pivot[i]=0,NULL,i), i=1..m)]);
    userinfo (1,firstIndependentRows,`*** Rank`, r, `with rows`,
              convert (rows,list));
    return rows,r;
end proc:

firstIndependentColumns:= proc (M,p:=0,max_rank:=min(Dimension(M)))
description "Returns the first independent columns of M with a naive "
    "complexity in O(n^3).";
option remember:
    return firstIndependentRows (Transpose (M),p,max_rank);
end proc:

staircaseStabilization:= proc (S,vars,mon_ord)
description "Returns the full minimal staircase containing S, "
    "i.e. the set of all divisors of elments in S, sorted for mon_ord.";
local Sp,s,v,T,d,e:
    if (S = [1]) then return S:
    end if:
    Sp:= {1}:
    for v in vars do
        T:= {}:
        for s in Sp do
            d:= max (map (t->degree (t,v), select (u->divide (u,s),S))):
            T:= T union {seq (s*v^e, e=0..d)}:
        end do:
        Sp:= Sp union T:
    end do:
    return sortListMon ([op(Sp)], mon_ord);
end proc:

sparseStaircaseStabilization:= proc (S,set_mon,lattice_mon,mon_ord)
description "Returns the full minimal staircase containing S, "
    "i.e. the set of all divisors of elments in S, sorted for mon_ord.";
local Sp,s,v,T,d,e:
    if (S = [1]) then return S:
    end if:
    Sp:= {1}:
    for v in vars do
        T:= {}:
        for s in Sp do
            d:= max (map (t->degree (t,v), select (u->divide (u,s,'q') and
                                                   q in lattice_mon,S))):
            T:= T union select (m->m in set_mon, {seq (s*v^e, e=0..d)}):
        end do:
        Sp:= Sp union T:
    end do:
    return sortListMon ([op(Sp)], mon_ord);
end proc:

staircaseMaximum:= proc (S,var,mon_ord)
description "Returns the maximal for | elements of the staircase S.";
local maxStaircase, maxSpan,s,t,isMax,i,cmp;
    maxStaircase:= [];
    maxSpan     := [];
    cmp         := orderComparison (mon_ord);
    for s in S do
        isMax:= true;
        for t in S do
            if (s[2] <> 0 and divide (t[2],s[2],'q') and q <> 1) then
                isMax:= false; break;
            end if:
        end do:
        if isMax then
            if not s[2] in maxSpan then
                maxStaircase:= [op(maxStaircase), s];
                maxSpan     := [op(maxSpan), s[2]];
            else
                for i from 1 to nops(maxStaircase) do
                    if (cmp(s[1],maxStaircase[i][1])) then
                        maxStaircase[i]:= c; break;
                    end if:
                end do:
            end if:
        end if:
    end do:
    return maxStaircase;
end proc:

fromStaircaseToGb:= proc (S,var,mon_ord)
local G,s,v;
    if (S = []) then return [1];
    end if:
    G:= [op({seq (seq (v*s, v in var), s in S)} minus {op(S)})];
    return InterReduce (G,mon_ord);
end proc:

fromGbToStaircase:= proc (vars,lmG,mon_ord)
local S,v,d,T,s,g,e:
    if (1 in lmG) then return []:
    end if:
    S:= [1]:
    for v in vars do
        T:=S:
        for s in S do
            g:=select (gg->divide (s,subs ({v=1},gg)),lmG):
            if (g <> []) then d:= min (op(map(gg->degree (gg,v)-1,g))):
            else error "BUG staircase":
            end if:
            T:= [op(T),seq (s*v^e,e=1..d)]:
        end do:
        S:= T:
    end do:
    return S:
end proc:

getRows_mon:= proc (all_mon,cols_mon)
description "Returns the maximal ordered set U such that cols_mon "
    "+ U is included in all_mon";
local rows_mon, AM;
    AM      := {op(all_mon)};
    rows_mon:= select (m->{op(expand (m*cols_mon))} subset AM,all_mon);
    return rows_mon;
end proc:

nfLeftPart:= proc (r,var,L,mon_ord,p)
local tmp,i;
    if (L = []) then
        if (r[2] <> 0) then return redp (expand (r/LeadingCoefficient (r[2],mon_ord)),p);
        else                return redp (expand (r),p);
        end if:
    end if:
    NormalForm (expand (r)[1],map (l->l[1],expand (L)),mon_ord,'q',characteristic=p):
    tmp:= redp (expand (r - add (q[i]*L[i],i=1..nops(L))),p);
    if (tmp[2] <> 0) then
        tmp:=redp (expand (tmp/LeadingCoefficient (tmp[2],mon_ord)),p);
    end if:
    try:
        tmp[1]:= sort (tmp[1],order=mon_ord);
        tmp[2]:= sort (tmp[2],order=mon_ord);
    catch:
    end try:
    return tmp;
end proc:

nfRightPart:= proc (r,var,L,mon_ord,p)
local res;
    res:= nfLeftPart ([r[2],r[1]],var,map (l->[l[2],l[1]],L),mon_ord,p);
    return nfLeftPart ([res[2],res[1]],var,[],mon_ord,p):
end proc:

leftHigherPart:= proc (r,var,M,G,mon_ord)
description "Remove all the monomials of r that can divide monomials M/g for g in G";
local tmp,i;
    if (G = []) then return r;
    end if:
    tmp:= expand (mirrorPolynomial (r,var,M));
    tmp:= NormalForm (tmp,G,mon_ord);
    return expand (mirrorPolynomial (tmp,var,M));
end proc:

nfLeftHigherPart:= proc (r,var,L,M,G,mon_ord,p)
local tmp,rHP,LHP,i;
    if (L = []) then
        if (r[2] <> 0) then return redp (expand (r/LeadingCoefficient (r[2],mon_ord)),p);
        else                return redp (expand (r),p);
        end if:
    end if:
    rHP:= [leftHigherPart (r[1],var,M,G,mon_ord),r[2]];
    LHP:= map (l->[leftHigherPart (l[1],var,M,G,mon_ord),l[2]],L);
    NormalForm (expand (rHP)[1],map (l->l[1],expand (LHP)),mon_ord,'q',characteristic=p):
    tmp:= redp (expand (r - add (q[i]*L[i],i=1..nops(L))),p);
    if (tmp[2] <> 0) then
        tmp:=redp (expand (tmp/LeadingCoefficient (tmp[2],mon_ord)),p);
    end if:
    try:
        tmp[1]:= sort (tmp[1],order=mon_ord);
        tmp[2]:= sort (tmp[2],order=mon_ord);
    catch:
    end try:
    return tmp;
end proc:

orthProj:= proc (f,p,m,n,b,xvar,Tab,myprime:=0)
local g,xalph;
    g:= f;
    for xalph in b do
        g:= redp (g - fromPolToTabRelation (Tab,xvar,g*m[xalph])*p[xalph],myprime);
    end do:
    return g;
end proc:

nnext:= proc (n,xvar,b,d,c,s)
local nn,a,bb,i;
    nn:= [op({seq (seq (bb*xvar[i],i=1..n), bb in b)})];
    nn:= remove (i->(i in b),nn);
    nn:= select (i->(i in s),nn);
    nn:= remove (i->(i in d),nn);
    a := {op(b)} union {op(d)} union {op(s)};
    nn:= select (i->({op(expand (i*c))} subset (a)),nn);
    return nn;
end proc:

# return 1st  monomial s such that s*R fails, -1 if no such monomial exists.
# return last monomial s such that s*R has been tested.
FailingWhenShiftedBy:= proc (R,all_mon,lcm_mon,mon_ord,B,rows_mon)
local xvar, cols_mon, lm1, lm2, shift_rows,i,j,c,m;
    xvar      := [op(indets (lcm_mon))];
    lm1       := LeadingMonomial (R[1],mon_ord);
    lm2       := LeadingMonomial (R[2],mon_ord);
    coeffs (R[2],xvar,'cols_mon');
    cols_mon  := [cols_mon];
    # shift_rows:= map (a->a/lm2,select (b->divide (b,lm2),all_mon));
    shift_rows:= map (a->ifelse (divide (a,lm2,'q'),q,NULL),all_mon);
    shift_rows:= select (a->map (b->b*a,{op(cols_mon)}) subset {op(all_mon)},
                         shift_rows);
    shift_rows:= sort ([op({op(shift_rows)} union {op(rows_mon)})],
                       (a,b)->TestOrder (a,b,mon_ord));
    shift_rows:= [0,op(shift_rows)];
    for i from 2 to nops(shift_rows) do
        m:= lcm_mon/shift_rows[i];
        c:= R[1];
        for j from 1 to nops(xvar) do c:= coeff (c,xvar[j],degree (m,xvar[j]));
        end do:
        if (c <> 0) then
            return shift_rows[i],shift_rows[-1];
        end if:
    end do:
    # printf ("%a\n", rows[-1]);
    return -1,shift_rows[-1];
end proc:

####################
# Table procedures #
####################

fromMonToTabElem:= proc (Tab,var,m)
description "Returns the table element of Tab corresponding to monomial "
    "m.\n"
    "For instance, if m=x^i*y^j and var=[x,y,z], it will return Tab(i,j,0).";
local v:
    return Tab(seq (degree (m,v), v in var));
end proc:

fromPolToTabRelation:= proc (Tab,var,P)
description "Evaluates the polynomial P at the table Tab by "
    "replacing every monomial by its corresponding table element.\n"
    "See fromMonToTabElem.";
local c,m,size,i;
    c:= [coeffs (expand (P),var,'m')];
    m:= [m];
    size:= nops(c);
    return add (c[i]*fromMonToTabElem (Tab,var,m[i]), i=1..size);
end proc:

testRelation:= proc (Tab,var,mon_ord,P,shift_mon,p:=0,errors:=false)
description "Evaluates P and its shifts for the monomial ordering mon_ord, "
    "at table Tab, allowing the user to test P as a valid relation.\n"
    "If P fails, errors set to true allows the user to get the failing "
    "shifting monomials.\n"
    "See fromPolToTabRelation.";
local s;
    s:= map (u->`if`(redp (fromPolToTabRelation (Tab,var,P*u),p) <> 0,u,NULL),
             shift_mon);
    if (s = []) then return true,`if`(errors,[],NULL);
    else return false,`if`(errors,s,NULL);
    end if:
end proc:

testGb:= proc (Tab,var,mon_ord,G,shift_mon,p:=0,errors:=false)
description "Evaluates the polynomials of G and their shifts "
    "for monomial ordering mon_ord, at table Tab, allowing the user to test G "
    "as a valid "
    "GrÃ¶bner basis of relations.\n"
    "If G fails, errors set to true allows the user to get the failing "
    "shifting monomials.\n"
    "See testRelation.";
local B,b;
    B:= map (g->[testRelation (Tab,var,mon_ord,g,shift_mon,p,errors)], G);
    for b in B do
        if (not b[1]) then return false,`if`(errors,map(m->m[2],B),NULL);
        end if:
    end do:
    return true,`if`(errors,[],NULL);
end proc:

from2SetsToMultiHankelMatrix:= proc (Tab,var,rows_mon,cols_mon:=rows_mon)
description "Makes the multi-Hankel matrix of Tab for sets of terms cols_mon "
    "and rows_mon.";
    return Matrix (nops(rows_mon), nops(cols_mon),
                   (i,j)-> fromMonToTabElem (Tab,var,cols_mon[j]*rows_mon[i]));
end proc:

mirrorPolynomial:= proc (P,var,M)
description "Makes the mirror of polynomial P in variables var.\n"
    "M is the monomial mapped to 1 and should be a multiple of the lcm of "
    "the support of P for the result to be a polynomial.";
    return expand (M * subs (map (v->v=1/v, var),P));
end proc:

from1SetToTruncatedGeneratingSeries:= proc (Tab,var,set_mon)
description "Makes the truncated generating series of Tab for set of terms set_mon.";
local t:
    return add (fromMonToTabElem (Tab,var,t)*t, t in set_mon);
end proc:

from1SetToMirrorTruncatedGeneratingSeries:= proc (Tab,var,set_mon)
description "Makes the miror of the truncated generating series of Tab for "
    "set of terms set_mon.";
    return mirrorPolynomial (from1SetToTruncatedGeneratingSeries (Tab,var,set_mon),var,
                             lcm(op(set_mon)));
end proc:

from2SetsToTruncatedGeneratingSeries:= proc (Tab,var,set_mon1,set_mon2:=set_mon1)
description "Makes the truncated generating series of Tab for set of terms "
    "set_mon1 + set_mon2.";
local all_mon,t,u;
    all_mon:= [op({seq (seq (t*u, t in set_mon1), u in set_mon2)})];
    return from1SetToTruncatedGeneratingSeries (Tab,var,all_mon);
end proc:

from2SetsToMirrorTruncatedGeneratingSeries:= proc (Tab,var,set_mon1,set_mon2:=set_mon1)
description "Makes the miror of the truncated generating series of Tab for "
    "set of terms set_mon1 + set_mon2.";
    return mirrorPolynomial (from2SetsToTruncatedGeneratingSeries (Tab,var,
                                                                   set_mon1,set_mon2),
                             var,lcm(op(set_mon1))*lcm(op(set_mon2)));
end proc:


fromGbToRandomSequence:= proc (G,vars,mon_order,p:=mychar)
description "Returns a random table in characteristic p"
    "whose ideal of relations is <G>"
    "if <G> is Gorenstein or contains <G> otherwise.";
local Tab,lmG,remG,roll,i;
    lmG := map (g->Groebner:-LeadingMonomial (g,mon_order), G);
    remG:= [seq (redp (lmG[i]-G[i], p),i=1..nops(G))];
    roll:= `if`(p=0,rand(-2^16..2^16-1),rand(0..p-1));
    Tab := proc ()
    option remember;
    local idx,m,i;
        idx:= [_passed];
        m  := mul (vars[i]^idx[i],i=1..nops(idx));
        for i from 1 to nops (lmG) do
            if divide (m,lmG[i],'q') then
                return fromPolToTabRelation (thisproc,vars,q*remG[i],p);
            end if:
        end do:
        return roll ();
    end proc;
    return Tab;
end proc:


###################
# Main procedures #
###################

BerlekampMasseySakata:= proc (Tab,var:=['x','y'],mon_ord:=tdeg(op(var)),
                              max_mon:=var[1]^10,p:=0,full_answer:=false)
description "Compute the minimal relation satisfied by Tab for all the monomials "
    "up to max_mon in characteristic p.\n"
    "If full_answer is set to true, returns a set of triplets [m,r,s] where\n"
    "- m is a monomial;\n"
    "- r is a relation with leading monomial m;\n"
    "- s is the shift of the relation, that is up to which monomial "
    "it has been tested.\n"
    "Otherwise returns a set of r only.";
local R,shift,F,fail,list_mon,toTest,discrepancy,cmp,mon,staircase,newStaircase,
    Gb,g,r,i,j,k;
    R:= [[1,1,0]]; F:=[];
    list_mon:= listMonLessOrEqualThan (var,mon_ord,max_mon);
    cmp     := orderComparison (mon_ord);
    userinfo (1,BerlekampMasseySakata,`*** Tab `, Tab,
              `in variable`, var, `up to`, max_mon,
              `in characteristic`, p, `***`);
    userinfo (2,BerlekampMasseySakata,`***\t New potential relation`, 1, `***`);
    for mon in list_mon do
        userinfo (1,BerlekampMasseySakata,mon);
        newStaircase:= F;
        toTest     := select (r->divide (mon,r[1]),R);
        shift      := map (r->mon/r[1],toTest);
        discrepancy:= [seq (redp (fromPolToTabRelation (Tab,var,
                                                        expand (toTest[i][2]*shift[i])),
                                  p),i=1..nops(toTest))];
        for i from 1 to nops (toTest) do
            if (discrepancy[i] <> 0) then
                newStaircase:= [op(newStaircase),[redp (toTest[i][2]/discrepancy[i],p),
                                                  shift[i]]];
            else
                R[i][3]:= shift[i];
            end if:
        end do:
        newStaircase:= staircaseMaximum (newStaircase,var,mon_ord);
        Gb          := fromStaircaseToGb (map (s->s[2],newStaircase),var,mon_ord);
        for i from 1 to nops(Gb) do
            g:= Gb[i];
            Gb[i]:= [g,g,0];
            for r in R do
                if (divide (g,r[1],'quogr')) then break;
                end if:
            end do:
            if (not divide (mon,g,'quomong')) then
                Gb[i][2]:= expand (quogr*r[2]);
                Gb[i][3]:= 0;
                j:= 0;
                while (cmp (list_mon[j+1]*g,mon)) do
                    j:= j+1;
                end do:
                if (j <> 0) then Gb[i][3]:= list_mon[j];
                end if:
            else
                for j from 1 to nops (F) do
                    if (divide (F[j][2],quomong,'quofailquomong')) then
                        Gb[i][2]:= redp (expand (quogr*r[2]
                                                 -fromPolToTabRelation (Tab,var,
                                                                        r[2]*mon/r[1])*
                                                 quofailquomong*F[j][1]),p);
                        Gb[i][3]:= quomong;
                        break;
                    end if:
                end do:
                if (j = nops(F)+1) then
                    Gb[i][2]:= r[2];
                    Gb[i][3]:= quomong;
                end if:
            end if:
        end do:
        i:= 1; j:= 1; k:=1;
        while (i <= nops (toTest) and j <= nops (Gb)) do
            if (cmp (toTest[i][1],Gb[j][1])) then
                userinfo (2,BerlekampMasseySakata,`***\t`,toTest[i][2],`***`);
                userinfo (2,BerlekampMasseySakata,
                          `if`(discrepancy[i] = 0,
                               `***\t SUCCEEDS with a shift`,
                               `***\t FAILS with a shift`),
                          shift[i],`***`);
                if (toTest[i][1] = Gb[j][1]) then
                    if (toTest[i][2] <> Gb[j][2]) then
                        userinfo (2,BerlekampMasseySakata,
                                  `***\t\t but tweaked to`, Gb[j][2],`***`);
                    end if:
                    j:= j+1;
                else
                    userinfo (2,BerlekampMasseySakata,
                              `***\t\t and is discarded ***`);
                end if:
                i:= i+1;
                k:= k+1;
            else
                while (k <= nops (R) and not cmp (Gb[j][1],R[k][1])) do
                    k:= k+1;
                end do:
                if (Gb[j][1] <> R[k][1]) then
                    userinfo (2,BerlekampMasseySakata,`***\t New potential relation in`,
                              Gb[j][1],`\n`,Gb[j][2],`***`);
                end if:
                j:= j+1;
            end if:
        end do:
        while (i <= nops (toTest)) do
            userinfo (2,BerlekampMasseySakata,`***\t`,toTest[i][2],`***`);
            userinfo (2,BerlekampMasseySakata,
                      `if`(discrepancy[i] = 0,
                           `***\t SUCCEEDS with a shift`,
                           `***\t FAILS with a shift`),
                      shift[i],`***`);
            i:= i+1;
        end do:
        while (j <= nops (Gb)) do
            while (k <= nops (R) and not cmp (Gb[j][1],R[k][1])) do
                k:= k+1;
            end do:
            if (k > nops (R) or Gb[j][1] <> R[k][1]) then
                userinfo (2,BerlekampMasseySakata,`***\t New potential relation in`,
                          Gb[j][1],`\n`,Gb[j][2],`***`);
            end if:
            j:= j+1;
        end do:
        R:= Gb;
        F:= newStaircase;
    end do:
    if (full_answer) then
        return R;
    else
        return map (g->g[2],R);
    end if:
end proc:

MatrixScalarFGLM:= proc (Tab,var:=['x','y'],mon_ord:=tdeg(op(var)),
                         cols_mon:=listMonLessOrEqualThan (var,mon_ord,var[1]^10),
                         rows_mon:=cols_mon,
                         lattice_mon:=cols_mon,p:=0,
                         full_answer:=false)
description "Compute the minimal relation satisfied by Tab for all the monomials "
    "in cols_mon + rows_mon in characteristic p."
    "If full_answer is set to true, returns a set of triplets [m,r,s] where\n"
    "- m is a monomial;\n"
    "- r is a relation with leading monomial m;\n"
    "- s is the shift of the relation, that is up to which monomial "
    "it has been tested.\n"
    "Otherwise returns a set of r only.";
local H,firstIndRows,usefulStaircase,fullStaircase,firstIndCols,
    subH,next_mon,R,rank,col_next_mon,i;
    userinfo (1,ScalarFGLM,`*** Tab `, Tab,
              `in variable`, var, `up to`, cols_mon[-1],`and`,rows_mon[-1],
              `in characteristic`, p, `***`);
    H                := from2SetsToMultiHankelMatrix (Tab,var,rows_mon,cols_mon);
    firstIndRows,rank:= firstIndependentRows (H,p,min(Dimension(H)));
    if (rank = 0) then
        if (full_answer) then
            return [1,1,rows_mon];
        else
            return 1;
        end if:
    end if:
    if (rows_mon = cols_mon) then
        firstIndCols:= firstIndRows;
    else
        firstIndCols,rank:= firstIndependentColumns (H,p,rank);
    end if:
    firstIndRows     := convert (firstIndRows,list);
    firstIndCols     := convert (firstIndCols,list);
    usefulStaircase:= map (m->cols_mon[m], firstIndCols);
    userinfo (2,ScalarFGLM,`Useful staircase`, usefulStaircase);
    fullStaircase  := sparseStaircaseStabilization (usefulStaircase,cols_mon,
                                                    lattice_mon,mon_ord);
    userinfo (2,ScalarFGLM,`Staircase`, fullStaircase);
    next_mon    := [op({op(cols_mon)} minus {op(fullStaircase)})];
    next_mon    := InterReduce (next_mon,mon_ord);
    subH        := H[firstIndRows,firstIndCols];
    col_next_mon:= from2SetsToMultiHankelMatrix (Tab,var,
                                                 map (i->rows_mon[i],firstIndRows),
                                                 next_mon);
    if (p = 0) then
        R:= LinearSolve (subH,col_next_mon);
    elif (p < 2^32) then
        subH        := LinearAlgebra[Modular][Mod] (p,subH,integer[8]);
        col_next_mon:= LinearAlgebra[Modular][Mod] (p,col_next_mon,integer[8]);
        R           := LinearAlgebra[Modular][LinearSolve] (p,<subH|col_next_mon>,
                                                            nops(next_mon),
                                                            inplace=false);
    else
        subH        := subH mod p;
        col_next_mon:= col_next_mon mod p;
        R           := LinearSolve (subH,col_next_mon) mod p;
    end if:
    R       := [seq (redp (next_mon[i] - DotProduct (Column (R,i),usefulStaircase),p),
                     i=1..nops(next_mon))];
    userinfo (2,ScalarFGLM,`***\t New potential relations`, R, `***`);
    if (full_answer) then
        return [seq ([next_mon[i], R[i], rows_mon],i=1..nops(next_mon))];
    else
        return R;
    end if:
end proc:

AGbb:= proc (Tab,xvar,a,mon_order,myprime)
local b,m,mm,c,d,cc,nn,s,t,l,p,q,k,n;
local xalph,palph,xgam,xgam_palph,malph,xgam_palphEval,boolgam,supp;
    n:= nops(xvar):
    b:=[];
    c:=[];
    d:= [];
    nn:=[1];
    s:= a;
    t:= a;
    p:= table ([]); q:= table ([]); k:= table ([]);
    userinfo (2,AGbb,`set of terms`,nn);
    while (nn <> []) do
        for xalph in nn do
            userinfo (1,AGbb,`xalpha`,xalph);
            palph:= orthProj (xalph,p,m,n,b,xvar,Tab,myprime);
            userinfo (2,AGbb,`palpha`,palph);
            p[xalph]:= palph;
            boolgam:= false;
            for xgam in t do
                userinfo (1,AGbb,`\txgamma`,xgam);
                xgam_palph    := xgam*palph;
                xgam_palphEval:= redp (fromPolToTabRelation (Tab,xvar,xgam_palph),
                                       myprime);
                coeffs (xgam_palph,xvars,'supp'):
                supp:= {supp}:
                if (supp subset {op(a)} and
                    xgam_palphEval <> 0) then
                    boolgam:= true;
                    userinfo (2,AGbb,`\txgamma`,xgam,`!`);
                    break;
                end if:
            end do:
            if (boolgam) then
                if (myprime = 0) then
                    malph:= xgam/xgam_palphEval;
                else
                    malph:= xgam/xgam_palphEval mod myprime;
                end if:
                m[xalph]:= malph;
                userinfo (2,AGbb,`\tmalph`,malph);
                # q[xalph]:= orthProj (malph,q,p,n,b,xvar,Tab,myprime);
                b:= [op({op(b),xalph})];
                userinfo (2,AGbb,`\tnew b`,b);
                s:= remove (i->i=xalph,s);
                userinfo (2,AGbb,`\tnew s`,s);
                mm:= [op(mm),xgam];
                c:= [op({op(c),xgam})];
                userinfo (2,AGbb,`\tnew c`,c);
                t:= remove (i->i=xgam,t);
                userinfo (2,AGbb,`\tnew t`,t);
            else
                userinfo (2,AGbb,`\tno xgam !!`);
                k[xalph]:= palph;
                userinfo (1,AGbb,`relation`,xalph,`\n\t\t OK`);
                d:= [op({op(d),xalph})];
                userinfo (2,AGbb,`\tnew d`,d);
                s:= remove (i->i=xalph,s);
                userinfo (2,AGbb,`\tnew s`,s);
            end if:
        end do:
        nn:= nnext (n,xvar,b,d,c,s);
        userinfo (2,AGbb,`set of terms`,nn);
    end do:
    return b,p,m,q,k,d;
end proc:

PolynomialScalarFGLM_guessing:= proc (Tab,xvar,cols_mon,mon_ord:=tdeg(op(xvar)),myprime:=65521)
local rows_mon, lcm_mon, all_mon, H, B, S, Z, G, Gp, R, Rp, F, r, fail_and_shift, i, f, lmf, j, g, z, zCreated,c,x;
    rows_mon:= [1];
    #  cols_mon:= listMonLessOrEqualThan (xvar,mon_ord, col_maxmon);
    lcm_mon := lcm (op(rows_mon))*lcm (op(cols_mon));
    all_mon := sort ([op({seq (seq (r*c, r in rows_mon),c in cols_mon)})],
                     (a,b)->TestOrder (a,b,mon_ord));
    userinfo (1,PolynomialScalarFGLM,`monoms:`,all_mon);
    H:= from1SetToMirrorTruncatedGeneratingSeries (Tab,xvar,cols_mon);
    B:= [seq ([x^(degree (lcm_mon,x)+1),0], x in xvar)];
    S:= [];
    Z:= [1];
    G:= [];
    Gp:=[];
    R:= [[H,1]]; # current relations
    userinfo (2,PolynomialScalarFGLM,`\tnew current relation`,R[1]);
    Rp:=[1];
    F:= [] ;     # failing relations
    while (Rp <> []) do
        R,z:= sort (R,(a,b)->TestOrder (LeadingMonomial (a[2],mon_ord),
                                        LeadingMonomial (b[2],mon_ord),
                                        mon_ord),output=[sorted,permutation]);
        Rp := Rp[z];
        F  := sort (F,(a,b)->TestOrder (LeadingMonomial (b[1],mon_ord),
                                        LeadingMonomial (a[1],mon_ord),
                                        mon_ord));
        userinfo (1,PolynomialScalarFGLM,`current relations`,map (r->r[2],R));
        userinfo (1,PolynomialScalarFGLM,`failing relations`,map (f->f[2],F));
        r:= R[1];
        userinfo (1,PolynomialScalarFGLM,`testing`,r[2]);
        if (LeadingMonomial (r[2],mon_ord) in cols_mon) then
            fail_and_shift:= [FailingWhenShiftedBy (r,all_mon,lcm_mon,mon_ord,
                                                    B,rows_mon)];
        else fail_and_shift:= [-1,0] # relation on the border to close the staircase
        end if:
        if (fail_and_shift[1] = -1) then # Good relation
            userinfo (1,PolynomialScalarFGLM,`\tOK with a shift`,fail_and_shift[2]);
            r:= [r[1],r[2],LeadingMonomial (r[2],mon_ord),fail_and_shift[2]];
            userinfo (1,PolynomialScalarFGLM,`\tnew relation!`,r);
            G := [op(G),r];
            Gp:= [op(Gp),r[3]];
            R := subsop (1=NULL,R);
            Rp:= subsop (1=NULL,Rp);
            for i from 1 to nops (R) do
                R[i]:= nfRightPart (R[i],xvar,[r[1..2]],mon_ord,myprime);
            end do:
        else
            userinfo (1,PolynomialScalarFGLM,`\tFAIL! when shifting by`,
                      fail_and_shift[1]);
            F:= [op(F),r];
            for j from 2 to nops(R) do
                Z:= nfLeftPart (R[j],xvar,[r,op(B)],mon_ord,myprime);
                z:= LeadingMonomial (Z[2],mon_ord);
                if (z <> Rp[j]) then Rp[j]:= z:
                end if:
                R[j] := Z;
            end do:
            R := subsop (1=NULL,R);
            Rp:= subsop (1=NULL,Rp);
            R,z:= sort (R,(a,b)->TestOrder (LeadingMonomial (b[1],mon_ord),
                                            LeadingMonomial (a[1],mon_ord),
                                            mon_ord),output=[sorted,permutation]);
            userinfo (2,PolynomialScalarFGLM,`\tupdating R to`,R);
            Rp := Rp[z];
            S:= [op(S),LeadingMonomial(r[2],mon_ord),fail_and_shift[1]];
            S:= staircaseStabilization (S,xvar,mon_ord);
            Z:= fromStaircaseToGb (S,xvar,mon_ord);
            userinfo (2,PolynomialScalarFGLM,`\tnew current relations in`,Z);
            for z in Z do
                if (z in Gp or z in Rp) then next;
                end if:
                Rp:= [op(Rp),z];
                zCreated:= false;
                userinfo (2,PolynomialScalarFGLM,`\tnew current relation`,z);
                i:= nops(F)-1;
                while (not zCreated and i > 0) do
                    f:= F[i];
                    lmf:= LeadingMonomial (f[1],mon_ord);
                    for j from i+1 to nops (F) do
                        g:= F[j];
                        if (divide (lmf,LeadingMonomial(g[1],mon_ord),'q') and
                            LeadingMonomial (g[2],mon_ord)*q = z) then
                            z:= nfLeftPart (f,xvar,[g,op(B),op(F)],mon_ord,myprime);
                            # Creation by division
                            zCreated:= true;
                            userinfo (2,PolynomialScalarFGLM,
                                      `\tby division of `,f,`and`,g);
                            break;
                        end if:
                    end do:
                    i:= i-1;
                end do:
                i:= nops(F);
                while (not zCreated and i > 0) do # No creation by division
                    f  := F[i];
                    lmf:= map (g->LeadingMonomial (g,mon_ord),f);
                    if (divide (z,lmf[2],'q')) then
                        z:= nfLeftPart (q*f,xvar,[op(B),op(F)],mon_ord,myprime);
                        userinfo (2,PolynomialScalarFGLM,
                                  `\tnot by division of`,f);
                        zCreated:= true;
                    end if:
                    i:= i-1;
                end do:
                if (not zCreated) then printf ("bug not created\n");
                end if:
                z:= nfRightPart (z,xvar,map (g->g[1..2],G),mon_ord,myprime);
                userinfo (1,PolynomialScalarFGLM,`\treduced to`,z);
                R := [op(R),z];
            end do:
        end if:
    end do:
    return map (g->g[2],G);
end proc:


###################
# Main procedures #
#    Adaptive     #
###################

AdaptiveMatrixScalarFGLM:= proc (Tab,var:=['x','y'],mon_ord:=tdeg(op(var)),d:=10,
                                 p:=0,full_answer:=false)
description "Compute the minimal relation satisfied by Tab for all the monomials "
    "in characteristic p."
    "If full_answer is set to true, returns a set of triplets [m,r,s] where\n"
    "- m is a monomial;\n"
    "- r is a relation with leading monomial m;\n"
    "- s is the shift of the relation, that is up to which monomial "
    "it has been tested.\n"
    "Otherwise returns a set of r only.\n"
    "Parameter d is an upper bound on the degree of the ideal "
    "to prevent an infinite loop.";
local L,U,rank,next_mon,staircase,R,tau,col_tau,row_tau,elem_tau2,r,i,g;
local col_next_mon,rtau;
    userinfo (1,AdaptiveScalarFGLM,`*** Tab `, Tab,
              `in variable`, var, `up to degree`, d,
              `in characteristic`, p, `***`);
    elem_tau2:= fromMonToTabElem (Tab,var,1);
    userinfo (2,AdaptiveScalarFGLM,`***\t New monomial`, 1, `***`);
    if (elem_tau2 = 0) then
        userinfo (2,AdaptiveScalarFGLM,`***\t New potential relation`, 1,
                  `***`);
        if (full_answer) then return [[1,1,1]];
        else return [1];
        end if:
    end if:
    userinfo (2,AdaptiveScalarFGLM,`***\t\t in the staircase! ***`);
    L        := Matrix (1,1,1);
    U        := Matrix (1,1,elem_tau2);
    rank     := 1;
    next_mon := sortListMon (var,mon_ord);
    staircase:= [1];
    if (d = 1) then
        userinfo (2,AdaptiveScalarFGLM,`***\t Early termination ***`);
        R:= map (v->[v,redp (v-fromMonToTabElem (Tab,var,v)/elem_tau2,p),1],next_mon);
        if (full_answer) then return R;
        else return map (r->r[2],R);
        end if:
    end if:
    R        := [];
    while (next_mon <> []) do
        tau    := next_mon[1];
        userinfo (2,AdaptiveScalarFGLM,`***\t New monomial`, tau, `***`);
        col_tau:= from2SetsToMultiHankelMatrix (Tab,var,staircase,[tau]);
        if (p = 0) then
            col_tau, row_tau:= LinearSolve (L,col_tau),
            Transpose (LinearSolve (Transpose (U),col_tau));
        elif (p < 2^32) then
            L              := LinearAlgebra[Modular][Mod] (p,L,integer[8]);
            U              := LinearAlgebra[Modular][Mod] (p,U,integer[8]);
            col_tau         := LinearAlgebra[Modular][Mod] (p,col_tau,integer[8]);
            col_tau, row_tau:= LinearAlgebra[Modular][LinearSolve] (p,<L|col_tau>,
                                                                    1,inplace=false),
            Transpose (LinearAlgebra[Modular][LinearSolve]
                       (p,<Transpose(U)|col_tau>,
                        1,inplace=false));
        else
            L               := L mod p;
            U               := U mod p;
            col_tau, row_tau:= col_tau mod p, row_tau mod p;
            col_tau, row_tau:= LinearSolve (L,col_tau),
            Transpose (LinearSolve (Transpose (U),col_tau));
        end if:
        elem_tau2:= fromMonToTabElem (Tab,var,tau^2);
        elem_tau2:= redp (-row_tau.col_tau+elem_tau2,p);
        if (type (elem_tau2,Matrix)) then elem_tau2:= elem_tau2[1,1];
        end if:
        if (elem_tau2 <> 0) then
            userinfo (2,AdaptiveScalarFGLM,`***\t\t in the staircase! ***`);
            L        := <<L,row_tau>|<Matrix (rank,1),1>>;
            U        := <<U,Matrix (1,rank)>|<col_tau,elem_tau2>>;
            staircase:= [op(staircase),tau];
            next_mon := InterReduce ([op(next_mon[2..-1]),
                                      op(remove (l->`or` (seq (divide (l,g),
                                                               g in map (r->r[1],R))),
                                                 expand (tau*var)))], mon_ord);
            rank:= rank+1;
            if (rank >= d) then
                userinfo (2,AdaptiveScalarFGLM,`***\t Early termination ***`);
                col_next_mon:= from2SetsToMultiHankelMatrix (Tab,var,
                                                             staircase,
                                                             next_mon);
                if (p = 0) then
                    col_next_mon:= LinearSolve (U,
                                                LinearSolve (L,col_next_mon));
                elif (p < 2^32) then
                    L:= LinearAlgebra[Modular][Mod] (p,L,integer[8]);
                    U:= LinearAlgebra[Modular][Mod] (p,U,integer[8]);
                    col_next_mon:= LinearAlgebra[Modular][Mod] (p,col_next_mon,
                                                                integer[8]);
                    col_next_mon:= LinearAlgebra[Modular][LinearSolve] (p,
                                                                        <L|
                                                                        col_next_mon>,
                                                                        nops(next_mon),
                                                                        inplace=false);
                    col_next_mon:= LinearAlgebra[Modular][LinearSolve] (p,
                                                                        <U|
                                                                        col_next_mon>,
                                                                        nops(next_mon),
                                                                        inplace=false);
                else
                    L           := L mod p;
                    U           := U mod p;
                    col_next_mon:= col_next_mon mod p;
                    col_next_mon:= LinearSolve (L,col_next_mon) mod p;
                    col_next_mon:= LinearSolve (U,col_next_mon) mod p;
                end if:
                r:= nops (R);
                R:= [op(R),seq ([next_mon[i],
                                 redp (next_mon[i]
                                       - DotProduct (Column (col_next_mon,i),
                                                     staircase),p),
                                 staircase],
                                i=1..nops(next_mon))];
                map (r->userinfo (2,AdaptiveScalarFGLM,`***\t New potential relations`,
                                  r[2],`***`),R[r+1..-1]);
                if (full_answer) then return R;
                else return map (r->r[2],R);
                end if:
            end if:
        else
            userinfo (2,AdaptiveScalarFGLM,`***\t\t NOT in the staircase! ***`);
            U;
            if (p = 0) then
                col_tau:= LinearSolve (U,col_tau);
            elif (p < 2^32) then
                U      := LinearAlgebra[Modular][Mod] (p,U,integer[8]);
                col_tau:= LinearAlgebra[Modular][Mod] (p,col_tau,integer[8]);
                col_tau:= LinearAlgebra[Modular][LinearSolve] (p,<U|col_tau>,
                                                               1,inplace=false);
            else
                U      := U mod p;
                col_tau:= col_tau mod p;
                col_tau:= LinearSolve (U,col_tau) mod p;
            end if:
            rtau:= redp (tau - DotProduct (col_tau,staircase),p);
            R   := [op(R),[tau, rtau, [op(staircase),tau]]];
            next_mon:= subsop(1=NULL,next_mon);
            userinfo (2,AdaptiveScalarFGLM,`***\t New potential relation`, rtau,
                      `***`);
        end if:
    end do:
    if (full_answer) then return R;
    else return map (r->r[2],R);
    end if:
end proc:

AdaptivePolynomialScalarFGLM_guessing:= proc (Tab,var:=['x','y'],mon_ord:=tdeg(op(var)),
                                              d:=10,p:=0,full_answer:=false)
description "Compute the minimal relation satisfied by Tab for all the monomials "
    "in characteristic p."
    "If full_answer is set to true, returns a set of triplets [m,r,s] where\n"
    "- m is a monomial;\n"
    "- r is a relation with leading monomial m;\n"
    "- s is the shift of the relation, that is up to which monomial "
    "it has been tested.\n"
    "Otherwise returns a set of r only.\n"
    "Parameter d is an upper bound on the degree of the ideal "
    "to prevent an infinite loop.";
local PolS,BS,RS,next_mon,staircase,GS,GStau,lcmS,lcmS2,TwoS,tau,lcmStau,lcmStau2,s;
local extra_mon,PolStau,BStau,RStau,rtau,rank,g,i,initiated,T,n,lm;
    userinfo (1,AdaptiveScalarFGLM,`*** Tab `, Tab,
              `in variable`, var, `up to degree`, d,
              `in characteristic`, p, `***`);
    extra_mon:= fromMonToTabElem (Tab,var,1);
    userinfo (2,AdaptiveScalarFGLM,`***\t New monomial`, 1, `***`);
    if (PolS = 0) then
        userinfo (2,AdaptiveScalarFGLM,`***\t New potential relation`, 1,
                  `***`);
        if (full_answer) then return [[1,1,1]];
        else return [1];
        end if:
    end if:
    userinfo (2,AdaptiveScalarFGLM,`***\t\t in the staircase! ***`);
    BS       := map (v->[v,0], var);
    RS       := [[extra_mon,1]];
    next_mon := sortListMon (var,mon_ord);
    staircase:= [1];
    T        := table ([1=1]);
    rank     := 1;
    PolS     := extra_mon;
    if (d = 1) then
        userinfo (2,AdaptiveScalarFGLM,`***\t Early termination ***`);
        GS:= map (v->v=[v,redp (v-fromMonToTabElem (Tab,var,v)/elem_tau2,p),1],
                  next_mon);
        if (full_answer) then return GS;
        else return map (g->g[2],GS);
        end if:
    end if:
    GS   := [];
    lcmS := 1;
    lcmS2:= 1;
    TwoS := [1];
    while (next_mon <> []) do
        tau      := next_mon[1];
        userinfo (2,AdaptiveScalarFGLM,`***\t New monomial`, tau, `***`);
        lcmStau  := lcm (tau,lcmS);
        lcmStau2 := lcmStau^2;
        extra_mon:= remove (m->m in TwoS, map(n->n*tau,[op(staircase),tau]));
        PolStau  := redp (mirrorPolynomial (from1SetToTruncatedGeneratingSeries
                                            (Tab,var,extra_mon),
                                            var,lcmStau2),p);
        BStau    := map (v->[v^(degree (lcmStau2,v)+1),0], var);
        RStau    := map (r->nfLeftPart([expand (lcmStau2/lcmS2 * r[1] +
                                                redp(PolStau * r[2],p)),r[2]],var,BStau,
                                       mon_ord,p),RS);
        GStau    := map (g->[g[1],
                             op(nfLeftPart([expand (lcmStau2/lcmS2 * g[2] +
                                                    redp(PolStau * g[3],p)),g[3]],
                                           var,BStau,mon_ord,p)),
                             g[4]],GS);
        PolStau  := RStau[1][1];
        initiated:= false;
        for i from 1 to nops (var) do
            if (degree (tau,var[i]) >= 2) then
                rtau:= nfLeftPart (RStau[T[tau/var[i]^2]],var,
                                   [RStau[T[tau/var[i]]],op(BStau)],mon_ord,p);
                initiated:= true;
                lm       := tau/var[i]^2;
                break;
            end if:
        end do:
        if (not initiated) then
            for i from 1 to nops (var) do
                if (degree (tau,var[i]) = 1) then
                    rtau:= nfLeftPart (var[i]*RStau[T[tau/var[i]]],var,
                                       BStau,mon_ord,p);
                    initiated:= true;
                    lm       := tau/var[i];
                    break;
                end if:
            end do:
        end if:
        if (not initiated) then error "BUG";
        end if:
        rtau:= nfRightPart (rtau,var,GStau,mon_ord,p);
        rtau:= nfLeftPart (rtau,var,BStau,mon_ord,p);
        rtau:= nfLeftHigherPart (rtau,var,RStau[T[lm]+1..-1],lcmStau2,
                                 map (g->g[1],GStau),mon_ord,p);
        if (LeadingMonomial (leftHigherPart (rtau[1],var,lcmStau2,map(g->g[1],GStau),
                                             mon_ord),mon_ord) = lcmStau2/tau) then
            userinfo (2,AdaptiveScalarFGLM,`***\t\t in the staircase! ***`);
            staircase:= [op(staircase),tau];
            next_mon := InterReduce ([op(next_mon[2..-1]),
                                      op(remove (l->`or` (seq (divide (l,g),
                                                               g in map (r->r[1],GS))),
                                                 expand (tau*var)))], mon_ord);
            rank     := rank+1;
            RS       := [op(RStau),rtau];
            BS       := BStau;
            TwoS     := mergeOrderedLists (TwoS,extra_mon,mon_ord);
            lcmS     := lcmStau;
            lcmS2    := lcmStau2;
            PolS     := PolStau;
            T[tau]   := rank;
            if (rank >= d) then
                userinfo (2,AdaptiveScalarFGLM,`***\t Early termination ***`);
                lcmStau  := lcm (op(next_mon),lcmS);
                lcmStau2 := lcmS*lcmStau;
                extra_mon:= sortListMon ([op(remove (m->m in TwoS,
                                                     {seq (seq (s*tau, s in staircase),
                                                           tau in next_mon)}))],mon_ord);
                PolStau := redp (mirrorPolynomial
                                 (from1SetToTruncatedGeneratingSeries
                                  (Tab,var,extra_mon),var,lcmStau2),p);
                BStau   := map (v->[v^(degree (lcmStau2,v)+1),0], var);
                RStau   := map (r->nfLeftPart([expand (lcmStau/lcmS * r[1] +
                                                       redp(PolStau * r[2],p)),
                                               r[2]],var,BStau,mon_ord,p),RS);
                GStau    := map (g->[g[1],
                                     op(nfLeftPart([expand (lcmStau/lcmS * g[2] +
                                                            redp(PolStau * g[3],p)),
                                                    g[3]],var,BStau,mon_ord,p)),
                                     g[4]],GS);
                PolStau:= RStau[1][1];
                for n from 1 to nops(next_mon) do
                    tau      := next_mon[n];
                    initiated:= false;
                    for i from 1 to nops (var) do
                        if (degree (tau,var[i]) >= 2) then
                            rtau:= nfLeftPart (RStau[T[tau/var[i]^2]],var,
                                               [RStau[T[tau/var[i]]],op(BStau)],
                                               mon_ord,p);
                            initiated:= true;
                            lm       := tau/var[i]^2;
                            break;
                        end if:
                    end do:
                    if (not initiated) then
                        for i from 1 to nops (var) do
                            if (degree (tau,var[i]) = 1) then
                                rtau:= nfLeftPart (var[i]*RStau[T[tau/var[i]]],var,
                                                   BStau,mon_ord,p);
                                initiated:= true;
                                lm       := tau/var[i];
                                break;
                            end if:
                        end do:
                    end if:
                    rtau       := nfRightPart (rtau,var,GStau,mon_ord,p);
                    rtau       := nfLeftPart (rtau,var,BStau,mon_ord,p);
                    rtau       := nfLeftHigherPart (rtau,var,RStau[T[lm]+1..-1],
                                                    lcmStau2,
                                                    map (g->g[1],GStau),mon_ord,p);
                    userinfo (2,AdaptiveScalarFGLM,`***\t New potential relations`,
                              rtau[2],`***`);
                    next_mon[n]:= [tau,rtau[2],staircase];
                end do:
                GStau:= [op(map (g->subsop(2=NULL,g),GStau)),
                         op(next_mon)];
                if (full_answer) then return GStau;
                else return map (g->g[2],GStau);
                end if:
            end if:
        else
            userinfo (2,AdaptiveScalarFGLM,`***\t\t NOT in the staircase! ***`);
            GS:= [op(GS),[tau,rtau[1],rtau[2],[op(staircase),tau]]];
            next_mon:= subsop(1=NULL,next_mon);
            userinfo (2,AdaptiveScalarFGLM,`***\t New potential relation`, rtau[2],
                      `***`);
        end if:
    end do:
    if (full_answer) then return GS;
    else return map (g->g[2],GS);
    end if:
end proc:


##########################
# Versions with counters #
##########################

nf_basicop:= proc (g, L, ord, counter, myprime)
local tmp,i;
local counterBasic;
    counterBasic:= counter;
    if (L = []) then
        if (g[2] <> 0) then
            return expand (g/LeadingCoefficient (g[2],ord)) mod myprime,
            counterBasic+nops(g[1]);
        else return expand (g) mod myprime,counterBasic+1;
        end if:
    end if:
    NormalForm (expand (g)[1],map (l->l[1],expand (L)),ord,'q',
                characteristic=myprime):
    tmp:= expand (g - add (q[i]*L[i],i=1..nops(L))) mod myprime;
    counterBasic:= counterBasic + 2*add (nops(q[i])*nops(L[i]),i=1..nops(L));
    if (tmp[2] <> 0) then
        tmp:=expand (tmp/LeadingCoefficient (tmp[2],ord)) mod myprime;
    end if:
    counterBasic:= counterBasic + nops(tmp[1]);
    try:
        tmp[1]:= sort (tmp[1],order=mon_ord);
        tmp[2]:= sort (tmp[2],order=mon_ord);
    catch:
    end try:
    return tmp,counterBasic;
end proc:

nfLP_basicop:= proc (g, L, mon, M, ord:=mon_ord, p:=0)
local tmp, g2, L2, i;
global count;
    if (L = []) then
        if (g[2] <> 0) then return expand (g/LeadingCoefficient (g[2],ord));
        else                return expand (g);
        end if:
        # return expand (g/LeadingCoefficient (g[2],ord));
    end if:
    g2   := [nfUnder (expand (g)[1],mon,M,ord),g[2]];
    L2   := map (l->`if` (l[2]=0,l,
                          [nfUnder (expand (l)[1],mon,M,ord),l[2]]),L);
    NormalForm (g2[1],map (l->l[1],L2),ord,'q',characteristic=p):
    tmp:= expand (g - add (q[i]*L[i],i=1..nops(L)));
    count:= count + add (nops(q[i])*(2*nops(L[i])+nops(L2[i])),i=1..nops(L));
    if (p <> 0) then tmp:= tmp mod p;
    end if:
    if (tmp[2] <> 0) then tmp:=expand (tmp/LeadingCoefficient (tmp[2],ord));
    end if:
    if (p <> 0) then tmp:= tmp mod p;
    end if:
    try:
        tmp[1]:= sort (tmp[1],order=mon_ord);
        tmp[2]:= sort (tmp[2],order=mon_ord);
    catch:
    end try:
    return tmp;
end proc:


nf2_basicop:= proc (g, L, ord, counter,myprime)
local res,counterBasic;
    res,counterBasic:= nf_basicop ([g[2],g[1]], map (l->[l[2],l[1]],L), ord,
                                   counter,myprime);
    return nf_basicop ([res[2],res[1]],[],ord,counterBasic,myprime);
end proc:


staircaseMaxElements_basicop:= proc (n,xvar,H,mon_order,counter)
local Max, c, d, isMax, SpansMax, i;
local counterBasic;
    counterBasic:= counter;
    Max := [];
    SpansMax := [];
    for c in H do
        userinfo(2,staircaseMaxElements,`c=`,c);
        isMax := true;
        for d in H do
            userinfo(3,staircaseMaxElements,`d=`,d);
            counterBasic:= counterBasic+1;
            if (d[4] <> 0 and divide(d[4],c[4]) and c[4] <> d[4]) then
                isMax := false;
                break;
            end if:
        end do:
        if isMax then
            if not c[4] in SpansMax then
                Max := [op(Max), c];
                SpansMax := [op(SpansMax), c[4]];
            else
                for i from 1 to nops(Max) do
                    counterBasic:= counterBasic+1;
                    if (TestOrder (c[1],Max[i][1],mon_order)) then
                        Max[i]:= c; break;
                    end if:
                end do:
            end if:
        end if:
    end do;
    return Max,counterBasic;
end proc:

staircaseBorder_basicop:= proc (n,xvar,S,mon_order,counter)
local B, trueB, isMin, b1, b2, trueS,s,m,x;
local counterBasic;
    counterBasic:= counter;
    if (S = []) then return [1];
    end if:
    trueS:= stabilize (S,n,xvar,mon_order);
    B:= [op({seq (seq (x*s, x in xvar), s in trueS)} minus {op(trueS)})];
    counterBasic:= counterBasic + nops(xvar)*nops(trueS);
    trueB:= [];
    for b1 in B do
        isMin:= true;
        for b2 in B do
            if (b2 = b1) then next;
            else
                counterBasic:= counterBasic+1;
                if (divide (b1,b2)) then
                    isMin:= false; break;
                end if:
            end if:
        end do:
        if (isMin) then trueB:= [op(trueB),b1];
        end if:
    end do;
    return sortListMon (trueB,xvar,mon_order),counterBasic;
end proc:

border_basicop:= proc (xvar,S,mon_ord,counter)
local B,bool,i,j,TB,s,m;
local counterBasic;
    counterBasic:= counter;
    if (S = []) then return 1;
    end if:
    B:= sort (remove (s->s in S, [op({seq (seq (s*m, m in xvar), s in S)})]),
              (a,b)->TestOrder(a,b,mon_ord));
    counterBasic:= counterBasic+nops(B)*nops(S);
    TB:= table (map (b->b = [b,true],B));
    for i from 1 to nops (B) do
        if (not TB[B[i]][2]) then next;
        end if:
        for j from i+1 to nops(B) do
            if (divide (B[j],B[i])) then
                TB[B[j]][2]:= false;
            end if:
            counterBasic:= counterBasic+1;
        end do:
    end do:
    return select (b->TB[b][2],B),counterBasic;
end proc:
# trace(border_basicop):


BMS_linalg_basicop:= proc (Tab,stop_monom,n,xvar,mon_order,myprime)
local m,T,S,H,G,g,Hp,Gp,gp,s,Sp,divides_mu,h,gp_muh_over_m,i,j,t,supp,degT;
local counterBasic,p;
    p:=  myprime;
    counterBasic:=0;
    degT:= degree (stop_monom,xvar);
    T:= select (mu->TestOrder (mu,stop_monom,mon_order),
                listMon (n,xvar,mon_order,degT));
    userinfo (2,BMS_linalg,`List of monomials:`,T);
    S:= [];
    G:= [[1,1,<1>,0]]; # [LT,pol-relation,vec-relation,current span]
    H:= [];            # [LT,pol-relation,vec-relation,fail]
    for t from 1 to nops(T) do
        m:= T[t];
        # if (degree (m,[y,z])=0) then
        #     printf ("*** %s ", convert (m,string));
        #     if (m = stop_monom) then
        #         printf ("\n");
        #     end if:
        # end if:
        userinfo (1,BMS_linalg,`*** monomial`, m, `***`);
        Hp:= H;
        for g in G do
            counterBasic:= counterBasic+1;
            if (divide (m,g[1],'m_over_g')) then
                supp:= Support (g[2],mon_order);
                gp:= DotProduct (multiHankel (n,xvar,Tab,[m_over_g],
                                              supp) mod p,g[3] mod p) mod p;
                counterBasic:= counterBasic + 2*nops(supp);
                if(gp <> 0) then
                    userinfo (2,BMS_linalg,`\t!!!`,g[2],`fails\t!!!`);
                    Hp:= [op(Hp),[g[1],g[2]/gp,g[3]/gp,m_over_g]];
                    counterBasic:= counterBasic + nops(supp);
                else userinfo (2,BMS_linalg,`\t`,g[2],`succeeds`);
                end if:
            else
                userinfo (2,BMS_linalg,`\t???`,g[2],`nothing to do\t???`);
            end if:
        end do:
        Hp,counterBasic:= staircaseMaxElements_basicop (n,xvar,Hp,mon_order,
                                                        counterBasic);
        userinfo (1,BMS_linalg,`\tfailing relations`);
        for h in Hp do
            userinfo (1,BMS_linalg,`\t\t`,[h[2],h[4]]);
        end do:
        Sp:= stabilize (map (h->h[4],Hp),n,xvar,mon_order);
        userinfo (3,BMS_linalg,`\tnew staircase`,Sp);
        Gp,counterBasic:= staircaseBorder_basicop (n,xvar,Sp,mon_order,
                                                   counterBasic);
        userinfo (3,BMS_linalg,`\tnew LT for relations`,Gp);
        Gp:= [seq ([s,1,<1>,[]], s in Gp)];
        userinfo (1,BMS_linalg,`\tvalid relations are`);
        for i from 1 to nops(Gp) do
            gp:= Gp[i];
            g,s:= relationBelow (gp,G);
            userinfo (3,BMS_linalg,`\t\t`,g[1],`is below`,gp[1]);
            counterBasic:= counterBasic+1;
            if (not divide (m,gp[1],'m_over_gp')) then
                userinfo (2,BMS_linalg,`\t\t`,gp[1],`does not divide`,m);
                gp[2]:= expand (g[2]*s) mod p;
                supp:= Support (gp[2],mon_order);
                gp[3]:= fromPolToVector (n,xvar,supp,gp[2]);
                counterBasic:= counterBasic+2*nops(supp);
                j:= t;
                while (j > 0 and not divide (T[j],gp[1],'span_gp')) do
                    j:=j-1;
                end do:
                if (j <> 0) then gp[4]:= span_gp;
                end if:
            else
                counterBasic:= counterBasic+1;
                divides_mu,h,gp_muh_over_m:= greaterSpan (H,m_over_gp);
                if (divides_mu) then
                    userinfo (2,BMS_linalg,`\t\t`,m,`/`,gp[1],`divides`,h[4]);
                    if (j = 1) then print (ok);
                    end if:
                    supp:= Support (g[2],mon_order);
                    counterBasic:= counterBasic+2*nops(supp);
                    gp[2]:= expand (g[2]*s
                                    - ((DotProduct (multiHankel (n,xvar,Tab,
                                                                 [m/g[1]] mod p,
                                                                 supp),
                                                    g[3] mod p) mod p)
                                       *gp_muh_over_m*h[2])) mod p;
                    supp:= Support (gp[2],mon_order);
                    gp[3]:= fromPolToVector (n,xvar,supp,gp[2]);
                    counterBasic:= counterBasic+nops(supp);
                    gp[4]:= m_over_gp;
                else
                    userinfo (2,BMS_linalg,`\t\t`,h);
                    userinfo (2,BMS_linalg,`\t\t`,m,`/`,gp[1],
                              `does not divide any fail(h)`);
                    gp:= g;
                    supp:= Support (gp[2],mon_order);
                    counterBasic:= counterBasic+2*nops(supp);
                    gp[3]:= fromPolToVector (n,xvar,supp,gp[2]);
                    gp[4]:= m_over_gp;
                end if:
            end if:
            Gp[i]:=gp;
            userinfo (1,BMS_linalg,`\t\t`,[gp[2],gp[4]]);
        end do:
        H:= Hp;
        G:= Gp;
        userinfo (1,BMS_linalg,`reduced to`);
        for i from 1 to nops(G) do
            Gp:= map (g->g[2],subsop(i=NULL,G));
            if (Gp <> []) then
                NormalForm (G[i][2], Gp, mon_order,'q');
                G[i][2]:= expand (G[i][2] - add (q[j]*Gp[j],j=1..nops(q)));
                supp:= Support (G[i][2],mon_order);
                G[i][3]:= fromPolToVector (n,xvar,supp,G[i][2]);
                userinfo (1,BMS_linalg,`\t\t`,[G[i][2],G[i][4]]);
            end if:
        end do:
        S:= Sp;
    end do:
    return counterBasic;
end proc:


Adaptive_BMS_linalg_basicop:= proc (Tab,stop_monom,sizeS,
                                    n,xvar,mon_order:=tdeg(op(xvar)))
local m,T,S,H,G,g,Hp,Gp,gp,s,Sp,divides_mu,h,gp_muh_over_m,i,j,t,supp,degT;
local counterBasic, skip, skipped, p;
    p:=  myprime;
    counterBasic:=0;
    degT:= degree (stop_monom,xvar);
    T:= select (mu->TestOrder (mu,stop_monom,mon_order),
                listMon (n,xvar,mon_order,degT));
    userinfo (2,BMS_linalg,`List of monomials:`,T);
    S:= [];
    G:= [[1,1,<1>,0]]; # [LT,pol-relation,vec-relation,current span]
    H:= [];            # [LT,pol-relation,vec-relation,fail]
    for t from 1 to nops(T) do
        m:= T[t];
        if (degree (m,xvar[-1]) = 0) then
            printf ("*** %s ",convert (m,string));
        end if:
        if (m = stop_monom) then  printf ("\n");
        end if:
        userinfo (1,Adaptive_BMS_linalg,`*** monomial`, m, `***`);
        skip:= true;
        for g in G do
            if (divide (m,g[1],'m_over_g')) then
                if (m_over_g in S or
                    nops({op(S)} union {op(fast_Stabilize ([g[1],m_over_g],
                                                           n,xvar,mon_order))})
                    <= sizeS)
                then
                    skip:= false;
                    userinfo (2,Adaptive_BMS_linalg,`will not be skipped!`);
                    break;
                end if;
            end if;
        end do;
        if (skip) then
            skipped:= [op(skipped), m];
            userinfo (1,Adaptive_BMS_linalg,`\tnew skipped monomial!`,skipped);
            next;
        end if:
        Hp:= H;
        for g in G do
            counterBasic:= counterBasic+1;
            if (divide (m,g[1],'m_over_g')) then
                supp:= Support (g[2],mon_order);
                gp:= DotProduct (multiHankel (n,xvar,Tab,[m_over_g],
                                              supp) mod myprime,g[3] mod myprime)
                mod myprime;
                counterBasic:= counterBasic + 2*nops(supp);
                if(gp <> 0) then
                    userinfo (2,Adaptive_BMS_linalg,`\t!!!`,g[2],`fails\t!!!`);
                    Hp:= [op(Hp),[g[1],g[2]/gp,g[3]/gp,m_over_g]] mod myprime;
                    counterBasic:= counterBasic + nops(supp);
                else userinfo (2,Adaptive_BMS_linalg,`\t`,g[2],`succeeds`);
                end if:
            else
                userinfo (2,Adaptive_BMS_linalg,`\t???`,g[2],`nothing to do\t???`);
            end if:
        end do:
        Hp,counterBasic:= staircaseMaxElements_basicop (n,xvar,Hp,mon_order,
                                                        counterBasic);
        userinfo (1,Adaptive_BMS_linalg,`\tfailing relations`);
        for h in Hp do
            userinfo (1,Adaptive_BMS_linalg,`\t\t`,[h[2],h[4]]);
        end do:
        if (Hp <> H) then
            Sp:= stabilize (map (h->h[4],Hp),n,xvar,mon_order);
        else
            Sp:= S;
        end if:
        userinfo (3,Adaptive_BMS_linalg,`\tnew staircase`,Sp);
        Gp,counterBasic:= staircaseBorder_basicop (n,xvar,Sp,mon_order,
                                                   counterBasic);
        userinfo (3,Adaptive_BMS_linalg,`\tnew LT for relations`,Gp);
        Gp:= [seq ([s,1,<1>,[]], s in Gp)];
        userinfo (1,Adaptive_BMS_linalg,`\tvalid relations are`);
        for i from 1 to nops(Gp) do
            gp:= Gp[i];
            g,s:= relationBelow (gp,G);
            userinfo (3,Adaptive_BMS_linalg,`\t\t`,g[1],`is below`,gp[1]);
            counterBasic:= counterBasic+1;
            if (not divide (m,gp[1],'m_over_gp')) then
                userinfo (2,Adaptive_BMS_linalg,`\t\t`,gp[1],`does not divide`,m);
                gp[2]:= expand (g[2]*s) mod myprime;
                supp:= Support (gp[2],mon_order);
                gp[3]:= fromPolToVector (n,xvar,supp,gp[2]);
                counterBasic:= counterBasic+2*nops(supp);
                j:= t;
                while (j > 0 and not divide (T[j],gp[1],'span_gp')) do
                    j:=j-1;
                end do:
                if (j <> 0) then gp[4]:= span_gp;
                end if:
            else
                counterBasic:= counterBasic+1;
                divides_mu,h,gp_muh_over_m:= greaterSpan (H,m_over_gp);
                if (divides_mu) then
                    userinfo (2,Adaptive_BMS_linalg,`\t\t`,m,`/`,gp[1],`divides`,h[4]);
                    if (j = 1) then print (ok);
                    end if:
                    supp:= Support (g[2],mon_order);
                    counterBasic:= counterBasic+2*nops(supp);
                    gp[2]:= expand (g[2]*s
                                    - ((DotProduct (multiHankel (n,xvar,Tab,
                                                                 [m/g[1]] mod myprime,
                                                                 supp),
                                                    g[3] mod myprime) mod myprime)
                                       *gp_muh_over_m*h[2])) mod myprime;
                    supp:= Support (gp[2],mon_order);
                    gp[3]:= fromPolToVector (n,xvar,supp,gp[2]);
                    counterBasic:= counterBasic+nops(supp);
                    gp[4]:= m_over_gp;
                else
                    userinfo (2,Adaptive_BMS_linalg,`\t\t`,h);
                    userinfo (2,Adaptive_BMS_linalg,`\t\t`,m,`/`,gp[1],
                              `does not divide any fail(h)`);
                    gp:= g;
                    supp:= Support (gp[2],mon_order);
                    counterBasic:= counterBasic+2*nops(supp);
                    gp[3]:= fromPolToVector (n,xvar,supp,gp[2]);
                    gp[4]:= m_over_gp;
                end if:
            end if:
            Gp[i]:=gp;
            userinfo (1,Adaptive_BMS_linalg,`\t\t`,[gp[2],gp[4]]);
        end do:
        H:= Hp;
        G:= Gp;
        userinfo (1,Adaptive_BMS_linalg,`reduced to`);
        for i from 1 to nops(G) do
            Gp:= map (g->g[2],subsop(i=NULL,G));
            if (Gp <> []) then
                NormalForm (G[i][2], Gp, mon_order,'q');
                G[i][2]:= expand (G[i][2] - add (q[j]*Gp[j],j=1..nops(q))) mod myprime;
                supp:= Support (G[i][2],mon_order);
                G[i][3]:= fromPolToVector (n,xvar,supp,G[i][2]);
                userinfo (1,Adaptive_BMS_linalg,`\t\t`,[G[i][2],G[i][4]]);
            end if:
        end do:
        S:= Sp;
    end do:
    return counterBasic;
end proc:

fast_Stabilize_basicop:= proc (S,n,xvar,mon_order,counter)
local Sp, s, T, i,t,d;
local counterBasic;
    counterBasic:= counter;
    Sp:= {};
    for s in S do
        counterBasic:= counterBasic+1;
        T:= {1};
        for i from 1 to n do
            counterBasic:= counterBasic+nops(T)*n;
            T:= {seq (seq (t*xvar[i]^d, d=0..degree (s,xvar[i])), t in T)};
        end do:
        counterBasic:= counterBasic+nops(T);
        Sp:= Sp union T;
    end do:
    return Sp,counterBasic;
end proc:

Adaptive2_BMS_linalg_basicop:= proc (Tab,stop_monom,sizeS,
                                     n,xvar,mon_order:=tdeg(op(xvar)))
local m,T,S,H,G,g,Hp,Gp,gp,s,Sp,divides_mu,h,gp_muh_over_m,i,j,t,supp,degT;
local counterBasic,fStabRes,bool,p;
    p:=  myprime;
    counterBasic:=0;
    degT:= degree (stop_monom,xvar);
    T:= select (mu->TestOrder (mu,stop_monom,mon_order),
                listMon (n,xvar,mon_order,degT));
    userinfo (2,Adaptive_BMS_linalg,`List of monomials:`,T);
    S:= [];
    G:= [[1,1,<1>,0]]; # [LT,pol-relation,vec-relation,current span]
    H:= [];            # [LT,pol-relation,vec-relation,fail]
    for t from 1 to nops(T) do
        m:= T[t];
        if (degree (m,[y,z]) = 0) then
            printf ("*** %s ",convert (m,string));
        end if:
        if (m = stop_monom) then  printf ("\n");
        end if:
        userinfo (1,Adaptive_BMS_linalg,`*** monomial`, m, `***`);
        Hp:= H;
        for g in G do
            counterBasic:= counterBasic+1;
            if (divide (m,g[1],'m_over_g')) then
                bool:= false;
                if (not m_over_g in S) then
                    fStabRes:=[fast_Stabilize_basicop ([g[1],m_over_g],n,xvar,
                                                       mon_order,counterBasic)];
                    counterBasic:= counterBasic + fStabRes[2];
                    if (nops({op(S)} union {op(fStabRes[1])}) > sizeS)
                    then
                        userinfo (2,Adaptive_Adaptive_BMS_linalg,`\t@@@`,g[2],
                                  `skipped\t@@@`);
                        bool:= true;
                    end if:
                end if:
                if (not bool) then
                    supp:= Support (g[2],mon_order);
                    gp:= DotProduct (multiHankel (n,xvar,Tab,[m_over_g],
                                                  supp) mod myprime,g[3] mod myprime)
                    mod myprime;
                    counterBasic:= counterBasic + 2*nops(supp);
                    if(gp <> 0) then
                        userinfo (2,Adaptive_BMS_linalg,`\t!!!`,g[2],`fails\t!!!`);
                        Hp:= [op(Hp),[g[1],g[2]/gp,g[3]/gp,m_over_g]];
                        counterBasic:= counterBasic + nops(supp);
                    else userinfo (2,Adaptive_BMS_linalg,`\t`,g[2],`succeeds`);
                    end if:
                end if:
            else
                userinfo (2,Adaptive_BMS_linalg,`\t???`,g[2],`nothing to do\t???`);
            end if:
        end do:
        Hp,counterBasic:= staircaseMaxElements_basicop (n,xvar,Hp,mon_order,
                                                        counterBasic);
        userinfo (1,Adaptive_BMS_linalg,`\tfailing relations`);
        for h in Hp do
            userinfo (1,Adaptive_BMS_linalg,`\t\t`,[h[2],h[4]]);
        end do:
        if (Hp <> H) then
            Sp:= stabilize (map (h->h[4],Hp),n,xvar,mon_order);
        else
            Sp:= S;
        end if:
        userinfo (3,Adaptive_BMS_linalg,`\tnew staircase`,Sp);
        Gp,counterBasic:= staircaseBorder_basicop (n,xvar,Sp,mon_order,
                                                   counterBasic);
        userinfo (3,Adaptive_BMS_linalg,`\tnew LT for relations`,Gp);
        Gp:= [seq ([s,1,<1>,[]], s in Gp)];
        userinfo (1,Adaptive_BMS_linalg,`\tvalid relations are`);
        for i from 1 to nops(Gp) do
            gp:= Gp[i];
            g,s:= relationBelow (gp,G);
            userinfo (3,Adaptive_BMS_linalg,`\t\t`,g[1],`is below`,gp[1]);
            counterBasic:= counterBasic+1;
            if (not divide (m,gp[1],'m_over_gp')) then
                userinfo (2,Adaptive_BMS_linalg,`\t\t`,gp[1],`does not divide`,m);
                gp[2]:= expand (g[2]*s) mod myprime;
                supp:= Support (gp[2],mon_order);
                gp[3]:= fromPolToVector (n,xvar,supp,gp[2]);
                counterBasic:= counterBasic+2*nops(supp);
                j:= t;
                while (j > 0 and not divide (T[j],gp[1],'span_gp')) do
                    j:=j-1;
                end do:
                if (j <> 0) then gp[4]:= span_gp;
                end if:
            else
                counterBasic:= counterBasic+1;
                divides_mu,h,gp_muh_over_m:= greaterSpan (H,m_over_gp);
                if (divides_mu) then
                    userinfo (2,Adaptive_BMS_linalg,`\t\t`,m,`/`,gp[1],`divides`,h[4]);
                    if (j = 1) then print (ok);
                    end if:
                    supp:= Support (g[2],mon_order);
                    counterBasic:= counterBasic+2*nops(supp);
                    gp[2]:= expand (g[2]*s
                                    - ((DotProduct (multiHankel (n,xvar,Tab,
                                                                 [m/g[1]] mod myprime,
                                                                 supp),
                                                    g[3] mod myprime) mod myprime)
                                       *gp_muh_over_m*h[2])) mod myprime;
                    supp:= Support (gp[2],mon_order);
                    gp[3]:= fromPolToVector (n,xvar,supp,gp[2]);
                    counterBasic:= counterBasic+nops(supp);
                    gp[4]:= m_over_gp;
                else
                    userinfo (2,Adaptive_BMS_linalg,`\t\t`,h);
                    userinfo (2,Adaptive_BMS_linalg,`\t\t`,m,`/`,gp[1],
                              `does not divide any fail(h)`);
                    gp:= g;
                    supp:= Support (gp[2],mon_order);
                    counterBasic:= counterBasic+2*nops(supp);
                    gp[3]:= fromPolToVector (n,xvar,supp,gp[2]);
                    gp[4]:= m_over_gp;
                end if:
            end if:
            Gp[i]:=gp;
            userinfo (1,Adaptive_BMS_linalg,`\t\t`,[gp[2],gp[4]]);
        end do:
        H:= Hp;
        G:= Gp;
        userinfo (1,Adaptive_BMS_linalg,`reduced to`);
        for i from 1 to nops(G) do
            Gp:= map (g->g[2],subsop(i=NULL,G));
            if (Gp <> []) then
                NormalForm (G[i][2], Gp, mon_order,'q');
                G[i][2]:= expand (G[i][2] - add (q[j]*Gp[j],j=1..nops(q)));
                supp:= Support (G[i][2],mon_order);
                G[i][3]:= fromPolToVector (n,xvar,supp,G[i][2]);
                userinfo (1,Adaptive_BMS_linalg,`\t\t`,[G[i][2],G[i][4]]);
            end if:
        end do:
        S:= Sp;
    end do:
    return G,counterBasic;
end proc:

ScalarFGLM_basicop:= proc (n,stopmon,sizeS,sizeGb,xvar,mon_ord)
local r,s,counterBasic;
    r:= nops (listMonLessOrEqualThan (n,xvar,mon_ord,stopmon));
    counterBasic:= r^3/3-r^2/2+r/6; # useful staircase
    s:= sizeS;
    # counterBasic:= counterBasic+s^3/3-s^2/2+s/6;
    counterBasic:= counterBasic+s*(2*s-1)*sizeGb;
    return counterBasic;
end proc:

MergeList:= proc (L1,L2,mon_order)
local L,LL,i,j;
    L:= [];
    i:= 1; j:= 1;
    while (i <= nops (L1) and j <= nops (L2)) do
        if (TestOrder (L1[i],L2[j],mon_order)) then
            L:=[op(L),L1[i]];
            if (L1[i] = L2[j]) then j:= j+1;
            end if:
            i:= i+1;
        else
            L:=[op(L),L2[j]];
            j:= j+1;
        end if:
    end do:
    if (i > nops (L1))
    then L:= [op(L),op(j..-1,L2)];
    else L:= [op(L),op(i..-1,L1)];
    end if:
    return L;
end proc:

Adaptive_ScalarFGLM_basicop:= proc (Tab, sizeS, LM,
                                    n:= 1, xvar:=listVar (n,'x'),
                                    mon_order:= tdeg (op(xvar)))
local L,S,Gb,Gp,r,tau,Sp,H,taup,alpha,i,g;
local counterBasic;
    counterBasic:=0;
    L := [1];
    S := [];
    Gp:= [];
    r := 0;
    userinfo (2,Adaptive_ScalarFGLM,`List of monomials`,L);
    while (L <> []) do
        tau:= L[1];
        userinfo (1,Adaptive_ScalarFGLM,`New monomial`,tau);
        Sp:= [op(S),tau];
        # H:= multiHankel (n,xvar,Tab,Sp,Sp);
        userinfo (3,Adaptive_ScalarFGLM,`Matrix`,print(H));
        counterBasic:= counterBasic+(r+1)*(r+2)/2;
        if (not tau in LM) then
            S:= Sp;
            r:= r+1;
            userinfo (1,Adaptive_ScalarFGLM,`Full rank:`,r);
            counterBasic:= counterBasic+n;
            # L:= [op(({op(L)} minus {tau}) union {seq (xvar[i]*tau, i=1..n)})];
            # L:= sortListMon (remove (l->`or` (seq (divide (l,g), g in Gp)),
            #                          L), xvar, mon_order);
            L:= MergeList (L[2..-1],
                           remove (ll->`or` (seq (divide (l,g), g in Gp)),
                                   [seq (xvar[n-i]*tau,i=0..n-1)]),
                           mon_order);
            L:= Groebner[Basis](L,mon_order);
            userinfo (2,Adaptive_ScalarFGLM,`List of monomials`,L);
            if (r >= sizeS) then
                userinfo (1,Adaptive_ScalarFGLM,`Useful staircase of size`,r);
                userinfo (2,Adaptive_ScalarFGLM,`Useful staircase:`, S);
                Gb:= [];
                # Gp:= [op(Gp), op(L),
                #       op({op(listMon (n, xvar, mon_order, degree (tau,xvar)+1))}
                #          minus {op(S)})];
                # Gp:= sortListMon (fgb_gbasis (Gp,0,xvar,[]), xvar,
                # mon_order);
                Gp:= LM;
                userinfo (2,Adaptive_ScalarFGLM,
                          `Potential leading monomials:`, Gp);
                for taup in Gp do
                    userinfo (1,Adaptive_ScalarFGLM,`*** monomial`, taup, `***`);
                    Sp:= select (s->TestOrder (s,taup,mon_order),S);
                    # H:= multiHankel (n,xvar,Tab,Sp,Sp);
                    # userinfo (3,Adaptive_ScalarFGLM,`Solving:`,
                    #           print(H,multiHankel (n,xvar,Tab,Sp,[taup])));
                    r:= nops (Sp);
                    counterBasic:= counterBasic+r*(r+1)/2;
                    # alpha:=LinearSolve (H,multiHankel (n,xvar,Tab,Sp,[taup]));
                    counterBasic:= counterBasic+2*r;
                    # alpha:= taup - DotProduct (alpha,Sp);
                    userinfo (1,Adaptive_ScalarFGLM,`New polynomial`,alpha);
                    Gb:= [op(Gb), alpha];
                end do:
                return counterBasic;
            end if:
        else
            userinfo (1,Adaptive_ScalarFGLM,`Not full rank:`,r);
            Gp:= [op(Gp),tau];
            L := sortListMon (remove (l->divide (l,tau),L), xvar, mon_order);
            userinfo (2,Adaptive_ScalarFGLM,`List of monomials`,L);
        end if:
    end do:
    error "Run Scalar-FGLM";
end proc:

PolynomialScalarFGLM_basicop:= proc (Tab,n,xvar,col_maxmon,row_maxmon,
                                     mon_ord,myprime)
local rows_mon, cols_mon, lcm_mon, all_mon, H, B, S, Z, G, Gp, R, Rp, F, r,c,x;
local fail_and_shift, i, f, lmf, j, g, z, zCreated;
local counterBasic;
    counterBasic:= 0:
    rows_mon:= listMonLessOrEqualThan (n,xvar,mon_ord, row_maxmon);
    cols_mon:= listMonLessOrEqualThan (n,xvar,mon_ord, col_maxmon);
    lcm_mon := lcm (op(rows_mon))*lcm (op(cols_mon));
    all_mon := sort ([op({seq (seq (r*c, r in rows_mon),c in cols_mon)})],
                     (a,b)->TestOrder (a,b,mon_ord));
    userinfo (1,PolynomialScalarFGLM,`monoms:`,all_mon);
    H:= expand (lcm_mon*subs({seq (x=1/x, x in xvar)},
                             from2SetsToPolynomial (n,xvar,Tab,rows_mon,
                                                    cols_mon) mod myprime));
    B:= [seq ([x^(degree (lcm_mon,x)+1),0], x in xvar)];
    S:= [];
    Z:= [1];
    G:= [];
    Gp:=[];
    R:= [[H,1]]; # current relations
    userinfo (2,PolynomialScalarFGLM,`\tnew current relation`,R[1]);
    Rp:=[1];
    F:= [] ;     # failing relations
    while (Rp <> []) do
        # if (nops (F) > 90) then
        #     F:=F[-90..-1];
        # end if:
        R,z:= sort (R,(a,b)->TestOrder (LeadingMonomial (a[2],mon_ord),
                                        LeadingMonomial (b[2],mon_ord),
                                        mon_ord),output=[sorted,permutation]);
        Rp := Rp[z];
        F  := sort (F,(a,b)->TestOrder (LeadingMonomial (b[1],mon_ord),
                                        LeadingMonomial (a[1],mon_ord),
                                        mon_ord));
        userinfo (1,PolynomialScalarFGLM,nops(F),`failing relations`);
        userinfo (1,PolynomialScalarFGLM,nops(R),`relations to be tested`);
        userinfo (1,PolynomialScalarFGLM,nops(G),`succeeding relations`);
        userinfo (2,PolynomialScalarFGLM,`current relations`,map (r->r[2],R));
        userinfo (2,PolynomialScalarFGLM,`failing relations`,map (f->f[2],F));
        r:= R[1];
        userinfo (1,PolynomialScalarFGLM,`testing`,r[2]);
        if (LeadingMonomial (r[2],mon_ord) in cols_mon) then
            fail_and_shift:= [FailingWhenShiftedBy (r,all_mon,lcm_mon,mon_ord,
                                                    B,rows_mon)];
            counterBasic:= counterBasic + nops(all_mon);
        else fail_and_shift:= [-1,0] # relation on the border to close the staircase
        end if:
        if (fail_and_shift[1] = -1) then # Good relation
            userinfo (1,PolynomialScalarFGLM,`\tOK \\o/ with a shift`,fail_and_shift[2]);
            r:= [r[1],r[2],LeadingMonomial (r[2],mon_ord),fail_and_shift[2]];
            userinfo (1,PolynomialScalarFGLM,`\tnew relation!`);
            userinfo (2,PolynomialScalarFGLM,r);
            G := [op(G),r];
            Gp:= [op(Gp),r[3]];
            R := subsop (1=NULL,R);
            Rp:= subsop (1=NULL,Rp);
            for i from 1 to nops (R) do
                # z:= nf2 (R[i],[r[1..2]],mon_ord);
                # if (lm(z,mon_ord) <> lm(R[i],mon_ord))
                # then printf ("change of LM when reducing by %a!!\n%a\n%a\n",
                #              r[1..2],z,R[i]);
                # end if:
                # R[i]:= z;
                R[i],counterBasic:= nf2_basicop (R[i],[r[1..2]],mon_ord,
                                                 counterBasic,myprime);
            end do:
        else
            userinfo (1,PolynomialScalarFGLM,`\tFAIL! when shifting by`,
                      fail_and_shift[1]);
            F:= [op(F),r];
            for j from 2 to nops(R) do
                Z,counterBasic:= nf_basicop (R[j],[r,op(B)],mon_ord,counterBasic,
                                             myprime);
                z:= LeadingMonomial (Z[2],mon_ord);
                if (z <> Rp[j]) then Rp[j]:= z
                end if:
                R[j] := Z;
            end do:
            R := subsop (1=NULL,R);
            Rp:= subsop (1=NULL,Rp);
            R,z:= sort (R,(a,b)->TestOrder (LeadingMonomial (b[1],mon_ord),
                                            LeadingMonomial (a[1],mon_ord),
                                            mon_ord),output=[sorted,permutation]);
            userinfo (2,PolynomialScalarFGLM,`\tupdating R to`,R);
            Rp := Rp[z];
            # if (fail_and_shift[1] in S) then printf ("bug fail\n");
            # end if;
            S:= [op(S),LeadingMonomial(r[2],mon_ord),fail_and_shift[1]];
            S:= stabilize (S,n,xvar,mon_ord);
            Z,counterBasic:= border_basicop (xvar,S,mon_ord,counterBasic);
            userinfo (2,PolynomialScalarFGLM,`\tnew current relations in`,Z);
            for z in Z do
                if (z in Gp or z in Rp) then next;
                end if:
                Rp:= [op(Rp),z];
                zCreated:= false;
                userinfo (2,PolynomialScalarFGLM,`\tnew current relation`,z);
                i:= nops(F)-1;
                while (not zCreated and i > 0) do
                    f:= F[i];
                    lmf:= lm(f,mon_ord);
                    for j from i+1 to nops (F) do
                        g:= F[j];
                        if (divide (lmf,lm(g,mon_ord),'q') and
                            LeadingMonomial (g[2],mon_ord)*q = z) then
                            z,counterBasic:= nf_basicop (f,[g,op(B),op(F)],
                                                         mon_ord,counterBasic,
                                                         myprime);
                            # Creation by division
                            zCreated:= true;
                            userinfo (2,PolynomialScalarFGLM,
                                      `\tby division of `,f,`and`,g);
                            break;
                        end if:
                    end do:
                    i:= i-1;
                end do:
                i:= nops(F);
                while (not zCreated and i > 0) do # No creation by division
                    f  := F[i];
                    lmf:= map (g->LeadingMonomial (g,mon_ord),f);
                    if (divide (z,lmf[2],'q')) then
                        z,counterBasic:= nf_basicop (q*f,[op(B),op(F),f],mon_ord,
                                                     counterBasic,myprime);
                        counterBasic:= counterBasic+nops(f[1])+nops(f[2]);
                        userinfo (2,PolynomialScalarFGLM,
                                  `\tnot by division of`,f);
                        zCreated:= true;
                    end if:
                    i:= i-1;
                end do:
                if (not zCreated) then printf ("bug not created\n");
                end if:
                z,counterBasic:= nf2_basicop (z,map (g->g[1..2],G),mon_ord,
                                              counterBasic,myprime);
                userinfo (3,PolynomialScalarFGLM,`\treduced to`,z);
                R := [op(R),z];
            end do:
        end if:
    end do:
    return counterBasic;#, sort (G,(a,b)->TestOrder (a[1],b[1],mon_ord));
end proc:

orthProj_basicop:= proc (f,p,m,n,b,xvar,Tab,counter, myprime)
local g,xalph;
local counterBasic;
    g:= f;
    counterBasic:= counter;
    for xalph in b do
        counterBasic:= counterBasic + nops(g);
        g:= g - fromPolToTabRelation (g*m[xalph],n,xvar,Tab)*p[xalph] mod myprime;
    end do:
    return g,counterBasic;
end proc:

AGbb_basicop:= proc (Tab,n,xvar,a,mon_order,myprime)
local b,m,mm,c,d,cc,nn,s,t,l,p,q,k;
local xalph,palph,xgam,xgam_palph,malph,xgam_palphEval,boolgam,supp;
local counterBasic;
    counterBasic:= 0;
    b:=[];
    c:=[];
    d:= [];
    nn:=[1];
    s:= a;
    t:= a;
    # l:= 0;
    p:= table ([]); q:= table ([]); k:= table ([]);
    userinfo (2,AGbb,`set of terms`,nn);
    while (nn <> []) do
        for xalph in nn do
            palph,counterBasic:= orthProj_basicop (xalph,p,m,n,b,xvar,Tab,
                                                   counterBasic,myprime);
            userinfo (1,AGbb,`palpha`,alph);
            p[xalph]:= palph;
            boolgam:= false;
            for xgam in t do
                userinfo (2,AGbb,`xgamma`,xgam);
                xgam_palph    := xgam*palph mod myprime;
                # counterBasic  := counterBasic+2*nops(palph);
                xgam_palphEval:= fromPolToTabRelation (xgam_palph,n,xvar,
                                                       Tab) mod myprime;
                counterBasic  := counterBasic+nops(palph);
                coeffs (xgam_palph,xvars,'supp'):
                supp:= {supp}:
                if (supp subset {op(a)} and
                    xgam_palphEval <> 0) then
                    boolgam:= true;
                    userinfo (2,AGbb,`\txgam`,xgam,`!`);
                    break;
                end if:
            end do:
            if (boolgam) then
                malph:= xgam/xgam_palphEval mod myprime;
                # counterBasic:= counterBasic+nops(xgam);
                m[xalph]:= malph;
                userinfo (2,AGbb,`\tmalph`,malph);
                # q[xalph],counterBasic:= orthProj_basicop (malph,q,p,n,b,xvar,Tab,
                #                                           counterBasic,myprime);
                b:= [op({op(b),xalph})];
                userinfo (2,AGbb,`\tnew b`,b);
                s:= remove (i->i=xalph,s);
                userinfo (2,AGbb,`\tnew s`,s);
                mm:= [op(mm),xgam];
                c:= [op({op(c),xgam})];
                userinfo (2,AGbb,`\tnew c`,c);
                t:= remove (i->i=xgam,t);
                userinfo (2,AGbb,`\tnew t`,t);
            else
                userinfo (2,AGbb,`\tno xgam !!`);
                k[xalph]:= palph;
                userinfo (1,AGbb,`relation`,alph,`\n\t\t OK`);
                d:= [op({op(d),xalph})];
                userinfo (2,AGbb,`\tnew d`,d);
                s:= remove (i->i=xalph,s);
                userinfo (2,AGbb,`\tnew s`,s);
            end if:
        end do:
        nn:= nnext (n,xvar,b,d,c,s);
        userinfo (2,AGbb,`set of terms`,nn);
    end do:
    return counterBasic;#[b,p,m,q,k,d];
end proc:
