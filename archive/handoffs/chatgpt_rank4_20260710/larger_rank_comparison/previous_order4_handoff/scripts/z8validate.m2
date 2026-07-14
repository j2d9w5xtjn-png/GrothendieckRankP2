-- z8validate.m2
-- Validate the Z/8 structure-constant machinery of z8search.m2 against the
-- hand-computed point mu_4 over Z/8:
--   A = (Z/8)[g]/(g^4-1), t = g-1, e_i = t^i, Delta(g) = g(x)g.
-- Relations mod 8:  t^4 = 4t+2t^2+4t^3,  t^5 = 4t^2+2t^3,  t^6 = 4t^2+4t^3.
-- Delta(t)   = t(x)1+1(x)t+t(x)t
-- Delta(t^2) = t^2(x)1+1(x)t^2+t^2(x)t^2+2t(x)t+2t^2(x)t+2t(x)t^2
-- Delta(t^3) = t^3(x)1+1(x)t^3+t^3(x)t^3+3(t^2(x)t+t(x)t^2+t^3(x)t+t(x)t^3
--              +t^3(x)t^2+t^2(x)t^3)+6t^2(x)t^2
-- Expected: all bialgebra equations vanish mod 8; fiber-killed-by-2 FAILS
-- (phi(t) = 2t + t^2 has odd t^2-coefficient); P4 = 0 mod 8 (mu_4 killed by 4).

cIx = flatten flatten for i from 1 to 3 list for j from 1 to 3 list
          for k from 1 to 3 list c_(i,j,k);
dIx = flatten flatten for i from 1 to 3 list for j from i to 3 list
          for r from 1 to 3 list d_(i,j,r);

Q = ZZ[ cIx | dIx ];

fib2t = set { (1,1,2), (1,2,3) };
Mc = (i,j,r) -> (
    ii := min(i,j); jj := max(i,j);
    (if member((ii,jj,r), fib2t) then 1_Q else 0_Q) + 2*d_(ii,jj,r));
ebas = i -> apply(4, k -> if k == i then 1_Q else 0_Q);
idx2 = (a,b) -> 4*a + b;
idx3 = (a,b,cc) -> 16*a + 4*b + cc;
Stab = hashTable flatten for a from 0 to 3 list for b from 0 to 3 list
    (a,b) => (if a == 0 then ebas b else if b == 0 then ebas a
              else {0_Q, Mc(a,b,1), Mc(a,b,2), Mc(a,b,3)});
DEl = for i from 0 to 3 list (
    if i == 0 then apply(16, t -> if t == 0 then 1_Q else 0_Q)
    else (
        v := new MutableList from toList(16:0_Q);
        v#(idx2(i,0)) = v#(idx2(i,0)) + 1_Q;
        v#(idx2(0,i)) = v#(idx2(0,i)) + 1_Q;
        for j from 1 to 3 do for k from 1 to 3 do
            v#(idx2(j,k)) = v#(idx2(j,k)) + c_(i,j,k);
        toList v));
mulA = (u,v) -> (
    out := new MutableList from toList(4:0_Q);
    for i from 0 to 3 do if u#i != 0 then
    for j from 0 to 3 do if v#j != 0 then (
        Sij := Stab#(i,j);
        for r from 0 to 3 do if Sij#r != 0 then
            out#r = out#r + u#i * v#j * Sij#r);
    toList out);
assocV = flatten flatten for i from 1 to 3 list for j from 1 to 3 list
    for k from 1 to 3 list (
    u := mulA(mulA(ebas i, ebas j), ebas k);
    ww := mulA(ebas i, mulA(ebas j, ebas k));
    apply(4, t -> u#t - ww#t));
DofVec = v -> (
    out := new MutableList from toList(16:0_Q);
    for r from 0 to 3 do if v#r != 0 then (
        D := DEl#r;
        for t from 0 to 15 do if D#t != 0 then out#t = out#t + v#r * D#t);
    toList out);
mulT2 = (u,v) -> (
    out := new MutableList from toList(16:0_Q);
    for a from 0 to 3 do for b from 0 to 3 do (
        ua := u#(idx2(a,b));
        if ua != 0 then
        for a2 from 0 to 3 do for b2 from 0 to 3 do (
            vb := v#(idx2(a2,b2));
            if vb != 0 then (
                co := ua*vb;
                SA := Stab#(a,a2); SB := Stab#(b,b2);
                for k from 0 to 3 do if SA#k != 0 then
                for l from 0 to 3 do if SB#l != 0 then
                    out#(idx2(k,l)) = out#(idx2(k,l)) + co*SA#k*SB#l)));
    toList out);
compatV = flatten for i from 1 to 3 list for j from i to 3 list (
    lhs := DofVec(Stab#(i,j));
    rhs := mulT2(DEl#i, DEl#j);
    apply(16, t -> lhs#t - rhs#t));
coassocV = for i from 1 to 3 list (
    out := new MutableList from toList(64:0_Q);
    D := DEl#i;
    for r from 0 to 3 do for s from 0 to 3 do (
        u := D#(idx2(r,s));
        if u != 0 then (
            Dr := DEl#r;
            for a from 0 to 3 do for b from 0 to 3 do
                if Dr#(idx2(a,b)) != 0 then
                    out#(idx3(a,b,s)) = out#(idx3(a,b,s)) + u*Dr#(idx2(a,b));
            Ds := DEl#s;
            for b from 0 to 3 do for cc from 0 to 3 do
                if Ds#(idx2(b,cc)) != 0 then
                    out#(idx3(r,b,cc)) = out#(idx3(r,b,cc)) - u*Ds#(idx2(b,cc))));
    toList out);
phiL = for i from 0 to 3 list (
    if i == 0 then ebas 0
    else (
        D := DEl#i;
        out := new MutableList from toList(4:0_Q);
        for j from 0 to 3 do for k from 0 to 3 do
            if D#(idx2(j,k)) != 0 then (
                Sjk := Stab#(j,k);
                for r from 0 to 3 do if Sjk#r != 0 then
                    out#r = out#r + D#(idx2(j,k))*Sjk#r);
        toList out));
P4L = for i from 1 to 3 list (
    p := phiL#i;
    out := new MutableList from toList(4:0_Q);
    for r from 0 to 3 do if p#r != 0 then (
        ph := phiL#r;
        for t from 0 to 3 do if ph#t != 0 then
            out#t = out#t + p#r * ph#t);
    toList out);

-- the mu_4 point
pt = hashTable {
    c_(1,1,1) => 1,
    c_(2,1,1) => 2, c_(2,2,1) => 2, c_(2,1,2) => 2, c_(2,2,2) => 1,
    c_(3,2,1) => 3, c_(3,1,2) => 3, c_(3,3,1) => 3, c_(3,1,3) => 3,
    c_(3,3,2) => 3, c_(3,2,3) => 3, c_(3,2,2) => 6, c_(3,3,3) => 1,
    d_(1,3,1) => 2, d_(1,3,2) => 1, d_(1,3,3) => 2,
    d_(2,2,1) => 2, d_(2,2,2) => 1, d_(2,2,3) => 2,
    d_(2,3,2) => 2, d_(2,3,3) => 1,
    d_(3,3,2) => 2, d_(3,3,3) => 2 };
evalP = f -> (
    v := sub(f, for x in gens Q list (x => (if pt#?x then pt#x else 0)));
    lift(v, ZZ) % 8);

eqs = flatten(assocV | compatV | coassocV);
<< "mu_4/Z8: #bialgebra equations violated mod 8: "
  << #select(eqs, f -> evalP f != 0) << "  (expect 0)" << endl;
<< "mu_4/Z8: phi(t) coords mod 8: " << apply(phiL#1, evalP)
  << "  (expect {0,2,1,0}: not killed by 2)" << endl;
<< "mu_4/Z8: phi(t^2) coords mod 8: " << apply(phiL#2, evalP)
  << "  (expect {0,4,6,0})" << endl;
<< "mu_4/Z8: phi(t^3) coords mod 8: " << apply(phiL#3, evalP)
  << "  (expect {0,0,4,0})" << endl;
<< "mu_4/Z8: P4 coords mod 8 (expect all 0): "
  << apply(P4L, v -> apply(v, evalP)) << endl;
<< "DONE z8validate" << endl;
