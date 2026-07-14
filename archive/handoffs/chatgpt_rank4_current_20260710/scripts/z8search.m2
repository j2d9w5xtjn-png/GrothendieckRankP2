-- z8search.m2
-- Mixed characteristic: R = Z/8Z (the first open mixed-char base for order 4:
-- m = (2), m^3 = 0, but m^2 != 0 and 2m != 0, so outside Schoof 2001).
--
-- Setup (structure constants over Z/8, computed via GB over ZZ with 8 in J):
--   A = R.1 + R.e1 + R.e2 + R.e3 free rank 4, augmentation eps(e_i) = 0.
--   e_i e_j = sum_r M_(i,j,r) e_r,  M_(i,j,r) = fib_(i,j,r) + 2*d_(i,j,r),
--     so the special fiber A/2A is the standard rank-4 local F_2-algebra
--     (branch 1: F2[x,y]/(x^2,y^2); branch 2: F2[t]/t^4).
--   Delta(e_i) = e_i(x)1 + 1(x)e_i + sum_{j,k>=1} c_(i,j,k) e_j(x)e_k.
--   [2]^# = phi = mu o Delta;   note phi(e_i) = 2 e_i + sum c_(i,j,k) e_j e_k
--   (the 2e_i term matters in mixed characteristic).
--
-- Equations J (all understood mod 8, so J includes the generator 8):
--   associativity, Delta multiplicative, coassociativity,
--   special fiber killed by 2:  phi(e_i) == 0 mod 2, imposed as
--     phi(e_i)_r = 2*w_(i,r) with witness variables w.
--
-- Goal: are all coordinates of P4_i = phi(phi(e_i)) in J?
-- Ideal membership over ZZ proves the identity [4]^# = 0 for ALL parameter
-- values in ALL Z/8-algebras (in particular Z/8 itself), i.e. no
-- counterexample among rank-4 bialgebra deformations with fiber killed by 2.

cIx = flatten flatten for i from 1 to 3 list for j from 1 to 3 list
          for k from 1 to 3 list c_(i,j,k);
dIx = flatten flatten for i from 1 to 3 list for j from i to 3 list
          for r from 1 to 3 list d_(i,j,r);
wIx = flatten for i from 1 to 3 list for r from 1 to 3 list w_(i,r);

Q = ZZ[ cIx | dIx | wIx ];

runZ8 = (fibKeys, name) -> (
    << endl << "########## Z/8 branch: " << name << " ##########" << endl;
    Mc := (i,j,r) -> (
        ii := min(i,j); jj := max(i,j);
        (if member((ii,jj,r), fibKeys) then 1_Q else 0_Q) + 2*d_(ii,jj,r));
    ebas := i -> apply(4, k -> if k == i then 1_Q else 0_Q);
    idx2 := (a,b) -> 4*a + b;
    idx3 := (a,b,cc) -> 16*a + 4*b + cc;
    Stab := hashTable flatten for a from 0 to 3 list for b from 0 to 3 list
        (a,b) => (if a == 0 then ebas b else if b == 0 then ebas a
                  else {0_Q, Mc(a,b,1), Mc(a,b,2), Mc(a,b,3)});
    DEl := for i from 0 to 3 list (
        if i == 0 then apply(16, t -> if t == 0 then 1_Q else 0_Q)
        else (
            v := new MutableList from toList(16:0_Q);
            v#(idx2(i,0)) = v#(idx2(i,0)) + 1_Q;
            v#(idx2(0,i)) = v#(idx2(0,i)) + 1_Q;
            for j from 1 to 3 do for k from 1 to 3 do
                v#(idx2(j,k)) = v#(idx2(j,k)) + c_(i,j,k);
            toList v));
    mulA := (u,v) -> (
        out := new MutableList from toList(4:0_Q);
        for i from 0 to 3 do if u#i != 0 then
        for j from 0 to 3 do if v#j != 0 then (
            Sij := Stab#(i,j);
            for r from 0 to 3 do if Sij#r != 0 then
                out#r = out#r + u#i * v#j * Sij#r);
        toList out);
    assocV := flatten flatten for i from 1 to 3 list for j from 1 to 3 list
        for k from 1 to 3 list (
        u := mulA(mulA(ebas i, ebas j), ebas k);
        ww := mulA(ebas i, mulA(ebas j, ebas k));
        apply(4, t -> u#t - ww#t));
    DofVec := v -> (
        out := new MutableList from toList(16:0_Q);
        for r from 0 to 3 do if v#r != 0 then (
            D := DEl#r;
            for t from 0 to 15 do if D#t != 0 then out#t = out#t + v#r * D#t);
        toList out);
    mulT2 := (u,v) -> (
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
    compatV := flatten for i from 1 to 3 list for j from i to 3 list (
        lhs := DofVec(Stab#(i,j));
        rhs := mulT2(DEl#i, DEl#j);
        apply(16, t -> lhs#t - rhs#t));
    coassocV := for i from 1 to 3 list (
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
    phiL := for i from 0 to 3 list (
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
    for i from 1 to 3 do assert((phiL#i)#0 == 0);
    -- sanity: phi(e_i) = 2e_i + quadratic terms
    P4L := for i from 1 to 3 list (
        p := phiL#i;
        out := new MutableList from toList(4:0_Q);
        for r from 0 to 3 do if p#r != 0 then (
            ph := phiL#r;
            for t from 0 to 3 do if ph#t != 0 then
                out#t = out#t + p#r * ph#t);
        toList out);
    fiber2E := flatten for i from 1 to 3 list
        for r from 1 to 3 list ((phiL#i)#r - 2*w_(i,r));
    eqs := unique select(
        flatten(assocV | compatV | coassocV) | fiber2E, f -> f != 0);
    J := ideal eqs + ideal(8_Q);
    bL := unique select(flatten P4L, f -> f != 0);
    << "#vars: " << numgens Q << "  #eqs: " << numgens J
      << "  #P4 coordinates: " << #bL << endl;
    done := false;
    for dg in {2,3,4,5,6,8,10} do (
        if done then break;
        << "-- gb DegreeLimit " << dg << ": " << flush;
        elapsedTime G := gb(J, DegreeLimit => dg);
        rems := apply(bL, b -> b % G);
        nz := select(rems, r -> r != 0);
        << "   nonzero remainders: " << #nz << " / " << #bL
          << "   (1 in J? " << (1_Q % G == 0) << ")" << endl;
        if #nz == 0 then (
            << "   ==> ALL P4 coordinates in J (identity mod 8 certified)." << endl;
            done = true));
    if not done then (
        << "-- full gb: " << flush;
        elapsedTime G := gb J;
        rems := apply(bL, b -> b % G);
        nz := select(rems, r -> r != 0);
        << "   nonzero remainders after full gb: " << #nz << " / " << #bL
          << "   (1 in J? " << (1_Q % G == 0) << ")" << endl;
        if #nz == 0 then << "   ==> ALL P4 coordinates in J." << endl
        else << "   NOT all in J -- potential counterexample locus; investigate!" << endl);
    );

fib1 = set { (1,2,3) };              -- fiber F2[x,y]/(x^2,y^2)  (covers alpha_2 x mu_2 !)
fib2t = set { (1,1,2), (1,2,3) };    -- fiber F2[t]/(t^4)

runZ8(fib1,  "fiber F2[x,y]/(x^2,y^2) over Z/8")
runZ8(fib2t, "fiber F2[t]/(t^4) over Z/8")

<< endl << "DONE z8search" << endl;
