-- s2gen.m2 (session 4): ideal-membership upgrade of the S' probe (s2check.py)
-- over R = k[eps]/eps^3, k an ARBITRARY F_2-algebra.
--
-- S' (THEORY_order4.md section 7):  phi(I) \subseteq m (ker phi \cap I).
-- Over curvilinear R with fiber killed by 2, S' at e_i is EQUIVALENT to the
-- vanishing of the polynomial defect
--     delta_i := phi(v_i),   v_i := phi(e_i)/eps  (any eps-division),
-- because the division is unique up to u in ann(eps)*I and
-- phi(u) = eps^2 phi(w) with phi(w) in eps*I (fiber2), so phi(u) = 0 mod J.
-- [In coordinates: v_{i,r} = digit-shift of phi(e_i)_r after dropping the
-- eps^0-digit, which is itself a fiber2 generator of J.]
--
-- TARGET: all eps-digit coefficients of all coordinates of delta_i lie in
-- J = (bialgebra equations) + (fiber2 equations).  Success = S'-UNIVERSALITY
-- at depth 3 for EVERY F_2-algebra k at once; then THEORY Thm 7.1 gives:
-- every free rank-4 bialgebra with killed-by-2 local fiber over EVERY
-- socle-line extension of k[eps]/eps^3 is killed by 4.
-- SAT counterpart (k = F_2 exact): s2check.py, [S2] -> unsat, gates passed.
--
-- Equation generator copied from gensearch.m2/minassoc.m2 (gate-validated);
-- gates rerun below: 16.2 must satisfy all equations AND have all delta
-- digits evaluate to 0 (hand check: delta_1 = phi(eps*xy) = eps*phi(xy) = 0).
-- (16.1 is NOT a gate here: its fiber is not killed by 2, so the division
-- that defines delta is meaningless there.)

kk = ZZ/2

cIx = flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
          for k from 1 to 3 list for d from 0 to 2 list c_(i,j,k,d);
mIx = flatten flatten flatten for i from 1 to 3 list for j from i to 3 list
          for r from 1 to 3 list for d from 1 to 2 list m_(i,j,r,d);

Q = kk[ {eps} | cIx | mIx ];
epsI = ideal(eps^3);
red = f -> f % epsI;

digitsQ = f -> (
    f = red f;
    f0 := sub(f, {eps => 0});
    g  := (f - f0)//eps;
    g0 := sub(g, {eps => 0});
    h  := (g - g0)//eps;
    h0 := sub(h, {eps => 0});
    {f0, g0, h0}
    );

ebas = i -> apply(4, k -> if k == i then 1_Q else 0_Q);
idx2 = (a,b) -> 4*a + b;
idx3 = (a,b,cc) -> 16*a + 4*b + cc;

Cc = (i,j,k) -> c_(i,j,k,0) + eps*c_(i,j,k,1) + eps^2*c_(i,j,k,2);

buildData = fib -> (
    Mc := (i,j,r) -> (
        ii := min(i,j); jj := max(i,j);
        (if member((ii,jj,r), fib) then 1_Q else 0_Q)
          + eps*m_(ii,jj,r,1) + eps^2*m_(ii,jj,r,2));
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
                v#(idx2(j,k)) = v#(idx2(j,k)) + Cc(i,j,k);
            apply(toList v, red)));
    mulA := (u,v) -> (
        out := new MutableList from toList(4:0_Q);
        for i from 0 to 3 do if u#i != 0 then
        for j from 0 to 3 do if v#j != 0 then (
            Sij := Stab#(i,j);
            for r from 0 to 3 do if Sij#r != 0 then
                out#r = out#r + u#i * v#j * Sij#r);
        apply(toList out, red));
    assocV := flatten flatten for i from 1 to 3 list for j from 1 to 3 list
        for k from 1 to 3 list (
        u := mulA(mulA(ebas i, ebas j), ebas k);
        w := mulA(ebas i, mulA(ebas j, ebas k));
        apply(4, t -> u#t + w#t));
    DofVec := v -> (
        out := new MutableList from toList(16:0_Q);
        for r from 0 to 3 do if v#r != 0 then (
            D := DEl#r;
            for t from 0 to 15 do if D#t != 0 then out#t = out#t + v#r * D#t);
        apply(toList out, red));
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
        apply(toList out, red));
    compatV := flatten for i from 1 to 3 list for j from i to 3 list (
        lhs := DofVec(Stab#(i,j));
        rhs := mulT2(DEl#i, DEl#j);
        apply(16, t -> lhs#t + rhs#t));
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
                        out#(idx3(r,b,cc)) = out#(idx3(r,b,cc)) + u*Ds#(idx2(b,cc))));
        apply(toList out, red));
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
            apply(toList out, red)));
    for i from 1 to 3 do assert((phiL#i)#0 == 0);
    fiber2E := flatten for i from 1 to 3 list
        for r from 1 to 3 list (digitsQ((phiL#i)#r))#0;
    -- v_i = phi(e_i)/eps with the eps^0-digit dropped (it is a fiber2 gen);
    -- coordinates v_{i,r} as ring elements of R = k[eps]/eps^3
    vL := for i from 1 to 3 list (
        for r from 0 to 3 list (
            d := digitsQ((phiL#i)#r);
            red(d#1 + eps*(d#2))));
    -- delta_i = phi(v_i) = sum_r v_{i,r} phi(e_r)   (phi is R-linear)
    deltaL := for i from 0 to 2 list (
        v := vL#i;
        out := new MutableList from toList(4:0_Q);
        for r from 1 to 3 do if v#r != 0 then (
            ph := phiL#r;
            for t from 0 to 3 do if ph#t != 0 then
                out#t = out#t + v#r * ph#t);
        apply(toList out, red));
    hashTable {
        "assocV" => assocV, "compatV" => compatV, "coassocV" => coassocV,
        "phiL" => phiL, "deltaL" => deltaL, "fiber2E" => fiber2E }
    );

collectEqs = data -> (
    vecs := data#"assocV" | data#"compatV" | data#"coassocV";
    hopf := unique select(flatten apply(vecs, v -> flatten apply(v, digitsQ)), f -> f != 0);
    fib2 := unique select(data#"fiber2E", f -> f != 0);
    (hopf, fib2)
    );

collectDelta = data -> unique select(
    flatten apply(data#"deltaL", v -> flatten apply(v, digitsQ)), f -> f != 0);

evalAt = (f, pt) -> (
    L := for v in gens Q list (v => (if pt#?v then pt#v else 0_kk));
    sub(f, L)
    );

fib1 = set { (1,2,3) };
fib2t = set { (1,1,2), (1,2,3) };

------------------------------------------------------------------
-- VALIDATION (gate: handoff 16.2 -- fiber2 holds there, S' holds by hand)
------------------------------------------------------------------
<< "=== building data (fiber xy) ===" << endl;
elapsedTime data1 = buildData fib1;
<< "=== building data (fiber t^4) ===" << endl;
elapsedTime data2 = buildData fib2t;

pt162 = hashTable { c_(1,2,1,2) => 1_kk,
    c_(3,1,2,0) => 1_kk, c_(3,2,1,0) => 1_kk, c_(3,2,3,2) => 1_kk };
(hopf1, f2eq1) = collectEqs data1;
<< "16.2 hopf equations violated: "
  << #select(hopf1, f -> evalAt(f, pt162) != 0) << " (expect 0)" << endl;
<< "16.2 fiber2 violated: "
  << #select(f2eq1, f -> evalAt(f, pt162) != 0) << " (expect 0)" << endl;
<< "16.2 delta digits nonzero: "
  << #select(collectDelta data1, f -> evalAt(f, pt162) != 0)
  << " (expect 0: S' holds at 16.2, delta_1 = phi(eps xy) = 0)" << endl;
-- trivial point (all deformations 0): phi(e_i) has eps-digits 0 => v = 0 => delta = 0
pt0 = hashTable {};
<< "trivial point delta digits nonzero: "
  << #select(collectDelta data1, f -> evalAt(f, pt0) != 0) << " (expect 0)" << endl;

------------------------------------------------------------------
-- MAIN: are all delta digits in J = (hopf) + (fiber2)?
------------------------------------------------------------------
Q2 = kk[ cIx | mIx ];
toQ2 = map(Q2, Q, {0_Q2} | (gens Q2));

runBranch = (data, name) -> (
    << endl << "########## S' branch: " << name << " ##########" << endl;
    (hopf, f2) := collectEqs data;
    dL := collectDelta data;
    << "#J gens (hopf + fiber2): " << (#hopf + #f2)
      << "  #delta coefficients to kill: " << #dL << endl;
    J := ideal apply(unique (hopf | f2), g -> toQ2 g);
    dQ2 := apply(dL, g -> toQ2 g);
    done := false;
    for d in {2,3,4,5,6,8} do (
        if done then break;
        << "-- gb DegreeLimit " << d << endl;
        elapsedTime G := gb(J, DegreeLimit => d);
        rems := apply(dQ2, b -> b % G);
        nz := select(rems, r -> r != 0);
        << "   nonzero remainders: " << #nz << " / " << #dQ2 << endl;
        << "   is 1 in J so far? " << (1_Q2 % G == 0) << endl;
        if #nz == 0 then (
            << "   ALL delta coefficients lie in J: S'-UNIVERSALITY at eps^3, arbitrary k." << endl;
            done = true));
    if not done then (
        << "-- full gb" << endl;
        elapsedTime G := gb J;
        rems := apply(dQ2, b -> b % G);
        nz := select(rems, r -> r != 0);
        << "   nonzero remainders after full gb: " << #nz << " / " << #dQ2 << endl;
        << "   is 1 in J? " << (1_Q2 % G == 0) << endl;
        if #nz == 0 then << "   ALL delta coefficients lie in J." << endl);
    );

runBranch(data1, "fiber k[x,y]/(x^2,y^2), R = k[eps]/eps^3, delta = phi(phi(e_i)/eps)")
runBranch(data2, "fiber k[t]/(t^4), R = k[eps]/eps^3, delta = phi(phi(e_i)/eps)")

<< endl << "DONE s2gen" << endl;
