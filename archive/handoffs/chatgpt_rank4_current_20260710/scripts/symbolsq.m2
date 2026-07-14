-- symbolsq.m2 (session 4): the UNCONDITIONAL first-order identity psi^2 = 0,
-- over R = k[e]/e^2, k an ARBITRARY F_2-algebra -- no liftability hypothesis.
--
-- WHY THIS RUN DECIDES A THEOREM (audit of order4_theory_push_handoff.md §2):
-- GPT-5.5 Pro's polarization argument shows: if psi^2 = 0 holds for EVERY
-- first-order deformation of either killed-by-2 fiber over every coefficient
-- F_2-algebra, then together with THEORY_order4.md Thm 6.2 (whose proof uses
-- only fiber2 + m^3 = 0 + freeness -- checked this session) one gets
--     [4]^# = eta o epsilon over EVERY equal-char Artin local base with
--     m^3 = 0, ALL embedding dimensions, arbitrary residue/coefficient field.
-- The previously banked Theorem A gives psi^2 = 0 only for deformations that
-- LIFT to eps^3 (THEORY Prop 7.3(ii)) -- not enough for the polarization
-- quotients. The SAT probe s2check.py proved the unconditional statement for
-- k = F_2 (eps^2 rows, 4/4 UNSAT). THIS run is the arbitrary-k upgrade:
-- all e-digit coefficients of psi(psi(e_i)) in J.
--
-- J = FIRST-ORDER equations of: associativity + Delta-multiplicativity +
-- fiber killed by 2 (the ablation-minimal set M+A, plus F which defines psi).
-- Coassociativity is NOT imposed (pass 1); if membership fails, pass 2 adds it.
--
-- psi here: phi(e_i) = e * v_i with v_i = (e-digit of phi(e_i)), well defined
-- mod J since the e^0-digit of phi(e_i) is a fiber2 generator; psi^2(e_i) =
-- e-digit of phi(v_i) = sum_r v_{i,r} phi(e_r).  (= s2gen.m2's delta at N=2.)
--
-- Gates: (a) 16.2 with a = e (first-order noncocommutative point): all J
-- equations vanish, all delta digits vanish (hand: psi(x)=xy, psi(xy)=0);
-- (b) trivial point: everything vanishes.  Generator code copied from
-- gensearch.m2/minassoc.m2/s2gen.m2 (gate-validated), digits cut to 2.

kk = ZZ/2

cIx = flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
          for k from 1 to 3 list for d from 0 to 1 list c_(i,j,k,d);
mIx = flatten flatten for i from 1 to 3 list for j from i to 3 list
          for r from 1 to 3 list m_(i,j,r,1);

Q = kk[ {eps} | cIx | mIx ];
epsI = ideal(eps^2);
red = f -> f % epsI;

digitsQ = f -> (
    f = red f;
    f0 := sub(f, {eps => 0});
    g  := (f - f0)//eps;
    g0 := sub(g, {eps => 0});
    {f0, g0}
    );

ebas = i -> apply(4, k -> if k == i then 1_Q else 0_Q);
idx2 = (a,b) -> 4*a + b;

Cc = (i,j,k) -> c_(i,j,k,0) + eps*c_(i,j,k,1);

buildData = fib -> (
    Mc := (i,j,r) -> (
        ii := min(i,j); jj := max(i,j);
        (if member((ii,jj,r), fib) then 1_Q else 0_Q) + eps*m_(ii,jj,r,1));
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
                        out#(16*a+4*b+s) = out#(16*a+4*b+s) + u*Dr#(idx2(a,b));
                Ds := DEl#s;
                for b from 0 to 3 do for cc from 0 to 3 do
                    if Ds#(idx2(b,cc)) != 0 then
                        out#(16*r+4*b+cc) = out#(16*r+4*b+cc) + u*Ds#(idx2(b,cc))));
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
    -- v_i = e-digit of phi(e_i);  delta_i = phi(v_i) = sum_r v_{i,r} phi(e_r)
    vL := for i from 1 to 3 list (
        for r from 0 to 3 list ( (digitsQ((phiL#i)#r))#1 ));
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

collectMA = data -> (
    vecs := data#"assocV" | data#"compatV";
    unique select(flatten apply(vecs, v -> flatten apply(v, digitsQ)), f -> f != 0));
collectC = data -> unique select(
    flatten apply(data#"coassocV", v -> flatten apply(v, digitsQ)), f -> f != 0);
collectF = data -> unique select(data#"fiber2E", f -> f != 0);
collectDelta = data -> unique select(
    flatten apply(data#"deltaL", v -> flatten apply(v, digitsQ)), f -> f != 0);

evalAt = (f, pt) -> (
    L := for v in gens Q list (v => (if pt#?v then pt#v else 0_kk));
    sub(f, L)
    );

fib1 = set { (1,2,3) };
fib2t = set { (1,1,2), (1,2,3) };

------------------------------------------------------------------
-- VALIDATION: 16.2 with a = e (first-order), and the trivial point
------------------------------------------------------------------
<< "=== building data (fiber xy) ===" << endl;
elapsedTime data1 = buildData fib1;
<< "=== building data (fiber t^4) ===" << endl;
elapsedTime data2 = buildData fib2t;

-- Delta(x) += e y(x)x ; Delta(xy) = xy(x)1+1(x)xy+x(x)y+y(x)x+e y(x)xy; m = 0.
pt162e = hashTable { c_(1,2,1,1) => 1_kk,
    c_(3,1,2,0) => 1_kk, c_(3,2,1,0) => 1_kk, c_(3,2,3,1) => 1_kk };
gateOK = true;
n1 = #select(collectMA data1 | collectF data1 | collectC data1,
             f -> evalAt(f, pt162e) != 0);
<< "16.2(a=e) equations violated (M+A+F+C): " << n1 << " (expect 0)" << endl;
if n1 != 0 then gateOK = false;
n2 = #select(collectDelta data1, f -> evalAt(f, pt162e) != 0);
<< "16.2(a=e) delta digits nonzero: " << n2
  << " (expect 0: psi(x) = xy, psi(xy) = 0)" << endl;
if n2 != 0 then gateOK = false;
pt0 = hashTable {};
n3 = #select(collectDelta data1, f -> evalAt(f, pt0) != 0);
<< "trivial point delta digits nonzero: " << n3 << " (expect 0)" << endl;
if n3 != 0 then gateOK = false;
if not gateOK then (<< "GATE FAILED -- STOP" << endl; exit 1);
<< "ALL GATES PASSED" << endl;

------------------------------------------------------------------
-- MAIN: delta digits in J?  pass 1: J = M+A+F; pass 2 (if needed): + coassoc
------------------------------------------------------------------
Q2 = kk[ cIx | mIx ];
toQ2 = map(Q2, Q, {0_Q2} | (gens Q2));

tryJ = (gensList, dL, label) -> (
    << endl << "-- " << label << ": #J gens " << #gensList
      << ", #delta coeffs " << #dL << endl;
    J := ideal apply(unique gensList, g -> toQ2 g);
    dQ2 := apply(dL, g -> toQ2 g);
    left := #dQ2;
    for d in {2,3,4,5,6,8} do (
        if left == 0 then break;
        << "-- gb DegreeLimit " << d << endl;
        elapsedTime G := gb(J, DegreeLimit => d);
        rems := apply(dQ2, b -> b % G);
        left = #select(rems, r -> r != 0);
        << "   nonzero remainders: " << left << " / " << #dQ2
          << "   (1 in J? " << (1_Q2 % G == 0) << ")" << endl);
    if left > 0 then (
        << "-- full gb" << endl;
        elapsedTime G := gb J;
        rems := apply(dQ2, b -> b % G);
        left = #select(rems, r -> r != 0);
        << "   nonzero remainders after full gb: " << left << " / " << #dQ2 << endl);
    left
    );

runBranch = (data, name) -> (
    << endl << "########## psi^2 branch: " << name << " ##########" << endl;
    dL := collectDelta data;
    r1 := tryJ(collectMA data | collectF data, dL, "pass 1: J = assoc+compat+fiber2");
    if r1 == 0 then
        << "   PSI^2 = 0 UNCONDITIONALLY (minimal axioms M+A+F), arbitrary k." << endl
    else (
        r2 := tryJ(collectMA data | collectF data | collectC data, dL,
                   "pass 2: J = assoc+compat+fiber2+coassoc");
        if r2 == 0 then
            << "   PSI^2 = 0 UNCONDITIONALLY (with coassoc), arbitrary k." << endl
        else
            << "   NOT closed: " << r2 << " coefficients remain outside J." << endl);
    );

runBranch(data1, "fiber k[x,y]/(x^2,y^2), R = k[e]/e^2, unconditional first order")
runBranch(data2, "fiber k[t]/(t^4), R = k[e]/e^2, unconditional first order")

<< endl << "DONE symbolsq" << endl;
