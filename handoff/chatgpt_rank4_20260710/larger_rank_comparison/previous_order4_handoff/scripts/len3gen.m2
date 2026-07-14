-- len3gen.m2  (session 3)
-- Grothendieck's question, order 4, over the UNIVERSAL embedding-dimension-2
-- length-3-truncated equal-characteristic base:
--
--     R = k[s,t]/(s,t)^3,   k an arbitrary commutative F_2-algebra.
--
-- Every equal-characteristic Artin local F_2-algebra with m^3 = 0 and
-- dim m/m^2 <= 2 is a quotient of this R (after choosing generators of m),
-- and ideal-membership certificates specialize along quotients and along
-- arbitrary base change in k.  So a full success here proves:
--
--   THEOREM (target): for every F_2-algebra k and every Artin local
--   k-algebra R with m^3 = 0, dim m/m^2 <= 2, every free rank-4 bialgebra
--   over R whose fiber has one of the two local shapes and is killed by 2
--   satisfies [4]^# = eta o eps.
--
-- This subsumes Theorem A (k[eps]/eps^3 = R/(t, s*t? no: R/(t)) ) and proves
-- the *polarized* psi-identity  psi_a psi_b + psi_b psi_a = 0 (a != b) plus
-- psi_a^2 = 0 for pairs of deformation directions (see THEORY_order4.md, S5).
--
-- Structure of the computation = gensearch.m2 (validated) with the eps-digit
-- arithmetic {1, eps, eps^2} replaced by the 6-digit basis
--     d = 0: 1,  d = 1: s,  d = 2: t,  d = 3: s^2,  d = 4: s*t,  d = 5: t^2.
--
-- VALIDATION GATES (golden rule 1): 16.1 (alpha_2 x| mu_2), 16.2 with
-- a = s^2 (digit 3), and a NEW mixed-direction gate 16.2' with a = s*t
-- (digit 4).  All three must pass before the main search results count.

kk = ZZ/2

cIx = flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
          for k from 1 to 3 list for d from 0 to 5 list c_(i,j,k,d);
mIx = flatten flatten flatten for i from 1 to 3 list for j from i to 3 list
          for r from 1 to 3 list for d from 1 to 5 list m_(i,j,r,d);

Q = kk[ {s,t} | cIx | mIx ];
rels = ideal(s^3, s^2*t, s*t^2, t^3);
red = f -> f % rels;

mono = {1_Q, s, t, s^2, s*t, t^2};

-- digitsQ: coefficients of f in the basis {1, s, t, s^2, s*t, t^2}
digitsQ = f -> (
    f = red f;
    a0 := sub(f, {s => 0, t => 0});
    f1 := f - a0;
    u  := sub(f1, {t => 0});          -- a1*s + a3*s^2
    q1 := u // s;                      -- a1 + a3*s
    a1 := sub(q1, {s => 0});
    a3 := sub(q1 // s, {s => 0, t => 0});
    v  := sub(f1, {s => 0});          -- a2*t + a5*t^2
    q2 := v // t;
    a2 := sub(q2, {t => 0});
    a5 := sub(q2 // t, {s => 0, t => 0});
    w  := f1 - u - v;                  -- a4*s*t
    a4 := sub(w // (s*t), {s => 0, t => 0});
    {a0, a1, a2, a3, a4, a5}
    );

ebas = i -> apply(4, k -> if k == i then 1_Q else 0_Q);
idx2 = (a,b) -> 4*a + b;
idx3 = (a,b,cc) -> 16*a + 4*b + cc;

Cc = (i,j,k) -> sum(0..5, d -> mono#d * c_(i,j,k,d));

-- fib : set of keys (i,j,r) (i<=j) where the fiber structure constant is 1
buildData = fib -> (
    Mc := (i,j,r) -> (
        ii := min(i,j); jj := max(i,j);
        (if member((ii,jj,r), fib) then 1_Q else 0_Q)
          + sum(1..5, d -> mono#d * m_(ii,jj,r,d)));
    Stab := hashTable flatten for a from 0 to 3 list for b from 0 to 3 list
        (a,b) => (if a == 0 then ebas b else if b == 0 then ebas a
                  else {0_Q, Mc(a,b,1), Mc(a,b,2), Mc(a,b,3)});
    DEl := for i from 0 to 3 list (
        if i == 0 then apply(16, tt -> if tt == 0 then 1_Q else 0_Q)
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
    -- associativity
    assocV := flatten flatten for i from 1 to 3 list for j from 1 to 3 list
        for k from 1 to 3 list (
        u := mulA(mulA(ebas i, ebas j), ebas k);
        w := mulA(ebas i, mulA(ebas j, ebas k));
        apply(4, tt -> u#tt + w#tt));
    -- Delta as linear map on a 4-vector
    DofVec := v -> (
        out := new MutableList from toList(16:0_Q);
        for r from 0 to 3 do if v#r != 0 then (
            D := DEl#r;
            for tt from 0 to 15 do if D#tt != 0 then out#tt = out#tt + v#r * D#tt);
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
    -- Delta multiplicative
    compatV := flatten for i from 1 to 3 list for j from i to 3 list (
        lhs := DofVec(Stab#(i,j));
        rhs := mulT2(DEl#i, DEl#j);
        apply(16, tt -> lhs#tt + rhs#tt));
    -- coassociativity
    coassocV := for i from 1 to 3 list (
        out := new MutableList from toList(64:0_Q);
        D := DEl#i;
        for r from 0 to 3 do for ss from 0 to 3 do (
            u := D#(idx2(r,ss));
            if u != 0 then (
                Dr := DEl#r;
                for a from 0 to 3 do for b from 0 to 3 do
                    if Dr#(idx2(a,b)) != 0 then
                        out#(idx3(a,b,ss)) = out#(idx3(a,b,ss)) + u*Dr#(idx2(a,b));
                Ds := DEl#ss;
                for b from 0 to 3 do for cc from 0 to 3 do
                    if Ds#(idx2(b,cc)) != 0 then
                        out#(idx3(r,b,cc)) = out#(idx3(r,b,cc)) + u*Ds#(idx2(b,cc))));
        apply(toList out, red));
    -- phi = mu o Delta  (the squaring map [2]^#)
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
    -- sanity: phi preserves the augmentation ideal
    for i from 1 to 3 do assert((phiL#i)#0 == 0);
    -- P4_i = phi(phi(e_i))
    P4L := for i from 1 to 3 list (
        p := phiL#i;
        out := new MutableList from toList(4:0_Q);
        for r from 0 to 3 do if p#r != 0 then (
            ph := phiL#r;
            for tt from 0 to 3 do if ph#tt != 0 then
                out#tt = out#tt + p#r * ph#tt);
        apply(toList out, red));
    -- special fiber killed by 2: digit-0 component of phi(e_i) coords
    fiber2E := flatten for i from 1 to 3 list
        for r from 1 to 3 list (digitsQ((phiL#i)#r))#0;
    hashTable {
        "assocV" => assocV, "compatV" => compatV, "coassocV" => coassocV,
        "phiL" => phiL, "P4L" => P4L, "fiber2E" => fiber2E, "DEl" => DEl }
    );

collectEqs = data -> (
    vecs := data#"assocV" | data#"compatV" | data#"coassocV";
    hopf := unique select(flatten apply(vecs, v -> flatten apply(v, digitsQ)), f -> f != 0);
    fib2 := unique select(data#"fiber2E", f -> f != 0);
    (hopf, fib2)
    );

collectB = data -> unique select(
    flatten apply(data#"P4L", v -> flatten apply(v, digitsQ)), f -> f != 0);

evalAt = (f, pt) -> (
    L := for v in gens Q list (v => (if pt#?v then pt#v else 0_kk));
    sub(f, L)
    );

fib1 = set { (1,2,3) };                      -- fiber k[x,y]/(x^2,y^2): e1=x, e2=y, e3=xy
fib2t = set { (1,1,2), (1,2,3) };            -- fiber k[t]/(t^4):       e1=t, e2=t^2, e3=t^3

------------------------------------------------------------------
-- VALIDATION GATES
------------------------------------------------------------------
<< "=== building data (fiber xy) ===" << endl;
elapsedTime data1 = buildData fib1;
<< "=== building data (fiber t^4) ===" << endl;
elapsedTime data2 = buildData fib2t;

(hopf1, f2eq1) = collectEqs data1;
b1 = collectB data1;

-- Gate 16.1: alpha_2 x| mu_2 over k (no deformation; digit-0 c's only).
pt161 = hashTable { c_(2,2,2,0) => 1_kk, c_(1,2,1,0) => 1_kk,
    c_(3,1,2,0) => 1_kk, c_(3,2,1,0) => 1_kk, c_(3,3,2,0) => 1_kk };
<< "16.1 hopf equations violated: "
  << #select(hopf1, f -> evalAt(f, pt161) != 0) << " (expect 0)" << endl;
<< "16.1 fiber-killed-by-2 violated: "
  << #select(f2eq1, f -> evalAt(f, pt161) != 0) << " (expect >0: not killed by 2)" << endl;
<< "16.1 P4 nonzero coeffs: "
  << #select(b1, f -> evalAt(f, pt161) != 0) << " (expect 0: killed by 4)" << endl;

-- Gate 16.2 (s^2 direction, digit 3): Delta(x) += s^2 y(x)x,
-- Delta(xy) = xy(x)1+1(x)xy+x(x)y+y(x)x+s^2 y(x)xy.
pt162 = hashTable { c_(1,2,1,3) => 1_kk,
    c_(3,1,2,0) => 1_kk, c_(3,2,1,0) => 1_kk, c_(3,2,3,3) => 1_kk };
<< "16.2(s^2) hopf equations violated: "
  << #select(hopf1, f -> evalAt(f, pt162) != 0) << " (expect 0)" << endl;
<< "16.2(s^2) fiber-killed-by-2 violated: "
  << #select(f2eq1, f -> evalAt(f, pt162) != 0) << " (expect 0)" << endl;
<< "16.2(s^2) P4 nonzero coeffs: "
  << #select(b1, f -> evalAt(f, pt162) != 0) << " (expect 0)" << endl;
<< "16.2(s^2) phi(x) coords as digit-vectors (expect xy-coord to be s^2, i.e. digit 3): "
  << apply((data1#"phiL")#1, f -> apply(digitsQ f, g -> evalAt(g, pt162))) << endl;

-- Gate 16.2' (MIXED direction s*t, digit 4): Delta(x) += s*t y(x)x,
-- Delta(xy) = ... + s*t y(x)xy.  New in session 3; checks the cross terms.
pt162m = hashTable { c_(1,2,1,4) => 1_kk,
    c_(3,1,2,0) => 1_kk, c_(3,2,1,0) => 1_kk, c_(3,2,3,4) => 1_kk };
<< "16.2'(st) hopf equations violated: "
  << #select(hopf1, f -> evalAt(f, pt162m) != 0) << " (expect 0)" << endl;
<< "16.2'(st) fiber-killed-by-2 violated: "
  << #select(f2eq1, f -> evalAt(f, pt162m) != 0) << " (expect 0)" << endl;
<< "16.2'(st) P4 nonzero coeffs: "
  << #select(b1, f -> evalAt(f, pt162m) != 0) << " (expect 0)" << endl;

------------------------------------------------------------------
-- MAIN SEARCH
------------------------------------------------------------------
Q2 = kk[ cIx | mIx ];
toQ2 = map(Q2, Q, {0_Q2, 0_Q2} | (gens Q2));

runBranch = (data, name) -> (
    << endl << "########## branch: " << name << " ##########" << endl;
    (hopf, f2) := collectEqs data;
    bL := collectB data;
    << "#hopf eqs: " << #hopf << "  #fiber2 eqs: " << #f2
      << "  #P4 coefficients to kill: " << #bL << endl;
    J := ideal apply(unique(hopf | f2), g -> toQ2 g);
    bQ2 := apply(bL, g -> toQ2 g);
    << "gen degrees: " << tally apply(flatten entries gens J, g -> first degree g) << endl;
    done := false;
    for d in {2,3,4,5,6} do (
        if done then break;
        << "-- gb DegreeLimit " << d << ": " << flush;
        elapsedTime G := gb(J, DegreeLimit => d);
        rems := apply(bQ2, b -> b % G);
        nz := select(rems, r -> r != 0);
        << "   nonzero remainders: " << #nz << " / " << #bQ2 << endl;
        << "   is 1 in J so far? " << (1_Q2 % G == 0) << endl << flush;
        if #nz == 0 then (
            << "   ALL P4 coefficients lie in J (ideal membership certificate)." << endl;
            done = true));
    if not done then (
        << "-- full gb" << endl;
        elapsedTime G := gb J;
        rems := apply(bQ2, b -> b % G);
        nz := select(rems, r -> r != 0);
        << "   nonzero remainders after full gb: " << #nz << " / " << #bQ2 << endl;
        << "   is 1 in J? " << (1_Q2 % G == 0) << endl;
        if #nz == 0 then << "   ALL P4 coefficients lie in J." << endl);
    );

runBranch(data1, "fiber k[x,y]/(x^2,y^2), R = k[s,t]/(s,t)^3 (universal embdim 2)")
runBranch(data2, "fiber k[t]/(t^4), R = k[s,t]/(s,t)^3 (universal embdim 2)")

<< endl << "DONE len3gen" << endl;
