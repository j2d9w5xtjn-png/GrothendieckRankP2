-- gensearch.m2
-- Grothendieck's question, order 4, over R = k[eps]/(eps^3), char k = 2.
--
-- General structure-constant search (handoff sections 18-19):
--   A = R.1 + R.e1 + R.e2 + R.e3, free rank 4, augmentation eps(e_i)=0.
--   Multiplication: e_i e_j = sum_r M_(i,j,r) e_r,  M symmetric, no unit term
--     (counit is an algebra map), with M = (fiber constants) + eps*m1 + eps^2*m2.
--   Comultiplication: Delta(e_i) = e_i(x)1 + 1(x)e_i + sum_{j,k>=1} C_(i,j,k) e_j(x)e_k,
--     C = c0 + eps*c1 + eps^2*c2.  (Counit axioms built in; fully general.)
--
-- Equations imposed (J):
--   * associativity of multiplication (commutativity is built into M symmetric)
--   * Delta is an algebra map: Delta(e_i e_j) = Delta(e_i)Delta(e_j)
--   * coassociativity
--   * special fiber killed by 2:  eps^0-digit of phi(e_i) = 0, phi = mu o Delta
--
-- Target: are all coefficients (eps-digits of all coordinates) of
--   P4_i = phi(phi(e_i)) in J (or in its radical)?
-- If yes: no counterexample in this branch, even without imposing antipode
-- or noncocommutativity (a stronger statement).

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

-- fib : set of keys (i,j,r) (i<=j) where the fiber structure constant is 1
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
    -- associativity
    assocV := flatten flatten for i from 1 to 3 list for j from 1 to 3 list
        for k from 1 to 3 list (
        u := mulA(mulA(ebas i, ebas j), ebas k);
        w := mulA(ebas i, mulA(ebas j, ebas k));
        apply(4, t -> u#t + w#t));
    -- Delta as linear map on a 4-vector
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
    -- Delta multiplicative
    compatV := flatten for i from 1 to 3 list for j from i to 3 list (
        lhs := DofVec(Stab#(i,j));
        rhs := mulT2(DEl#i, DEl#j);
        apply(16, t -> lhs#t + rhs#t));
    -- coassociativity
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
            for t from 0 to 3 do if ph#t != 0 then
                out#t = out#t + p#r * ph#t);
        apply(toList out, red));
    -- special fiber killed by 2
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

-- evaluate a polynomial at a point: pt is a hashtable var => kk-value (default 0)
evalAt = (f, pt) -> (
    L := for v in gens Q list (v => (if pt#?v then pt#v else 0_kk));
    sub(f, L)
    );

fib1 = set { (1,2,3) };                      -- fiber k[x,y]/(x^2,y^2): e1=x, e2=y, e3=xy
fib2t = set { (1,1,2), (1,2,3) };            -- fiber k[t]/(t^4):       e1=t, e2=t^2, e3=t^3

------------------------------------------------------------------
-- VALIDATION
------------------------------------------------------------------
<< "=== building data (fiber xy) ===" << endl;
elapsedTime data1 = buildData fib1;
<< "=== building data (fiber t^4) ===" << endl;
elapsedTime data2 = buildData fib2t;

-- Validation A: handoff 16.1, alpha_2 x| mu_2 over k (m-deformation = 0).
-- e1 = x, e2 = t, e3 = xt.
-- Delta(t) = t(x)1+1(x)t+t(x)t; Delta(x) = x(x)1+1(x)x+t(x)x;
-- Delta(xt) = xt(x)1+1(x)xt+x(x)t+t(x)x+xt(x)t.
pt161 = hashTable { c_(2,2,2,0) => 1_kk, c_(1,2,1,0) => 1_kk,
    c_(3,1,2,0) => 1_kk, c_(3,2,1,0) => 1_kk, c_(3,3,2,0) => 1_kk };
(hopf1, f2eq1) = collectEqs data1;
bad161 = select(hopf1, f -> evalAt(f, pt161) != 0);
<< "16.1 hopf equations violated: " << #bad161 << " (expect 0)" << endl;
<< "16.1 fiber-killed-by-2 violated: "
  << #select(f2eq1, f -> evalAt(f, pt161) != 0) << " (expect >0: not killed by 2)" << endl;
<< "16.1 P4 nonzero coeffs: "
  << #select(collectB data1, f -> evalAt(f, pt161) != 0) << " (expect 0: killed by 4)" << endl;

-- Validation B: handoff 16.2, noncocommutative deformation, a = eps^2.
-- e1=x, e2=y, e3=xy; Delta(x) += eps^2 y(x)x ; Delta(y) primitive;
-- Delta(xy) = xy(x)1+1(x)xy+x(x)y+y(x)x+eps^2 y(x)xy.
pt162 = hashTable { c_(1,2,1,2) => 1_kk,
    c_(3,1,2,0) => 1_kk, c_(3,2,1,0) => 1_kk, c_(3,2,3,2) => 1_kk };
bad162 = select(hopf1, f -> evalAt(f, pt162) != 0);
<< "16.2 hopf equations violated: " << #bad162 << " (expect 0)" << endl;
<< "16.2 fiber-killed-by-2 violated: "
  << #select(f2eq1, f -> evalAt(f, pt162) != 0) << " (expect 0)" << endl;
<< "16.2 P4 nonzero coeffs: "
  << #select(collectB data1, f -> evalAt(f, pt162) != 0) << " (expect 0)" << endl;
-- and phi(x) = eps^2 * xy at this point:
phix162 = apply((data1#"phiL")#1, f -> evalAt(f, pt162) ); -- digits lost; check symbolically:
<< "16.2 phi(x) coords (should be {0,0,0, eps^2-coeff nonzero}): "
  << apply((data1#"phiL")#1, f -> (d := digitsQ f; apply(d, g -> evalAt(g, pt162)))) << endl;

-- Validation C: fixed-algebra identity [4]^# == 0 when multiplication is undeformed.
-- Note: with m = 0 the P4 coefficients are NOT identically zero as free
-- polynomials in the c's; the hand argument that fixed-algebra branches are
-- empty uses Delta(e3) = Delta(e1)Delta(e2), i.e. the compat equations.
-- That vanishing-mod-J is exactly what the main run below certifies.

------------------------------------------------------------------
-- MAIN SEARCH
------------------------------------------------------------------
Q2 = kk[ cIx | mIx ];
toQ2 = map(Q2, Q, {0_Q2} | (gens Q2));

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
    for d in {2,3,4,5,6,8} do (
        if done then break;
        << "-- gb DegreeLimit " << d << endl;
        elapsedTime G := gb(J, DegreeLimit => d);
        rems := apply(bQ2, b -> b % G);
        nz := select(rems, r -> r != 0);
        << "   nonzero remainders: " << #nz << " / " << #bQ2 << endl;
        << "   is 1 in J so far? " << (1_Q2 % G == 0) << endl;
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
        if #nz == 0 then << "   ALL P4 coefficients lie in J." << endl
        else (
            << "   testing radical membership via Frobenius powers..." << endl;
            for b in bQ2 do (
                if b % G != 0 then (
                    pow := b; k := 0; okp := false;
                    while k < 5 do (pow = pow^2; k = k+1;
                        if pow % G == 0 then (okp = true; break));
                    << "   b = " << b << "  : b^(2^k) in J for k = "
                      << (if okp then toString k else "NO (up to 32nd power)") << endl))));
    );

runBranch(data1, "fiber k[x,y]/(x^2,y^2), R = k[eps]/eps^3")
runBranch(data2, "fiber k[t]/(t^4), R = k[eps]/eps^3")

<< endl << "DONE" << endl;
