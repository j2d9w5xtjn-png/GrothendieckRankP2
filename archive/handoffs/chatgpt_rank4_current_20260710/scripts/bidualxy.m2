-- bidualgen.m2  (session 14, 2026-07-09)
-- Arbitrary-k' certificates for the BIDUAL S' problem: R = k'[u,v]/(u^2,v^2),
-- phi = [2]^# = u P + v Q + uv T, both fibers, PER SPLIT MODEL (the four xy
-- models of THEORY 12.4.1 + the t^4 (c1,c4) normal form of THEORY 12.3).
--
-- CONTEXT.  THEORY 15.5: S'(A/R) <=> solvability, at each COTANGENT generator
-- g only (15.5.1: products are free), of the two boxed equations
--     (B1)  T P g + Q r + P a           = 0
--     (B2)  T Q g + Q (T g + a) + P s   = 0        (a, r, s in I_H free)
-- given the pairwise-nilpotence identities P^2 = Q^2 = PQ = QP = 0 on the
-- relevant vectors (THEORY 15.3, hand-banked; re-certified here).
-- The SEVENTH external note (order4_seventh_push_bidual_xy_rank1.md) closed
-- the two rank-one xy split branches by explicit divisions and reduced the
-- image-line branches to lemma (I2); its inputs (R1), (rho), (I0) and the
-- divisions are certified here at arbitrary-k' strength.
--
-- NEW (session 14, derived in-session): the POLARIZED LAYER-2
-- MULTIPLICATIVITY identity.  For x, y in I_H (constant vectors), matching
-- the uv-digit of phi(x *_A y) = phi(x) phi(y) over u^2 = v^2 = 0 gives
--     T(mu_0(x,y)) = P(mu_Q(x,y)) + Q(mu_P(x,y)) + mu_0(Px,Qy) + mu_0(Qx,Py),
-- and matching the u-digit gives P(mu_0(x,y)) = 0 (P, Q KILL fiber products).
-- Consequences, worked out in THEORY 16 (session 14):
--   * t^4: P(t^2) = P(t^3) = 0 and I^2 * I^2 = 0 make
--         T(t^2) = mu_Q(t,t)_t  Pt + mu_P(t,t)_t  Qt,
--         T(t^3) = mu_Q(t,t^2)_t Pt + mu_P(t,t^2)_t Qt,
--     so with Pt = B_P t^2 + C_P t^3, Qt = B_Q t^2 + C_Q t^3:
--         (B1) is solved by a = A_s t, r = R_s t   with
--             A_s = B_P mu_Q(t,t)_t + C_P mu_Q(t,t^2)_t,
--             R_s = B_P mu_P(t,t)_t + C_P mu_P(t,t^2)_t,
--     and (B2) by s = alpha_s t (alpha_s the P-side scalar of TQt) PROVIDED
--     the single scalar identity  [target "Tscalar"]
--         (Tt)_t = B_P mu_Q(t,t)_t + C_P mu_Q(t,t^2)_t
--                + B_Q mu_P(t,t)_t + C_Q mu_P(t,t^2)_t
--     holds -- the POLARIZATION of Theorem K step (6), (Psi2 t)_t = pB + qC.
--     Tscalar in J  ==>  bidual S' for the t^4 fiber, arbitrary k',
--     INDEPENDENT of the (missing) sixth external note.
--   * image-line xy: T(z) in k'z ("I0") follows formally (P,Q image-line +
--     z^2 = 0); certified anyway.
--
-- DIRECT ROUTE (belt-and-braces + fallback): (B1)+(B2) at g is the linear
-- system  M w = b_g,  M = [[P, Q, 0], [Q, 0, P]] (6x9 over the structure-
-- constant ring), b_g = (TPg ; TQg + QTg).  Solvability at EVERY k'-point of
-- V(J) with polynomial witnesses <=> b_g in image(M) + J*A^6, a MODULE
-- membership, GB-checkable with DegreeLimit (partial reduction to 0 = full
-- certificate, golden rule 2).
--
-- SOUNDNESS of pinning + descent: as in s4xygen/s4t4gen (THEORY 12.4.3,
-- 14.8): S' is a submodule-membership condition, stable under faithfully
-- flat base change (kernels commute with flat base change), and the fiber
-- shape/normal-form theorems are ff-covers; the digit-0 gate below catches
-- any wrong pin table (J would contain 1 and everything would be vacuous --
-- we also print "1 in J?").
--
-- Digit convention: d = 1 <-> u (P), d = 2 <-> v (Q), d = 3 <-> uv (T).

kk = ZZ/2

pinsA2A2   = set { (3,1,2), (3,2,1) };
pinsW2F    = set { (2,1,1), (3,1,2), (3,2,1) };
pinsMu2Mu2 = set { (1,1,1), (2,2,2), (3,1,2), (3,2,1), (3,1,3), (3,3,1),
                   (3,2,3), (3,3,2), (3,3,3) };
pinsMu2A2  = set { (1,1,1), (3,1,2), (3,2,1), (3,1,3), (3,3,1) };
fibXY = set { (1,2,3) };
fibT4 = set { (1,1,2), (1,2,3) };

runModel = (pins, name, caseType) -> (
    << endl << "############################################################" << endl;
    << "## bidualgen: model " << name << "  over k'[u,v]/(u^2,v^2)   (case " << caseType << ")" << endl;
    << "############################################################" << endl;
    cIx := flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
              for k from 1 to 3 list for d from 1 to 3 list c_(i,j,k,d);
    mIx := flatten flatten flatten for i from 1 to 3 list for j from i to 3 list
              for r from 1 to 3 list for d from 1 to 3 list m_(i,j,r,d);
    extra := if caseType === "t4" then {C1, C4} else {};
    Q := kk[ {uu, vv} | extra | cIx | mIx ];
    use Q;
    uuq := uu_Q; vvq := vv_Q;
    nilI := ideal(uuq^2, vvq^2);
    red := f -> f % nilI;
    -- digits {f_1, f_u, f_v, f_uv}
    digitsQ := f -> (
        f = red f;
        f00 := sub(f, {uuq => 0, vvq => 0});
        g := f - f00;
        gu := sub(g, {vvq => 0});
        gv := sub(g, {uuq => 0});
        gw := g - gu - gv;
        {f00, gu // uuq, gv // vvq, gw // (uuq*vvq)});
    ebas := i -> apply(4, k -> if k == i then 1_Q else 0_Q);
    idx2 := (a,b) -> 4*a + b;
    idx3 := (a,b,cc) -> 16*a + 4*b + cc;
    pin0 := if caseType === "t4" then (
        (i,j,k) -> (
            if i == 1 then (
                if (j,k) == (1,2) or (j,k) == (2,1) then C1_Q
                else if (j,k) == (2,3) or (j,k) == (3,2) then (C1_Q)^2
                else if (j,k) == (2,2) then C4_Q
                else 0_Q)
            else if i == 2 then 0_Q
            else (
                if (j,k) == (1,2) or (j,k) == (2,1) then 1_Q
                else if (j,k) == (2,3) or (j,k) == (3,2) then C1_Q
                else 0_Q))
    ) else (
        (i,j,k) -> if member((i,j,k), pins) then 1_Q else 0_Q
    );
    fib := if caseType === "t4" then fibT4 else fibXY;
    layer := d -> if d == 1 then uuq else if d == 2 then vvq else uuq*vvq;
    Cc := (i,j,k) -> pin0(i,j,k) + sum for d from 1 to 3 list (layer d) * c_(i,j,k,d);
    Mc := (i,j,r) -> (
        ii := min(i,j); jj := max(i,j);
        (if member((ii,jj,r), fib) then 1_Q else 0_Q)
          + sum for d from 1 to 3 list (layer d) * m_(ii,jj,r,d));
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
    -- ===== GATES =====
    vecs := assocV | compatV | coassocV;
    dig0 := flatten apply(vecs, v -> apply(v, f -> (digitsQ f)#0));
    bad0 := select(dig0, f -> f != 0);
    << "GATE digit-0 axioms of pinned model identically 0: "
      << (if #bad0 == 0 then "OK" else "FAILED") << endl;
    badF := select(fiber2E, f -> f != 0);
    << "GATE phi_0 = 0 (model killed by 2): "
      << (if #badF == 0 then "OK" else "FAILED (" | toString(#badF) | " nonzero)") << endl;
    if #bad0 != 0 or #badF != 0 then (
        << "!! GATE FAILURE for model " << name << " -- SKIPPING GB (pins wrong?)" << endl;
    ) else (
    PsiD := hashTable flatten for i from 1 to 3 list for r from 1 to 3 list
        (i,r) => digitsQ((phiL#i)#r);
    Psi := (n,i,r) -> (PsiD#(i,r))#n;
    -- apply layer-n operator to a length-3 vector of ring elements
    opV := (n,w) -> for r from 1 to 3 list sum for j from 1 to 3 list (w#(j-1))*Psi(n,j,r);
    psiVec := (n,i) -> for r from 1 to 3 list Psi(n,i,r);
    addV := (w1,w2) -> for j from 0 to 2 list (w1#j + w2#j);
    targets := {};
    -- (a) pairwise nilpotence rows, ALL basis vectors
    for i from 1 to 3 do (
        for pr in {("P2", opV(1, psiVec(1,i))), ("QP", opV(2, psiVec(1,i))),
                   ("PQ", opV(1, psiVec(2,i))), ("Q2", opV(2, psiVec(2,i)))} do
            for r from 1 to 3 do
                targets = targets | {(pr#0 | "[" | toString i | "," | toString r | "]",
                                      (pr#1)#(r-1))});
    -- (b) model-specific structured targets
    if caseType === "t4" then (
        -- P, Q kill products (t^2, t^3)
        for d in {1,2} do for i in {2,3} do for r from 1 to 3 do
            targets = targets | {("kill" | toString d | "[" | toString i | ","
                                  | toString r | "]", Psi(d,i,r))};
        -- P(t), Q(t) in I^2
        targets = targets | {("PtI2", Psi(1,1,1)), ("QtI2", Psi(2,1,1))};
        -- THE scalar (polarized Theorem K step 6)
        targets = targets | {("Tscalar",
            Psi(3,1,1) + Psi(1,1,2)*m_(1,1,1,2) + Psi(1,1,3)*m_(1,2,1,2)
                       + Psi(2,1,2)*m_(1,1,1,1) + Psi(2,1,3)*m_(1,2,1,1))};
    ) else if caseType === "imageline" then (
        for d in {1,2} do (
            for g in {1,2} do for r in {1,2} do
                targets = targets | {("shape" | toString d | "[" | toString g | ","
                                      | toString r | "]", Psi(d,g,r))};
            for r from 1 to 3 do
                targets = targets | {("shape" | toString d | "[3," | toString r | "]",
                                      Psi(d,3,r))});
        targets = targets | {("I0[1]", Psi(3,3,1)), ("I0[2]", Psi(3,3,2))};
    ) else if caseType === "rank1W" then (
        for d in {1,2} do (
            for r from 1 to 3 do targets = targets |
                {("shape" | toString d | "[1," | toString r | "]", Psi(d,1,r)),
                 ("shape" | toString d | "[3," | toString r | "]", Psi(d,3,r))};
            targets = targets | {("shape" | toString d | "[2,2]", Psi(d,2,2)),
                                 ("shape" | toString d | "[2,3]", Psi(d,2,3))});
        lamP := m_(1,1,1,1); lamQ := m_(1,1,1,2);
        alpP := c_(1,1,1,1); alpQ := c_(1,1,1,2);
        delP := c_(1,2,2,1); delQ := c_(1,2,2,2);
        nuP  := m_(2,2,1,1); nuQ  := m_(2,2,1,2);
        alpha := Psi(3,1,1);
        targets = targets |
          {("R1[1,2]", Psi(3,1,2)), ("R1[1,3]", Psi(3,1,3)),
           ("rho", Psi(3,2,2) + lamP*alpQ + lamQ*alpP),
           ("pol22a", lamP*delQ + lamQ*delP),
           ("pol22b", nuP*delQ + nuQ*delP)};
        avec := {0_Q, alpha + lamQ*alpP, 0_Q};
        rvec := {0_Q, lamP*alpP, 0_Q};
        svec := {0_Q, lamQ*alpQ, 0_Q};
        B1r := addV(addV(opV(3, psiVec(1,2)), opV(2, rvec)), opV(1, avec));
        B2r := addV(addV(opV(3, psiVec(2,2)), opV(2, addV(psiVec(3,2), avec))),
                    opV(1, svec));
        for r from 1 to 3 do targets = targets |
            {("B1res[" | toString r | "]", B1r#(r-1)),
             ("B2res[" | toString r | "]", B2r#(r-1))};
    ) else ( -- rank1E = mu2a2 (x <-> y mirror)
        for d in {1,2} do (
            for r from 1 to 3 do targets = targets |
                {("shape" | toString d | "[2," | toString r | "]", Psi(d,2,r)),
                 ("shape" | toString d | "[3," | toString r | "]", Psi(d,3,r))};
            targets = targets | {("shape" | toString d | "[1,1]", Psi(d,1,1)),
                                 ("shape" | toString d | "[1,3]", Psi(d,1,3))});
        lamP2 := m_(1,1,2,1); lamQ2 := m_(1,1,2,2);
        alpP2 := c_(2,1,1,1); alpQ2 := c_(2,1,1,2);
        delP2 := c_(2,2,2,1); delQ2 := c_(2,2,2,2);
        nuP2  := m_(2,2,2,1); nuQ2  := m_(2,2,2,2);
        alpha2 := Psi(3,2,2);
        targets = targets |
          {("R1[2,1]", Psi(3,2,1)), ("R1[2,3]", Psi(3,2,3)),
           ("rho", Psi(3,1,1) + lamP2*alpQ2 + lamQ2*alpP2),
           ("pol22a", lamP2*delQ2 + lamQ2*delP2),
           ("pol22b", nuP2*delQ2 + nuQ2*delP2)};
        avec2 := {alpha2 + lamQ2*alpP2, 0_Q, 0_Q};
        rvec2 := {lamP2*alpP2, 0_Q, 0_Q};
        svec2 := {lamQ2*alpQ2, 0_Q, 0_Q};
        B1r2 := addV(addV(opV(3, psiVec(1,1)), opV(2, rvec2)), opV(1, avec2));
        B2r2 := addV(addV(opV(3, psiVec(2,1)), opV(2, addV(psiVec(3,1), avec2))),
                     opV(1, svec2));
        for r from 1 to 3 do targets = targets |
            {("B1res[" | toString r | "]", B1r2#(r-1)),
             ("B2res[" | toString r | "]", B2r2#(r-1))};
    );
    -- ===== move to the u,v-free ring =====
    hopf := unique select(flatten apply(vecs, v -> flatten apply(v, digitsQ)), f -> f != 0);
    f2  := unique select(fiber2E, f -> f != 0);
    Q2 := kk[ extra | cIx | mIx ];
    toQ2 := map(Q2, Q, {0_Q2, 0_Q2} | (gens Q2));
    J := ideal apply(unique(hopf | f2), g -> toQ2 g);
    tQ2 := apply(targets, t -> (t#0, toQ2 (t#1)));
    cotgens := if caseType === "t4" then {1} else {1,2};
    -- module system M w = b_g
    Mmat := matrix (
        (for r from 1 to 3 list (
            (for j from 1 to 3 list toQ2 Psi(1,j,r)) |
            (for j from 1 to 3 list toQ2 Psi(2,j,r)) |
            toList(3:0_Q2))) |
        (for r from 1 to 3 list (
            (for j from 1 to 3 list toQ2 Psi(2,j,r)) |
            toList(3:0_Q2) |
            (for j from 1 to 3 list toQ2 Psi(1,j,r)))));
    bvecs := apply(cotgens, g -> (
        b1 := opV(3, psiVec(1,g));
        b2 := addV(opV(3, psiVec(2,g)), opV(2, psiVec(3,g)));
        (g, transpose matrix { apply(b1 | b2, f -> toQ2 f) })));
    Nmod := image Mmat + J*(Q2^6);
    -- I2 side ideals (image-line only)
    useI2 := caseType === "imageline";
    pxv := toQ2 Psi(1,1,3); pyv := toQ2 Psi(1,2,3);
    qxv := toQ2 Psi(2,1,3); qyv := toQ2 Psi(2,2,3);
    J2q := if useI2 then J + ideal(pxv, pyv, qxv^2, qxv*qyv, qyv^2) else J;
    J2p := if useI2 then J + ideal(qxv, qyv, pxv^2, pxv*pyv, pyv^2) else J;
    i2targets := if useI2 then
        flatten for g in {1,2} list (
            {("I2q[" | toString g | "]",
              qxv*(toQ2 Psi(3,g,1)) + qyv*(toQ2 Psi(3,g,2)), "q"),
             ("I2p[" | toString g | "]",
              pxv*(toQ2 Psi(3,g,1)) + pyv*(toQ2 Psi(3,g,2)), "p")})
        else {};
    << "#vars: " << numgens Q2 << "  #eqs: " << numgens J
      << "  #ideal targets: " << #tQ2
      << "  #module targets: " << #bvecs
      << "  #I2 targets: " << #i2targets << endl;
    done := false;
    for d in {2,3,4,5,6,8} do (
        if done then break;
        << "-- gb DegreeLimit " << d << ": " << flush;
        elapsedTime G := gb(J, DegreeLimit => d);
        nz := select(tQ2, t -> (t#1) % G != 0);
        << "   ideal targets open: " << #nz << " / " << #tQ2
          << "   (1 in J? " << (1_Q2 % G == 0) << ")" << endl;
        if #nz > 0 and #nz <= 25 then
            << "   still open: " << concatenate between(", ", apply(nz, t -> t#0)) << endl;
        << "   module gb: " << flush;
        elapsedTime Gn := gb(Nmod, DegreeLimit => d);
        nzm := select(bvecs, b -> (b#1) % Gn != 0);
        << "   Bsys open at g in {" << concatenate between(", ",
              apply(nzm, b -> toString(b#0))) << "}"
          << "  (certified: " << #bvecs - #nzm << " / " << #bvecs << ")" << endl;
        nzi := {};
        if useI2 then (
            Gq := gb(J2q, DegreeLimit => d);
            Gp := gb(J2p, DegreeLimit => d);
            nzi = select(i2targets, t ->
                (t#1) % (if t#2 === "q" then Gq else Gp) != 0);
            << "   I2 targets open: " << #nzi << " / " << #i2targets;
            if #nzi > 0 then
                << "   [" << concatenate between(", ", apply(nzi, t -> t#0)) << "]";
            << endl);
        if #nz == 0 and #nzm == 0 and #nzi == 0 then (
            << "   ==> ALL bidualgen targets certified for model " << name
              << " (arbitrary-k')." << endl;
            done = true));
    if not done then
        << "   (model " << name << " left with open targets at max DegreeLimit)" << endl;
    ));

-- t4 model runs in bidualgen.m2 (this variant: xy only)
runModel(pinsA2A2,   "a2a2",   "imageline")
runModel(pinsW2F,    "W2F",    "rank1W")
runModel(pinsMu2Mu2, "mu2mu2", "imageline")
runModel(pinsMu2A2,  "mu2a2",  "rank1E")
<< endl << "DONE bidualxy" << endl;
