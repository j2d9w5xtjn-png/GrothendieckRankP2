-- s4xygen.m2  (session 12, 2026-07-09)
-- Arbitrary-k' ideal-membership certificates for the s = 4 divided-[4] identity
-- over R = k'[eps]/eps^4, xy fiber, PER SPLIT MODEL (the four models of
-- THEORY 12.4.1: alpha_2^2, W_2[F], mu_2^2, mu_2 x alpha_2).
--
-- This is the targeted Groebner job recommended by the FOURTH external note
-- (order4_max_pass_xy_s4.md, 2026-07-09): instead of s4gen.m2's xy stage
-- (Delta_0 FREE, 27 extra variables, GB very heavy), we pin Delta_0 AND mu_0
-- to each split model -- exactly the setting of the note's F2 gates and of the
-- Theorem I/L descent mechanism (12.4.1: any killed-by-2 xy fiber defined over
-- a perfect subfield becomes one of the four models after faithfully flat base
-- change, and the D4 = 0 identity descends).
--
-- Targets per model:
--   (i)  the note's displayed per-case identities (Lemma A operator package
--        for the image-line cases; rank-one normal forms + four L-identities
--        for W2F / mu2a2) -- each membership = the arbitrary-k' upgrade of one
--        note gate;
--   (ii) the nine components of D4 = Psi1 Psi3 + Psi2 Psi2 + Psi3 Psi1 -- the
--        endpoint itself, so Theorem M(xy) can land even if some intermediate
--        normal form fails to certify.
-- All four models landing (ii) ==> s = 4 for the xy fiber over every
-- F_2-algebra k' (fiber defined over a perfect subfield), which with
-- Theorem K (t^4, s=4 chain: THEORY 14.1-14.6) + 12.6.1 + Thm 7.1 gives
-- S'-universality over k'[eps]/eps^4 and killed-by-4 over k'[eps]/eps^5.
--
-- GATE (golden rule 1): with all digit-0 structure constants pinned, the
-- digit-0 part of EVERY axiom equation is a constant; if a pin table were
-- wrong, some constant would be 1, J would contain 1, and every "certificate"
-- would be vacuous.  We assert all digit-0 parts vanish and phi_0 = 0
-- (model killed by 2) BEFORE the GB loop, and print the gate verdict.
-- Golden rule 4: a target reducing to 0 against a PARTIAL (DegreeLimit) GB is
-- a complete cofactor certificate for that target (partial logs = proofs).

kk = ZZ/2
NN = 4

-- split-model comultiplication pins: Delta_0(e_i) = e_i(x)1 + 1(x)e_i
--   + sum_{(i,j,k) in pins} e_j(x)e_k,  basis e1 = x, e2 = y, e3 = z = xy.
-- (verified by hand against Delta(x)Delta(y) in each model, session 12)
pinsA2A2   = set { (3,1,2), (3,2,1) };
pinsW2F    = set { (2,1,1), (3,1,2), (3,2,1) };
pinsMu2Mu2 = set { (1,1,1), (2,2,2), (3,1,2), (3,2,1), (3,1,3), (3,3,1),
                   (3,2,3), (3,3,2), (3,3,3) };
pinsMu2A2  = set { (1,1,1), (3,1,2), (3,2,1), (3,1,3), (3,3,1) };

fibXY = set { (1,2,3) };   -- mu_0: x*y = z, x^2 = y^2 = 0

runModel = (pins, name, caseType) -> (
    << endl << "############################################################" << endl;
    << "## s4xygen: split model " << name << "  (xy fiber, eps^" << NN << " = 0)" << endl;
    << "############################################################" << endl;
    cIx := flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
              for k from 1 to 3 list for d from 1 to NN-1 list c_(i,j,k,d);
    mIx := flatten flatten flatten for i from 1 to 3 list for j from i to 3 list
              for r from 1 to 3 list for d from 1 to NN-1 list m_(i,j,r,d);
    Q := kk[ {eps} | cIx | mIx ];
    use Q;
    epsq := eps_Q;
    epsI := ideal(epsq^NN);
    red := f -> f % epsI;
    digitsQ := f -> (
        f = red f;
        out := {};
        for d from 0 to NN-1 do (
            f0 := sub(f, {epsq => 0});
            out = append(out, f0);
            f = (f - f0)//epsq);
        out);
    ebas := i -> apply(4, k -> if k == i then 1_Q else 0_Q);
    idx2 := (a,b) -> 4*a + b;
    idx3 := (a,b,cc) -> 16*a + 4*b + cc;
    Cc := (i,j,k) -> (if member((i,j,k), pins) then 1_Q else 0_Q)
          + sum for d from 1 to NN-1 list epsq^d * c_(i,j,k,d);
    Mc := (i,j,r) -> (
        ii := min(i,j); jj := max(i,j);
        (if member((ii,jj,r), fibXY) then 1_Q else 0_Q)
          + sum for d from 1 to NN-1 list epsq^d * m_(ii,jj,r,d));
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
    -- ===== GATE: digit-0 consistency of the pinned model =====
    vecs := assocV | compatV | coassocV;
    dig0 := apply(flatten apply(vecs, v -> apply(v, f -> (digitsQ f)#0)), f -> f);
    bad0 := select(dig0, f -> f != 0);
    << "GATE digit-0 axioms of pinned model identically 0: "
      << (if #bad0 == 0 then "OK" else "FAILED") << endl;
    badF := select(fiber2E, f -> f != 0);
    << "GATE phi_0 = 0 (model killed by 2): "
      << (if #badF == 0 then "OK" else "FAILED (" | toString(#badF) | " nonzero)") << endl;
    if #bad0 != 0 or #badF != 0 then (
        << "!! GATE FAILURE for model " << name << " -- SKIPPING GB (pins wrong?)" << endl;
    ) else (
    -- layer digits of phi: PsiD#(i,r) = {Psi_0(e_i)_r, ..., Psi_3(e_i)_r}
    PsiD := hashTable flatten for i from 1 to 3 list for r from 1 to 3 list
        (i,r) => digitsQ((phiL#i)#r);
    Psi := (n,i,r) -> (PsiD#(i,r))#n;
    -- D4 components (always targets)
    targets := flatten for i from 1 to 3 list for r from 1 to 3 list (
        f := sum for rho from 1 to 3 list (
              Psi(1,i,rho) * Psi(3,rho,r)
            + Psi(2,i,rho) * Psi(2,rho,r)
            + Psi(3,i,rho) * Psi(1,rho,r));
        ("D4[" | toString i | "," | toString r | "]", f));
    -- note's per-case identities
    if caseType === "imageline" then (
        cx := Psi(1,1,3); cy := Psi(1,2,3);
        cof := g -> (if g == 1 then cx else if g == 2 then cy else 0_Q);
        -- N-shape: Psi1 = ell(.) z, Psi1(z) = 0
        for i from 1 to 3 do for r from 1 to 3 do
            if not ((i == 1 and r == 3) or (i == 2 and r == 3)) then
                targets = targets | {("Nshape[" | toString i | "," | toString r | "]",
                                      Psi(1,i,r))};
        if name === "mu2mu2" then (
            for r from 1 to 3 do targets = targets |
                {("Mz[" | toString r | "]", Psi(2,3,r)),
                 ("Lz[" | toString r | "]", Psi(3,3,r))};
        ) else (
            -- a2a2: M(z) in k'z only
            targets = targets | {("Mz[1]", Psi(2,3,1)), ("Mz[2]", Psi(2,3,2))};
        );
        for g from 1 to 3 do (
            for r from 1 to 2 do (
                f := (sum for rho from 1 to 3 list Psi(2,g,rho)*Psi(2,rho,r))
                     + (cof g)*Psi(3,3,r);
                targets = targets | {("LemA1[" | toString g | "," | toString r | "]", f)});
            f := (sum for rho from 1 to 3 list Psi(2,g,rho)*Psi(2,rho,3))
                 + (cof g)*Psi(3,3,3) + cx*Psi(3,g,1) + cy*Psi(3,g,2);
            targets = targets | {("LemA2[" | toString g | "]", f)});
    ) else if caseType === "rank1W" then (
        -- W2F: lam = mu1(x,x)_x, nu = mu1(y,y)_x, mm = mu1(x,y)_y,
        --      alp = (w1 x)_{11}, del = (w1 x)_{22}, rho = lam alp + nu del,
        --      chi = (Psi2 y)_z
        lam := m_(1,1,1,1); nu := m_(2,2,1,1); mm := m_(1,2,2,1);
        alp := c_(1,1,1,1); del := c_(1,2,2,1);
        rho := lam*alp + nu*del; chi := Psi(2,2,3);
        targets = targets |
          {("N[1,1]", Psi(1,1,1)), ("N[1,2]", Psi(1,1,2)), ("N[1,3]", Psi(1,1,3)),
           ("N[2,1]+lam", Psi(1,2,1) + lam), ("N[2,2]", Psi(1,2,2)), ("N[2,3]", Psi(1,2,3)),
           ("N[3,1]", Psi(1,3,1)), ("N[3,2]", Psi(1,3,2)), ("N[3,3]", Psi(1,3,3)),
           ("Mx=rho x (1)", Psi(2,1,1) + rho), ("Mx (2)", Psi(2,1,2)), ("Mx (3)", Psi(2,1,3)),
           ("Myy=rho", Psi(2,2,2) + rho),
           ("Mz (1)", Psi(2,3,1) + mm*lam), ("Mz (2)", Psi(2,3,2)), ("Mz (3)", Psi(2,3,3)),
           ("lam Lx_y=rho^2", lam*Psi(3,1,2) + rho^2),
           ("lam Lx_z=rho chi", lam*Psi(3,1,3) + rho*chi),
           ("Lz_y=mm rho", Psi(3,3,2) + mm*rho),
           ("lam(Ly_y+Lx_x+mm chi)", lam*(Psi(3,2,2) + Psi(3,1,1) + mm*chi))};
    ) else (
        -- mu2a2 (x <-> y dual): lam = mu1(x,x)_y, nu = mu1(y,y)_y, mm = mu1(x,y)_x,
        --      alp = (w1 y)_{11}, del = (w1 y)_{22}, rho = lam alp + nu del,
        --      chi = (Psi2 x)_z
        lam2 := m_(1,1,2,1); nu2 := m_(2,2,2,1); mm2 := m_(1,2,1,1);
        alp2 := c_(2,1,1,1); del2 := c_(2,2,2,1);
        rho2 := lam2*alp2 + nu2*del2; chi2 := Psi(2,1,3);
        targets = targets |
          {("N[1,1]", Psi(1,1,1)), ("N[1,2]+lam", Psi(1,1,2) + lam2), ("N[1,3]", Psi(1,1,3)),
           ("N[2,1]", Psi(1,2,1)), ("N[2,2]", Psi(1,2,2)), ("N[2,3]", Psi(1,2,3)),
           ("N[3,1]", Psi(1,3,1)), ("N[3,2]", Psi(1,3,2)), ("N[3,3]", Psi(1,3,3)),
           ("My=rho y (1)", Psi(2,2,1)), ("My (2)", Psi(2,2,2) + rho2), ("My (3)", Psi(2,2,3)),
           ("Mxx=rho", Psi(2,1,1) + rho2),
           ("Mz (1)", Psi(2,3,1)), ("Mz (2)", Psi(2,3,2) + mm2*lam2), ("Mz (3)", Psi(2,3,3)),
           ("lam Ly_x=rho^2", lam2*Psi(3,2,1) + rho2^2),
           ("lam Ly_z=rho chi", lam2*Psi(3,2,3) + rho2*chi2),
           ("Lz_x=mm rho", Psi(3,3,1) + mm2*rho2),
           ("lam(Lx_x+Ly_y+mm chi)", lam2*(Psi(3,1,1) + Psi(3,2,2) + mm2*chi2))};
    );
    hopf := unique select(flatten apply(vecs, v -> flatten apply(v, digitsQ)), f -> f != 0);
    f2  := unique select(fiber2E, f -> f != 0);
    Q2 := kk[ cIx | mIx ];
    toQ2 := map(Q2, Q, {0_Q2} | (gens Q2));
    J := ideal apply(unique(hopf | f2), g -> toQ2 g);
    tQ2 := apply(targets, t -> (t#0, toQ2 (t#1)));
    << "#vars: " << numgens Q2 << "  #eqs: " << numgens J
      << "  #targets: " << #tQ2 << endl;
    done := false;
    for d in {2,3,4,5,6,8} do (
        if done then break;
        << "-- gb DegreeLimit " << d << ": " << flush;
        elapsedTime G := gb(J, DegreeLimit => d);
        nz := select(tQ2, t -> (t#1) % G != 0);
        << "   nonzero remainders: " << #nz << " / " << #tQ2
          << "   (1 in J? " << (1_Q2 % G == 0) << ")" << endl;
        if #nz > 0 then
            << "   still open: " << concatenate between(", ", apply(nz, t -> t#0)) << endl;
        if #nz == 0 then (
            << "   ==> ALL s4xygen targets in J (arbitrary-k' certificate, model "
              << name << ")." << endl;
            done = true));
    ));

runModel(pinsA2A2,   "a2a2",   "imageline")
runModel(pinsW2F,    "W2F",    "rank1W")
runModel(pinsMu2Mu2, "mu2mu2", "imageline")
runModel(pinsMu2A2,  "mu2a2",  "rank1E")
<< endl << "DONE s4xygen" << endl;
