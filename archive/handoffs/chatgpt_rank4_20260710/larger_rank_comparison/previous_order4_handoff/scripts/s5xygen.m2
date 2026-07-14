-- s5xygen.m2  (session 13, 2026-07-09)
-- Arbitrary-k' certificates for the s = 5 divided-[4] identity over
-- R = k'[eps]/eps^5, xy fiber, PER SPLIT MODEL (THEORY 12.4.1), following
-- the s4xygen.m2 pinning pattern (which certified Theorem M(xy) in ~3 min).
--
-- COTANGENT REDUCTION (fifth note Lemma 1.1 + THEORY 15.3): with s <= 4
-- banked (Theorems I, L, M(xy)), the product-class row i = 3 (source z = xy)
-- of D5 vanishes formally; the open content is rows i = 1, 2 (sources x, y).
--
-- BANKED-IDENTITY BOOST: D2, D3, D4 components adjoined to J as generators.
-- Soundness as in s5t4gen.m2's header: banked identities vanish at every
-- k'-point of V(J) (per split model, any F_2-algebra k' -- the 12.4.3/L/M(xy)
-- proofs and s4xygen certificates are per-model, arbitrary-k'), so
-- target in J_aug ==> target vanishes on all solutions (record as
-- "vanishing-on-solutions", not raw membership).
-- Success on rows 1,2 in all four models ==> **Theorem (s = 5, xy)** via the
-- 12.4.3 descent (perfect-subfield proviso), which with s5t4gen closes s = 5.

kk = ZZ/2
NN = 5

pinsA2A2   = set { (3,1,2), (3,2,1) };
pinsW2F    = set { (2,1,1), (3,1,2), (3,2,1) };
pinsMu2Mu2 = set { (1,1,1), (2,2,2), (3,1,2), (3,2,1), (3,1,3), (3,3,1),
                   (3,2,3), (3,3,2), (3,3,3) };
pinsMu2A2  = set { (1,1,1), (3,1,2), (3,2,1), (3,1,3), (3,3,1) };

fibXY = set { (1,2,3) };   -- mu_0: x*y = z, x^2 = y^2 = 0

runModel = (pins, name) -> (
    << endl << "############################################################" << endl;
    << "## s5xygen: split model " << name << "  (xy fiber, eps^" << NN << " = 0)" << endl;
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
        Dcomp := (s,i,r) -> sum flatten for n from 1 to s-1 list (
            m := s-n;
            if m < 1 or m > NN-1 or n > NN-1 then {}
            else for rho from 1 to 3 list Psi(n,i,rho) * Psi(m,rho,r));
        bankedD := flatten for s in {2,3,4} list
            flatten for i from 1 to 3 list for r from 1 to 3 list Dcomp(s,i,r);
        targets := flatten for i from 1 to 3 list for r from 1 to 3 list
            ("D5[" | toString i | "," | toString r | "]", Dcomp(5,i,r));
        cotNames := set {"D5[1,1]", "D5[1,2]", "D5[1,3]",
                         "D5[2,1]", "D5[2,2]", "D5[2,3]"};
        hopf := unique select(flatten apply(vecs, v -> flatten apply(v, digitsQ)), f -> f != 0);
        f2  := unique select(fiber2E, f -> f != 0);
        Q2 := kk[ cIx | mIx ];
        toQ2 := map(Q2, Q, {0_Q2} | (gens Q2));
        bankedQ2 := select(apply(bankedD, g -> toQ2 g), f -> f != 0);
        J := ideal (apply(unique(hopf | f2), g -> toQ2 g) | bankedQ2);
        tQ2 := apply(targets, t -> (t#0, toQ2 (t#1)));
        << "#vars: " << numgens Q2 << "  #eqs (incl. " << #bankedQ2
          << " banked): " << numgens J << "  #targets: " << #tQ2 << endl;
        done := false;
        cotDone := false;
        for d in {2,3,4,5,6,7,8} do (
            if done then break;
            << "-- gb DegreeLimit " << d << ": " << flush;
            elapsedTime G := gb(J, DegreeLimit => d);
            nz := select(tQ2, t -> (t#1) % G != 0);
            << "   nonzero remainders: " << #nz << " / " << #tQ2
              << "   (1 in J? " << (1_Q2 % G == 0) << ")" << endl;
            if #nz > 0 then
                << "   still open: " << concatenate between(", ", apply(nz, t -> t#0)) << endl;
            nzCot := select(nz, t -> member(t#0, cotNames));
            if #nzCot == 0 and not cotDone then (
                << "   ==> COTANGENT ROWS D5[1,*], D5[2,*] all in J_aug for "
                  << name << "." << endl;
                cotDone = true);
            if #nz == 0 then (
                << "   ==> ALL s5xygen targets in J_aug for " << name << "." << endl;
                done = true));
        );
    );

runModel(pinsA2A2,   "alpha2 x alpha2");
runModel(pinsW2F,    "W2[F]");
runModel(pinsMu2Mu2, "mu2 x mu2");
runModel(pinsMu2A2,  "mu2 x alpha2");

<< endl << "DONE s5xygen" << endl;
