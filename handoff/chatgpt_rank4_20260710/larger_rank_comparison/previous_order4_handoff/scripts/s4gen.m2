-- s4gen.m2  (session 11, 2026-07-09)
-- Arbitrary-k' ideal-membership certificates for the s = 4 divided-[4] identity
-- over R = k'[eps]/eps^4, BOTH fibers.  Encoding identical to search_eps45.m2
-- (= gensearch.m2 conventions); the only change is the REDUCTION TARGETS:
-- instead of the [4]^# coefficients we reduce
--   (i)  the nine components of D4 := Psi1 Psi3 + Psi2 Psi2 + Psi3 Psi1
--        (s = 4 layer identity, THEORY 12.6.1/12.6.6); membership in J proves
--        the identity for EVERY F_2-algebra k' -- t^4 fiber: upgrades the third
--        external handoff (order4_further_push_s4_t4.md, machine-gated by
--        s4cert.py) to theorem strength; xy fiber: the remaining OPEN frontier;
--   (ii) for the t^4 fiber additionally the note's named scalars
--        aB, aC, BC, Lambda + bB^2, Lambda*B + bB^3, Lambda*C, aB^3, aB^2C
--        (THEORY 12.6.6(e) four-scalar reduction + the note's sharper forms).
-- Success on both fibers ==> S'-universality over k'[eps]/eps^4 and
-- killed-by-4 over k'[eps]/eps^5, both fibers, arbitrary k' (12.6.1 + Thm 7.1)
-- -- fully subsuming search_eps45's still-open eps^5 stages.
-- Golden rule: a target reducing to 0 against a PARTIAL (DegreeLimit) GB is a
-- complete cofactor certificate for that target -- partial logs = partial proofs.

kk = ZZ/2
NN = 4

runCert = (fibKeys, name, extraT4) -> (
    << endl << "############################################################" << endl;
    << "## s4gen: " << name << "   (eps^" << NN << " = 0, fiber2: true)" << endl;
    << "############################################################" << endl;
    cIx := flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
              for k from 1 to 3 list for d from 0 to NN-1 list c_(i,j,k,d);
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
    Cc := (i,j,k) -> sum for d from 0 to NN-1 list epsq^d * c_(i,j,k,d);
    Mc := (i,j,r) -> (
        ii := min(i,j); jj := max(i,j);
        (if member((ii,jj,r), fibKeys) then 1_Q else 0_Q)
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
    -- layer digits of phi: PsiD#(i,r) = {Psi_0(e_i)_r, ..., Psi_3(e_i)_r}
    PsiD := hashTable flatten for i from 1 to 3 list for r from 1 to 3 list
        (i,r) => digitsQ((phiL#i)#r);
    -- targets: the nine D4 components (composition (Psi_m Psi_n)(e_i)_r =
    -- sum_rho Psi_n(e_i)_rho * Psi_m(e_rho)_r; symmetric in the (m,n) list)
    targets := flatten for i from 1 to 3 list for r from 1 to 3 list (
        f := sum for rho from 1 to 3 list (
              (PsiD#(i,rho))#1 * (PsiD#(rho,r))#3
            + (PsiD#(i,rho))#2 * (PsiD#(rho,r))#2
            + (PsiD#(i,rho))#3 * (PsiD#(rho,r))#1);
        ("D4[" | toString i | "," | toString r | "]", f));
    if extraT4 then (
        B := (PsiD#(1,2))#1; Cx := (PsiD#(1,3))#1;
        aa := m_(2,2,1,1); bb := m_(2,2,2,1);
        pp := m_(1,1,1,1); qq := m_(1,2,1,1);
        pp2 := m_(1,1,2,1); pp3 := m_(1,1,3,1);
        qq2 := m_(1,2,2,1); qq3 := m_(1,2,3,1);
        sig2 := pp*pp2 + qq*pp3 + m_(1,1,1,2);
        sig3 := pp*qq2 + qq*qq3 + m_(1,2,1,2);
        Qd := (PsiD#(1,2))#2; Rd := (PsiD#(1,3))#2;
        Lam := (PsiD#(1,1))#3 + Qd*pp + Rd*qq + B*sig2 + Cx*sig3;
        targets = targets | {
            ("aB", aa*B), ("aC", aa*Cx), ("BC", B*Cx),
            ("Lam+bB2", Lam + bb*B^2),
            ("LamB+bB3", Lam*B + bb*B^3), ("LamC", Lam*Cx),
            ("aB3", aa*B^3), ("aB2C", aa*B^2*Cx)});
    vecs := assocV | compatV | coassocV;
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
            << "   ==> ALL s4gen targets in J (arbitrary-k' certificate, " << name << ")." << endl;
            done = true));
    );

fib2t = set { (1,1,2), (1,2,3) };    -- fiber k[t]/(t^4)  (certifies the note)
fib1  = set { (1,2,3) };             -- fiber k[x,y]/(x^2,y^2)  (OPEN frontier)

runCert(fib2t, "fiber k[t]/(t^4), eps^4, D4 + note scalars", true)
runCert(fib1,  "fiber k[x,y]/(x^2,y^2), eps^4, D4", false)
<< endl << "DONE s4gen" << endl;
