-- fp3gen.m2  (session 14, 2026-07-09)
-- Arbitrary-k' certificates for S' over the remaining two monomial
-- m^3 = 0, embdim-2 bases (THEORY 16.5):
--   (a) FatPoint3  R = k'[u,v]/(u,v)^3       phi = uP + vQ + u^2A + uvT + v^2B
--   (b) RingT      R = k'[u,v]/(u^2,uv,v^3)  phi = uP + vQ + v^2V
-- per split model (t^4 (c1,c4)-pinned + the four xy models), exactly as in
-- bidualgen.m2 (THEORY 16.3 encoding: digit-layered structure constants,
-- digit-0 gates, solvability-as-module-membership).
--
-- Division systems (derived by digit-matching, THEORY 16.5; m^2-components
-- of the divisors k_1, k_2 are irrelevant -- they die in u k_i and are
-- automatically in ker phi since phi(m^2 w) in m^3 I = 0):
-- (a) FatPoint3: phi(g) = u k1 + v k2, k1 = Pg + u m1 + v m2,
--     k2 = Qg + u n1 + v n2 forces m1 = Ag, n2 = Bg, m2 + n1 = Tg; then
--     ker-membership of k1, k2 <=>  pairwise nilpotence (P^2, QP, PQ, Q^2)
--     + PURE identities {A,P}g = 0, {B,Q}g = 0
--     + the 12x3 module system in the single free vector m2:
--         P m2 = TPg + QAg          Q m2 = BPg
--         P m2 = AQg + PTg          Q m2 = TQg + QTg + PBg
-- (b) RingT: uv = 0 kills the uv slot; digit-matching forces n2 = Vg,
--     m1 contributes nothing; conditions = pairwise nilpotence
--     + PURE identity {Q,V}g = 0 + the 3x3 system  Q m2 = VPg.
-- S' at cotangent generators g suffices (15.5.1: m^3 = 0 in both bases).
--
-- Success on (a) settles the FatPoint3/xy S' gap (np2/np3's exact-F2
-- `unknown`) at FULL arbitrary-k' strength; (a)+(b) + Theorems N and O
-- close S' over ALL FOUR monomial m^3 = 0 embdim-2 bases.
-- Golden rules: digit-0 + phi_0 gates before GB; "1 in J?" printed; partial
-- DegreeLimit reduction to 0 = complete certificate.

kk = ZZ/2

pinsA2A2   = set { (3,1,2), (3,2,1) };
pinsW2F    = set { (2,1,1), (3,1,2), (3,2,1) };
pinsMu2Mu2 = set { (1,1,1), (2,2,2), (3,1,2), (3,2,1), (3,1,3), (3,3,1),
                   (3,2,3), (3,3,2), (3,3,3) };
pinsMu2A2  = set { (1,1,1), (3,1,2), (3,2,1), (3,1,3), (3,3,1) };
fibXY = set { (1,2,3) };
fibT4 = set { (1,1,2), (1,2,3) };

-- baseType: "FP3" (layers u,v,u2,uv,v2 = d 1..5) or "T" (layers u,v,v2 = d 1..3)
runModel = (baseType, pins, name, caseType) -> (
    NL := if baseType === "FP3" then 5 else 3;
    << endl << "############################################################" << endl;
    << "## fp3gen: base " << baseType << ", model " << name
      << "  (case " << caseType << ", " << NL << " layers)" << endl;
    << "############################################################" << endl;
    cIx := flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
              for k from 1 to 3 list for d from 1 to NL list c_(i,j,k,d);
    mIx := flatten flatten flatten for i from 1 to 3 list for j from i to 3 list
              for r from 1 to 3 list for d from 1 to NL list m_(i,j,r,d);
    extra := if caseType === "t4" then {C1, C4} else {};
    Q := kk[ {uu, vv} | extra | cIx | mIx ];
    use Q;
    uuq := uu_Q; vvq := vv_Q;
    nilI := if baseType === "FP3"
        then ideal(uuq^3, uuq^2*vvq, uuq*vvq^2, vvq^3)
        else ideal(uuq^2, uuq*vvq, vvq^3);
    red := f -> f % nilI;
    layer := d -> (
        if baseType === "FP3" then (
            if d == 1 then uuq else if d == 2 then vvq
            else if d == 3 then uuq^2 else if d == 4 then uuq*vvq
            else vvq^2)
        else (
            if d == 1 then uuq else if d == 2 then vvq else vvq^2));
    -- digits: {f_1} | {f_layer(d)}_{d=1..NL}
    digitsQ := f -> (
        f = red f;
        f0 := sub(f, {uuq => 0, vvq => 0});
        g := f - f0;
        if baseType === "FP3" then (
            gu := sub(g, {vvq => 0});
            gv := sub(g, {uuq => 0});
            hu := gu // uuq;
            f1 := sub(hu, {uuq => 0});
            f3 := (hu - f1) // uuq;
            hv := gv // vvq;
            f2 := sub(hv, {vvq => 0});
            f5 := (hv - f2) // vvq;
            f4 := (g - gu - gv) // (uuq*vvq);
            {f0, f1, f2, f3, f4, f5}
        ) else (
            gu := sub(g, {vvq => 0});
            gv := sub(g, {uuq => 0});
            f1 := gu // uuq;
            hv := gv // vvq;
            f2 := sub(hv, {vvq => 0});
            f3 := (hv - f2) // vvq;
            {f0, f1, f2, f3}));
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
    Cc := (i,j,k) -> pin0(i,j,k) + sum for d from 1 to NL list (layer d) * c_(i,j,k,d);
    Mc := (i,j,r) -> (
        ii := min(i,j); jj := max(i,j);
        (if member((ii,jj,r), fib) then 1_Q else 0_Q)
          + sum for d from 1 to NL list (layer d) * m_(ii,jj,r,d));
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
    -- digit-reconstruction self-gate on all phi entries
    badD := 0;
    for i from 1 to 3 do for r from 1 to 3 do (
        f := (phiL#i)#r;
        dg := digitsQ f;
        rec := dg#0 + sum for d from 1 to NL list (layer d)*(dg#d);
        if red(rec - f) != 0 then badD = badD + 1);
    << "GATE digit reconstruction on phi entries: "
      << (if badD == 0 then "OK" else "FAILED") << endl;
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
    if #bad0 != 0 or #badF != 0 or badD != 0 then (
        << "!! GATE FAILURE for base " << baseType << " model " << name
          << " -- SKIPPING GB" << endl;
    ) else (
    PsiD := hashTable flatten for i from 1 to 3 list for r from 1 to 3 list
        (i,r) => digitsQ((phiL#i)#r);
    Psi := (n,i,r) -> (PsiD#(i,r))#n;
    -- layer names: FP3: P=1 Q=2 A=3 T=4 B=5;  T: P=1 Q=2 V=3
    anticomm := (n1,n2,g,r) -> sum for j from 1 to 3 list
        (Psi(n1,g,j)*Psi(n2,j,r) + Psi(n2,g,j)*Psi(n1,j,r));
    compOp2 := (n1,n2,g,r) -> sum for j from 1 to 3 list Psi(n1,g,j)*Psi(n2,j,r);
    -- compOp2(n1,n2,g,r) = (N2 N1 g)_r  [apply n1 first, then n2]
    targets := {};
    for i from 1 to 3 do (
        for pr in {("P2", (g,r) -> compOp2(1,1,g,r)), ("QP", (g,r) -> compOp2(1,2,g,r)),
                   ("PQ", (g,r) -> compOp2(2,1,g,r)), ("Q2", (g,r) -> compOp2(2,2,g,r))} do
            for r from 1 to 3 do
                targets = targets | {(pr#0 | "[" | toString i | "," | toString r | "]",
                                      (pr#1)(i,r))});
    cotgens := if caseType === "t4" then {1} else {1,2};
    for g in cotgens do for r from 1 to 3 do (
        if baseType === "FP3" then (
            targets = targets |
              {("AP[" | toString g | "," | toString r | "]", anticomm(1,3,g,r)),
               ("BQ[" | toString g | "," | toString r | "]", anticomm(2,5,g,r))};
        ) else (
            targets = targets |
              {("QV[" | toString g | "," | toString r | "]", anticomm(2,3,g,r))};
        ));
    hopf := unique select(flatten apply(vecs, v -> flatten apply(v, digitsQ)), f -> f != 0);
    f2  := unique select(fiber2E, f -> f != 0);
    Q2 := kk[ extra | cIx | mIx ];
    toQ2 := map(Q2, Q, {0_Q2, 0_Q2} | (gens Q2));
    J := ideal apply(unique(hopf | f2), g -> toQ2 g);
    tQ2 := apply(targets, t -> (t#0, toQ2 (t#1)));
    -- module systems
    Pblk := for r from 1 to 3 list for j from 1 to 3 list toQ2 Psi(1,j,r);
    Qblk := for r from 1 to 3 list for j from 1 to 3 list toQ2 Psi(2,j,r);
    Mmat := if baseType === "FP3"
        then matrix (Pblk | Qblk | Pblk | Qblk)
        else matrix Qblk;
    nrows := if baseType === "FP3" then 12 else 3;
    bvecs := apply(cotgens, g -> (
        rhs := if baseType === "FP3" then (
            (for r from 1 to 3 list toQ2 (compOp2(1,4,g,r) + compOp2(3,2,g,r))) |
            (for r from 1 to 3 list toQ2 (compOp2(1,5,g,r))) |
            (for r from 1 to 3 list toQ2 (compOp2(2,3,g,r) + compOp2(4,1,g,r))) |
            (for r from 1 to 3 list toQ2 (compOp2(2,4,g,r) + compOp2(4,2,g,r)
                                          + compOp2(5,1,g,r)))
        ) else (
            for r from 1 to 3 list toQ2 (compOp2(1,3,g,r))
        );
        (g, transpose matrix {rhs})));
    Nmod := image Mmat + J*(Q2^nrows);
    << "#vars: " << numgens Q2 << "  #eqs: " << numgens J
      << "  #ideal targets: " << #tQ2
      << "  #module targets: " << #bvecs << endl;
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
        << "   Msys open at g in {" << concatenate between(", ",
              apply(nzm, b -> toString(b#0))) << "}"
          << "  (certified: " << #bvecs - #nzm << " / " << #bvecs << ")" << endl;
        if #nz == 0 and #nzm == 0 then (
            << "   ==> ALL fp3gen targets certified for base " << baseType
              << " model " << name << " (arbitrary-k')." << endl;
            done = true));
    if not done then
        << "   (base " << baseType << " model " << name
          << " left with open targets at max DegreeLimit)" << endl;
    ));

-- RingT first (3 layers, cheaper), then FatPoint3 (the np3 gap ring)
runModel("T",   null,       "t4",     "t4")
runModel("T",   pinsA2A2,   "a2a2",   "imageline")
runModel("T",   pinsW2F,    "W2F",    "rank1W")
runModel("T",   pinsMu2Mu2, "mu2mu2", "imageline")
runModel("T",   pinsMu2A2,  "mu2a2",  "rank1E")
runModel("FP3", null,       "t4",     "t4")
runModel("FP3", pinsA2A2,   "a2a2",   "imageline")
runModel("FP3", pinsW2F,    "W2F",    "rank1W")
runModel("FP3", pinsMu2Mu2, "mu2mu2", "imageline")
runModel("FP3", pinsMu2A2,  "mu2a2",  "rank1E")
<< endl << "DONE fp3gen" << endl;
