-- s4t4gen.m2  (session 12, 2026-07-09)
-- Arbitrary-k' ideal-membership certificates for the s = 4 divided-[4] identity
-- over R = k'[eps]/eps^4, t^4 fiber, with the fiber comultiplication pinned to
-- the BANKED normal form (Theorem I step, THEORY 12.3, hand-proved + gated
-- firstorder_gates 51/51):
--     w0(t)  = c1 (t o t^2) + c1^2 (t^2 o t^3) + c4 t^2(x)t^2      (o = symm)
-- and its multiplicativity consequences (hand-derived session 12, char 2:
-- all squares of w0t-monomials die since every monomial has a leg of degree
-- >= 2, and Delta_0(t^2) = (Delta_0 t)^2, Delta_0(t^3) = Delta_0(t)Delta_0(t^2)):
--     w0(t^2) = 0,
--     w0(t^3) = t o t^2 + c1 (t^2 o t^3).
-- This replaces s4gen.m2's 27 free digit-0 comultiplication variables by TWO
-- parameters (c1, c4), which is what made the xy per-model runs (s4xygen.m2)
-- ~50x faster.  SOUNDNESS: the normal form is a theorem about EVERY
-- killed-by-2 t^4-shaped fiber (any k', any Delta_0), so substituting it does
-- not shrink the solution variety; the digit-0 gate below verifies the family
-- is self-consistent (all digit-0 axiom parts must vanish IDENTICALLY as
-- polynomials in c1, c4 -- a wrong pin table shows up here).
-- Targets: the nine D4 components + the third handoff's named scalars
-- (same list as s4gen.m2's t^4 stage).  Success ==> Theorem M(t^4) at machine
-- strength = banking rule THEORY 14.5(a), independent of the still-running
-- s4cert F4 battery and of s4gen's free-Delta_0 grind.

kk = ZZ/2
NN = 4

<< endl << "############################################################" << endl;
<< "## s4t4gen: t^4 fiber, Delta_0 pinned to (c1,c4) normal form, eps^" << NN << endl;
<< "############################################################" << endl;

cIx = flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
          for k from 1 to 3 list for d from 1 to NN-1 list c_(i,j,k,d);
mIx = flatten flatten flatten for i from 1 to 3 list for j from i to 3 list
          for r from 1 to 3 list for d from 1 to NN-1 list m_(i,j,r,d);
Q = kk[ {eps, C1, C4} | cIx | mIx ];
epsq = eps_Q;
c1q = C1_Q;
c4q = C4_Q;
epsI = ideal(epsq^NN);
red = f -> f % epsI;
digitsQ = f -> (
    f = red f;
    out := {};
    for d from 0 to NN-1 do (
        f0 := sub(f, {epsq => 0});
        out = append(out, f0);
        f = (f - f0)//epsq);
    out);
ebas = i -> apply(4, k -> if k == i then 1_Q else 0_Q);
idx2 = (a,b) -> 4*a + b;
idx3 = (a,b,cc) -> 16*a + 4*b + cc;

-- digit-0 comultiplication pins (basis e1 = t, e2 = t^2, e3 = t^3)
pin0 = (i,j,k) -> (
    if i == 1 then (
        if (j,k) == (1,2) or (j,k) == (2,1) then c1q
        else if (j,k) == (2,3) or (j,k) == (3,2) then c1q^2
        else if (j,k) == (2,2) then c4q
        else 0_Q)
    else if i == 2 then 0_Q
    else (
        if (j,k) == (1,2) or (j,k) == (2,1) then 1_Q
        else if (j,k) == (2,3) or (j,k) == (3,2) then c1q
        else 0_Q));
Cc = (i,j,k) -> pin0(i,j,k) + sum for d from 1 to NN-1 list epsq^d * c_(i,j,k,d);
fibT4 = set { (1,1,2), (1,2,3) };
Mc = (i,j,r) -> (
    ii := min(i,j); jj := max(i,j);
    (if member((ii,jj,r), fibT4) then 1_Q else 0_Q)
      + sum for d from 1 to NN-1 list epsq^d * m_(ii,jj,r,d));
Stab = hashTable flatten for a from 0 to 3 list for b from 0 to 3 list
    (a,b) => (if a == 0 then ebas b else if b == 0 then ebas a
              else {0_Q, Mc(a,b,1), Mc(a,b,2), Mc(a,b,3)});
DEl = for i from 0 to 3 list (
    if i == 0 then apply(16, t -> if t == 0 then 1_Q else 0_Q)
    else (
        v := new MutableList from toList(16:0_Q);
        v#(idx2(i,0)) = v#(idx2(i,0)) + 1_Q;
        v#(idx2(0,i)) = v#(idx2(0,i)) + 1_Q;
        for j from 1 to 3 do for k from 1 to 3 do
            v#(idx2(j,k)) = v#(idx2(j,k)) + Cc(i,j,k);
        apply(toList v, red)));
mulA = (u,v) -> (
    out := new MutableList from toList(4:0_Q);
    for i from 0 to 3 do if u#i != 0 then
    for j from 0 to 3 do if v#j != 0 then (
        Sij := Stab#(i,j);
        for r from 0 to 3 do if Sij#r != 0 then
            out#r = out#r + u#i * v#j * Sij#r);
    apply(toList out, red));
assocV = flatten flatten for i from 1 to 3 list for j from 1 to 3 list
    for k from 1 to 3 list (
    u := mulA(mulA(ebas i, ebas j), ebas k);
    w := mulA(ebas i, mulA(ebas j, ebas k));
    apply(4, t -> u#t + w#t));
DofVec = v -> (
    out := new MutableList from toList(16:0_Q);
    for r from 0 to 3 do if v#r != 0 then (
        D := DEl#r;
        for t from 0 to 15 do if D#t != 0 then out#t = out#t + v#r * D#t);
    apply(toList out, red));
mulT2 = (u,v) -> (
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
compatV = flatten for i from 1 to 3 list for j from i to 3 list (
    lhs := DofVec(Stab#(i,j));
    rhs := mulT2(DEl#i, DEl#j);
    apply(16, t -> lhs#t + rhs#t));
coassocV = for i from 1 to 3 list (
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
phiL = for i from 0 to 3 list (
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
fiber2E = flatten for i from 1 to 3 list
    for r from 1 to 3 list (digitsQ((phiL#i)#r))#0;

-- ===== GATE: digit-0 consistency of the (c1,c4) family =====
vecs = assocV | compatV | coassocV;
dig0 = flatten apply(vecs, v -> apply(v, f -> (digitsQ f)#0));
bad0 = select(dig0, f -> f != 0);
<< "GATE digit-0 axioms of (c1,c4)-pinned fiber identically 0: "
  << (if #bad0 == 0 then "OK" else "FAILED -- offenders:") << endl;
if #bad0 != 0 then (scan(bad0, f -> << "    " << f << endl););
badF = select(fiber2E, f -> f != 0);
<< "GATE phi_0 = 0 (fiber killed by 2): "
  << (if #badF == 0 then "OK" else "FAILED") << endl;
if #bad0 != 0 or #badF != 0 then (
    << "!! GATE FAILURE -- ABORTING (pin table wrong?)" << endl;
) else (
    PsiD := hashTable flatten for i from 1 to 3 list for r from 1 to 3 list
        (i,r) => digitsQ((phiL#i)#r);
    Psi := (n,i,r) -> (PsiD#(i,r))#n;
    targets := flatten for i from 1 to 3 list for r from 1 to 3 list (
        f := sum for rho from 1 to 3 list (
              Psi(1,i,rho) * Psi(3,rho,r)
            + Psi(2,i,rho) * Psi(2,rho,r)
            + Psi(3,i,rho) * Psi(1,rho,r));
        ("D4[" | toString i | "," | toString r | "]", f));
    B := Psi(1,1,2); Cx := Psi(1,1,3);
    aa := m_(2,2,1,1); bb := m_(2,2,2,1);
    pp := m_(1,1,1,1); qq := m_(1,2,1,1);
    pp2 := m_(1,1,2,1); pp3 := m_(1,1,3,1);
    qq2 := m_(1,2,2,1); qq3 := m_(1,2,3,1);
    sig2 := pp*pp2 + qq*pp3 + m_(1,1,1,2);
    sig3 := pp*qq2 + qq*qq3 + m_(1,2,1,2);
    Qd := Psi(2,1,2); Rd := Psi(2,1,3);
    Lam := Psi(3,1,1) + Qd*pp + Rd*qq + B*sig2 + Cx*sig3;
    targets = targets | {
        ("aB", aa*B), ("aC", aa*Cx), ("BC", B*Cx),
        ("Lam+bB2", Lam + bb*B^2),
        ("LamB+bB3", Lam*B + bb*B^3), ("LamC", Lam*Cx),
        ("aB3", aa*B^3), ("aB2C", aa*B^2*Cx)};
    hopf := unique select(flatten apply(vecs, v -> flatten apply(v, digitsQ)), f -> f != 0);
    f2  := unique select(fiber2E, f -> f != 0);
    Q2 := kk[ {C1, C4} | cIx | mIx ];
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
            << "   ==> ALL s4t4gen targets in J (arbitrary-k' certificate, t^4"
              << " (c1,c4)-family)." << endl;
            done = true));
    );
<< endl << "DONE s4t4gen" << endl;
