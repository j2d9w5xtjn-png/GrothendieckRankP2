-- certs.m2
-- Extract and verify explicit membership certificates for the eps^3 theorem:
-- each coefficient b of [4]^# is written as b = sum_i q_i * g_i with g_i the
-- associativity and Delta-multiplicativity equations.  minassoc.m2 proves the
-- stronger fact that these two axiom families alone force [4]^# = 0, so we do
-- not burden the computation with coassociativity or fiber equations.
--
-- Memory note (2026-07-10): the old implementation requested
-- ChangeMatrix=>true for the entire partial Groebner basis.  That retained a
-- lift of every GB element against 403+ original equations and reached 43 GiB
-- RSS.  Here we track against the smaller 157/178-generator ideal, divide each
-- target directly by the engine GB (without copying getChangeMatrix/gens), and
-- run each branch in a fresh process.  The final identity is still
-- re-verified by direct matrix multiplication against the original generators
-- (no Groebner reduction is involved in the verification step).
-- Certificates are saved to scripts/certs_<branch>.m2out.

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
    {f0, g0, sub(h, {eps => 0})});
ebas = i -> apply(4, k -> if k == i then 1_Q else 0_Q);
idx2 = (a,b) -> 4*a + b;
idx3 = (a,b,cc) -> 16*a + 4*b + cc;
Cc = (i,j,k) -> c_(i,j,k,0) + eps*c_(i,j,k,1) + eps^2*c_(i,j,k,2);

doBranch = (fibKeys, name) -> (
    Mc := (i,j,r) -> (
        ii := min(i,j); jj := max(i,j);
        (if member((ii,jj,r), fibKeys) then 1_Q else 0_Q)
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
        ww := mulA(ebas i, mulA(ebas j, ebas k));
        apply(4, t -> u#t + ww#t));
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
    -- Coassociativity is deliberately not generated: assoc+compat already
    -- imply every target (scripts/minassoc.log), a strictly stronger result.
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
    P4L := for i from 1 to 3 list (
        p := phiL#i;
        out := new MutableList from toList(4:0_Q);
        for r from 0 to 3 do if p#r != 0 then (
            ph := phiL#r;
            for t from 0 to 3 do if ph#t != 0 then
                out#t = out#t + p#r * ph#t);
        apply(toList out, red));
    vecs := assocV | compatV;
    hopf := unique select(flatten apply(vecs, v -> flatten apply(v, digitsQ)), f -> f != 0);
    bL := unique select(flatten apply(P4L, v -> flatten apply(v, digitsQ)), f -> f != 0);
    Q2 := kk[ cIx | mIx ];
    toQ2 := map(Q2, Q, {0_Q2} | (gens Q2));
    gensList := apply(unique hopf, g -> toQ2 g);
    Gmat := matrix{gensList};
    bQ2 := apply(bL, g -> toQ2 g);
    degLim := if name === "xy" then 5 else 6;
    expectedE := if name === "xy" then 157 else 178;
    expectedB := if name === "xy" then 21 else 24;
    assert(#gensList == expectedE);
    assert(#bQ2 == expectedB);
    << "branch " << name << ": " << #gensList
      << " assoc+compat equations, " << #bQ2 << " P4 coefficients; "
      << "tracked GB through degree " << degLim << endl << flush;
    << "  generator degrees: "
      << tally apply(gensList, g -> first degree g) << endl << flush;
    if getenv "CERT_GENERATE_ONLY" === "1" then return null;
    -- Keep the change data inside the engine.  Calling gens/getChangeMatrix
    -- and multiplying the two matrices made several enormous copies in the
    -- old script.  Division by G already returns rows indexed by Gmat's
    -- original generators.
    elapsedTime G := gb(Gmat, DegreeLimit => degLim,
                        HardDegreeLimit => degLim,
                        ChangeMatrix => true);
    fn := "scripts/certs_" | name | ".m2out";
    part := fn | ".part";
    if fileExists part then removeFile part;
    fh := openOut part;
    fh << "-- Certificates: b = G * v with G the equation row-matrix." << endl;
    fh << "-- ring: " << toString describe Q2 << endl << endl;
    fh << "Gens = " << toExternalString gensList << endl << endl;
    maxDegs := {};
    for j from 0 to #bQ2-1 do (
        << "  lifting target " << j+1 << "/" << #bQ2 << "..." << flush;
        v := matrix{{bQ2#j}} // G;
        assert(Gmat * v - matrix{{bQ2#j}} == 0); -- direct verification
        << " verified" << endl << flush;
        fh << "-- certificate " << j << endl;
        fh << "b_" << j << " = " << toExternalString (bQ2#j) << endl;
        fh << "v_" << j << " = {";
        md := 0;
        for r from 0 to numrows v-1 do (
            q := v_(r,0);
            if r > 0 then fh << ",";
            fh << toExternalString q;
            if q != 0 then md = max(md, first degree q));
        fh << "}" << endl << endl;
        maxDegs = append(maxDegs, md);
        v = null;);
    close fh;
    moveFile(part, fn);
    << "  all " << #bQ2 << " certificates verified by direct multiplication." << endl;
    << "  saved to " << fn << endl;
    << "  max cofactor degree per certificate: " << maxDegs << endl << flush;
    G = null;
    gbRemove Gmat;
    collectGarbage();
    );

branchChoice = getenv "CERT_BRANCH"
if branchChoice =!= "t4" then doBranch(set {(1,2,3)}, "xy");
if branchChoice =!= "xy" then (
    collectGarbage();
    doBranch(set {(1,1,2),(1,2,3)}, "t4"););
<< "DONE certs" << endl;
