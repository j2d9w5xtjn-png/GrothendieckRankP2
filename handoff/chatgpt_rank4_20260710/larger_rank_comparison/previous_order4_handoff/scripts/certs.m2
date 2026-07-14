-- certs.m2
-- Extract and verify explicit membership certificates for the eps^3 theorem:
-- each coefficient b of [4]^# is written as b = sum_i q_i * g_i with g_i the
-- Hopf/fiber equations, and the identity is re-verified by direct matrix
-- multiplication (no Groebner reduction involved in the verification step).
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
    P4L := for i from 1 to 3 list (
        p := phiL#i;
        out := new MutableList from toList(4:0_Q);
        for r from 0 to 3 do if p#r != 0 then (
            ph := phiL#r;
            for t from 0 to 3 do if ph#t != 0 then
                out#t = out#t + p#r * ph#t);
        apply(toList out, red));
    fiber2E := flatten for i from 1 to 3 list
        for r from 1 to 3 list (digitsQ((phiL#i)#r))#0;
    vecs := assocV | compatV | coassocV;
    hopf := unique select(flatten apply(vecs, v -> flatten apply(v, digitsQ)), f -> f != 0);
    f2 := unique select(fiber2E, f -> f != 0);
    bL := unique select(flatten apply(P4L, v -> flatten apply(v, digitsQ)), f -> f != 0);
    Q2 := kk[ cIx | mIx ];
    toQ2 := map(Q2, Q, {0_Q2} | (gens Q2));
    gensList := apply(unique(hopf | f2), g -> toQ2 g);
    Gmat := matrix{gensList};
    bQ2 := apply(bL, g -> toQ2 g);
    << "branch " << name << ": " << #gensList << " equations, "
      << #bQ2 << " P4 coefficients" << endl;
    -- degree-limited GB with change matrix; avoid ever computing the full GB
    elapsedTime G := gb(ideal gensList, DegreeLimit => 6, ChangeMatrix => true);
    gbMat := gens G;
    chg := getChangeMatrix G;          -- gbMat == Gmat * chg
    assert(Gmat * chg - gbMat == 0);
    F := forceGB gbMat;
    certs := for b in bQ2 list (
        u := matrix{{b}} // F;         -- gbMat * u + (b % F) == b, b % F == 0
        assert(matrix{{b}} % F == 0);
        v := chg * u;
        assert(Gmat * v - matrix{{b}} == 0);   -- direct verification vs originals
        (b, v));
    << "  all " << #certs << " certificates verified by direct multiplication." << endl;
    fn := "scripts/certs_" | name | ".m2out";
    fh := openOut fn;
    fh << "-- Certificates: b = G * v with G the equation row-matrix." << endl;
    fh << "-- ring: " << toString describe Q2 << endl << endl;
    fh << "Gens = " << toExternalString gensList << endl << endl;
    for i from 0 to #certs-1 do (
        (b, v) := certs#i;
        fh << "-- certificate " << i << endl;
        fh << "b_" << i << " = " << toExternalString b << endl;
        fh << "v_" << i << " = " << toExternalString (flatten entries v) << endl << endl);
    close fh;
    << "  saved to " << fn << endl;
    -- degree statistics of the certificates
    << "  max cofactor degree per certificate: "
      << apply(certs, cv -> max apply(flatten entries cv#1, q -> if q == 0 then 0 else first degree q)) << endl;
    );

doBranch(set {(1,2,3)}, "xy")
doBranch(set {(1,1,2),(1,2,3)}, "t4")
<< "DONE certs" << endl;
