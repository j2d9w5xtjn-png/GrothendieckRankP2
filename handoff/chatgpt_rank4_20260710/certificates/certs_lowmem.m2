-- certs_lowmem.m2
--
-- Low-peak-memory certificate extractor for the eps^3 rank-four identity.
-- It is mathematically stronger than certs.m2: the certificate ideal contains
-- only associativity and Delta-multiplicativity equations (Theorem F / the
-- minassoc computation), not coassociativity or the special-fibre [2]=0
-- equations.  A certificate against this smaller ideal is automatically a
-- certificate against the old larger ideal.
--
-- The truncated coefficient ring is represented directly by triples over Q:
--       a0 + eps*a1 + eps^2*a2  <-->  {a0,a1,a2}.
-- This avoids a second polynomial ring containing eps, repeated reduction
-- modulo eps^3, digit extraction by substitution/division, and the final ring
-- coercion.  Equations are emitted as soon as a coordinate is computed.
--
-- Usage (run the two branches in separate processes):
--   CERT_BRANCH=xy CERT_MODE=build M2 --script scripts/certs_lowmem.m2
--   CERT_BRANCH=t4 CERT_MODE=build M2 --script scripts/certs_lowmem.m2
-- After the build gates agree with minassoc, replace build by cert to run the
-- tracked, hard-degree-limited GB and stream verified certificates to disk.

kk = ZZ/2;

cIx = flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
          for k from 1 to 3 list for d from 0 to 2 list c_(i,j,k,d);
mIx = flatten flatten flatten for i from 1 to 3 list for j from i to 3 list
          for r from 1 to 3 list for d from 1 to 2 list m_(i,j,r,d);
Q = kk[cIx | mIx, MonomialOrder => GRevLex];
use Q;

zR = {0_Q,0_Q,0_Q};
oR = {1_Q,0_Q,0_Q};
addR = (a,b) -> {a#0+b#0, a#1+b#1, a#2+b#2};
mulR = (a,b) -> {
    a#0*b#0,
    a#0*b#1 + a#1*b#0,
    a#0*b#2 + a#1*b#1 + a#2*b#0};
zeroR = a -> a#0 == 0 and a#1 == 0 and a#2 == 0;

ebas = i -> apply(4, k -> if k == i then oR else zR);
idx2 = (a,b) -> 4*a+b;

buildBranch = fibKeys -> (
    Cc := (i,j,k) -> {c_(i,j,k,0),c_(i,j,k,1),c_(i,j,k,2)};
    Mc := (i,j,r) -> (
        ii := min(i,j); jj := max(i,j);
        {if member((ii,jj,r),fibKeys) then 1_Q else 0_Q,
         m_(ii,jj,r,1),m_(ii,jj,r,2)});

    Stab := hashTable flatten for a from 0 to 3 list for b from 0 to 3 list
        (a,b) => (if a == 0 then ebas b else if b == 0 then ebas a
                  else {zR,Mc(a,b,1),Mc(a,b,2),Mc(a,b,3)});
    DEl := for i from 0 to 3 list (
        if i == 0 then apply(16,t -> if t == 0 then oR else zR)
        else (
            v := new MutableList from toList(16:zR);
            v#(idx2(i,0)) = addR(v#(idx2(i,0)),oR);
            v#(idx2(0,i)) = addR(v#(idx2(0,i)),oR);
            for j from 1 to 3 do for k from 1 to 3 do
                v#(idx2(j,k)) = addR(v#(idx2(j,k)),Cc(i,j,k));
            toList v));

    mulA := (u,v) -> (
        out := new MutableList from toList(4:zR);
        for i from 0 to 3 do if not zeroR(u#i) then
        for j from 0 to 3 do if not zeroR(v#j) then (
            Sij := Stab#(i,j);
            for r from 0 to 3 do if not zeroR(Sij#r) then
                out#r = addR(out#r,mulR(mulR(u#i,v#j),Sij#r)));
        toList out);

    gensList := {};
    genLabels := {};
    seen := new MutableHashTable;
    emit := (a,label) -> for d from 0 to 2 do (
        f := a#d;
        if f != 0 and not seen#?f then (
            seen#f = #gensList;
            gensList = append(gensList,f);
            genLabels = append(genLabels,label | ".d" | toString d)));

    -- Associativity, streamed coordinate by coordinate.
    for i from 1 to 3 do for j from 1 to 3 do for k from 1 to 3 do (
        u := mulA(mulA(ebas i,ebas j),ebas k);
        w := mulA(ebas i,mulA(ebas j,ebas k));
        for r from 0 to 3 do emit(addR(u#r,w#r),
            "assoc[" | toString i | "," | toString j | "," |
            toString k | ";" | toString r | "]"));

    DofVec := v -> (
        out := new MutableList from toList(16:zR);
        for r from 0 to 3 do if not zeroR(v#r) then (
            D := DEl#r;
            for t from 0 to 15 do if not zeroR(D#t) then
                out#t = addR(out#t,mulR(v#r,D#t)));
        toList out);
    mulT2 := (u,v) -> (
        out := new MutableList from toList(16:zR);
        for a from 0 to 3 do for b from 0 to 3 do (
            ua := u#(idx2(a,b));
            if not zeroR ua then
            for a2 from 0 to 3 do for b2 from 0 to 3 do (
                vb := v#(idx2(a2,b2));
                if not zeroR vb then (
                    co := mulR(ua,vb);
                    SA := Stab#(a,a2); SB := Stab#(b,b2);
                    for k from 0 to 3 do if not zeroR(SA#k) then
                    for l from 0 to 3 do if not zeroR(SB#l) then
                        out#(idx2(k,l)) = addR(out#(idx2(k,l)),
                            mulR(mulR(co,SA#k),SB#l)))));
        toList out);

    -- Delta multiplicative, streamed coordinate by coordinate.
    for i from 1 to 3 do for j from i to 3 do (
        lhs := DofVec(Stab#(i,j));
        rhs := mulT2(DEl#i,DEl#j);
        for t from 0 to 15 do emit(addR(lhs#t,rhs#t),
            "compat[" | toString i | "," | toString j | ";" |
            toString t | "]"));

    -- phi = mu o Delta and P4 = phi o phi.
    phiL := for i from 0 to 3 list (
        if i == 0 then ebas 0 else (
            D := DEl#i;
            out := new MutableList from toList(4:zR);
            for j from 0 to 3 do for k from 0 to 3 do
                if not zeroR(D#(idx2(j,k))) then (
                    Sjk := Stab#(j,k);
                    for r from 0 to 3 do if not zeroR(Sjk#r) then
                        out#r = addR(out#r,mulR(D#(idx2(j,k)),Sjk#r)));
            toList out));
    for i from 1 to 3 do assert(zeroR((phiL#i)#0));
    P4L := for i from 1 to 3 list (
        p := phiL#i;
        out := new MutableList from toList(4:zR);
        for r from 0 to 3 do if not zeroR(p#r) then (
            ph := phiL#r;
            for t from 0 to 3 do if not zeroR(ph#t) then
                out#t = addR(out#t,mulR(p#r,ph#t)));
        toList out);

    targets := {};
    targetLabels := {};
    seenT := new MutableHashTable;
    for i from 1 to 3 do for r from 0 to 3 do for d from 0 to 2 do (
        b := (P4L#(i-1)#r)#d;
        if b != 0 and not seenT#?b then (
            seenT#b = #targets;
            targets = append(targets,b);
            targetLabels = append(targetLabels,
                "P4[" | toString i | "," | toString r | "].d" | toString d)));
    hashTable{"gens"=>gensList,"genLabels"=>genLabels,
              "targets"=>targets,"targetLabels"=>targetLabels});

branch = getenv "CERT_BRANCH";
if branch === null then branch = "xy";
mode = getenv "CERT_MODE";
if mode === null then mode = "build";
if branch == "xy" then (
    fibKeys = set{(1,2,3)};
    degreeBound = 5;
    expectedGens = 157;
    expectedTargets = 21;
    expectedDegrees = new Tally from {1=>19,2=>69,3=>15,4=>54};
) else if branch == "t4" then (
    fibKeys = set{(1,1,2),(1,2,3)};
    degreeBound = 6;
    expectedGens = 178;
    expectedTargets = 24;
    expectedDegrees = new Tally from {1=>28,2=>57,3=>39,4=>54};
) else error "CERT_BRANCH must be xy or t4";

<< "BUILD low-memory branch " << branch << flush;
elapsedTime data = buildBranch fibKeys;
gensList = data#"gens";
bQ = data#"targets";
degTally = tally apply(gensList,g -> first degree g);
<< "\nbranch " << branch << ": " << #gensList << " equations, "
   << #bQ << " P4 coefficients\n";
<< "generator degrees: " << degTally << endl << flush;
assert(#gensList == expectedGens);
assert(#bQ == expectedTargets);
assert(degTally == expectedDegrees);

if mode == "build" then (
    if getenv "CERT_PRINT_TARGETS" == "1" then
        << "TARGET LABELS " << apply(toList(0..#bQ-1),
            i -> (i,(data#"targetLabels")#i)) << endl;
    << "BUILD GATES PASS " << branch << endl << flush;
) else if mode == "scan" then (
    GmatS := matrix{gensList};
    << "TARGET LABELS " << apply(toList(0..#bQ-1),
        i -> (i,(data#"targetLabels")#i)) << endl << flush;
    for d in toList(2..degreeBound) do (
        GS := gb(GmatS,DegreeLimit=>d,HardDegreeLimit=>d);
        open := select(toList(0..#bQ-1),i -> matrix{{bQ#i}} % GS != 0);
        << "SCAN " << branch << " degree " << d << " open=" << open
           << endl << flush;
        GS = null;
        gbRemove GmatS;
        collectGarbage());
) else if mode == "check" then (
    Gmat0 := matrix{gensList};
    << "ORDINARY GB CHECK branch " << branch << " hard degree "
       << degreeBound << flush;
    elapsedTime G0 := gb(Gmat0,DegreeLimit=>degreeBound,
        HardDegreeLimit=>degreeBound);
    assert(1_Q % G0 != 0);
    for b in bQ do assert(matrix{{b}} % G0 == 0);
    << "\nORDINARY MEMBERSHIP GATE PASS " << branch << endl << flush;
) else if mode == "certpruned5" then (
    -- Harvest all 24 t4 targets at hard degree 5 after exact linear
    -- elimination and deduplication.  (Before this pruning, two appeared to
    -- require degree 6.)
    assert(branch == "t4");
    runBound := 5;
    linPos := select(toList(0..#gensList-1),
        i -> first degree(gensList#i) == 1);
    nonPos := select(toList(0..#gensList-1),
        i -> not member(i,linPos));
    linList := apply(linPos,i -> gensList#i);
    Lmat := matrix{linList};
    T := Q/(ideal linList);
    S := prune T;
    rho := T.minimalPresentationMap * map(T,Q);
    liftS := q -> lift(T.minimalPresentationMapInv(q),Q);
    assert all(linList,g -> rho(g) == 0);

    -- Quotienting may create new duplicate equations.  Keep the first
    -- original position for each nonzero reduced polynomial.
    pairs0 := select(apply(nonPos,i -> {i,rho(gensList#i)}),p -> p#1 != 0);
    seenRed := new MutableHashTable;
    pairs := {};
    for p in pairs0 do if not seenRed#?(p#1) then (
        seenRed#(p#1) = true;
        pairs = append(pairs,p));
    redPos := apply(pairs,p -> p#0);
    redList := apply(pairs,p -> p#1);
    RedMat := matrix{redList};
    << "PRUNED5 branch t4: " << #linPos << " linear equations; "
       << numgens Q << " -> " << numgens S << " variables; "
       << #pairs0 << " nonzero / " << #redList
       << " distinct remaining equations" << endl << flush;

    elapsedTime G := gb(RedMat,DegreeLimit=>runBound,
        HardDegreeLimit=>runBound,ChangeMatrix=>true);
    assert(1_S % G != 0);
    easyPos := select(toList(0..#bQ-1),i -> matrix{{rho(bQ#i)}} % G == 0);
    hardPos := select(toList(0..#bQ-1),i -> not member(i,easyPos));
    << "PRUNED5 certified target indices=" << easyPos
       << " hard target indices=" << hardPos << endl << flush;
    assert(#easyPos == 24);
    assert(hardPos == {});
    GL := gb(Lmat,DegreeLimit=>1,HardDegreeLimit=>1,ChangeMatrix=>true);

    fn := "scripts/certs_lowmem_pruned_t4_d5.m2out";
    part := fn | ".part";
    if fileExists part then removeFile part;
    fh := openOut part;
    fh << "-- All 24 direct degree-at-most-5 t4 certificates b = Gens * v." << endl;
    fh << "-- Gens are associativity + Delta-multiplicativity only." << endl;
    fh << "-- Linear elimination and deduplication lower the old apparent D6 pair to D5." << endl;
    fh << "-- ring: " << toString describe Q << endl << endl;
    fh << "CertifiedTargetIndices = " << toExternalString easyPos << endl;
    fh << "HardTargetIndices = " << toExternalString hardPos << endl << endl;
    fh << "Gens = {";
    for i from 0 to #gensList-1 do (
        if i > 0 then fh << ",";
        fh << toExternalString(gensList#i));
    fh << "}" << endl << endl;

    maxDegrees := {};
    for i in easyPos do (
        << "PRUNED5 LIFT t4 target index " << i << flush;
        b := bQ#i;
        qS := matrix{{rho(b)}} // G;
        assert(numRows qS == #redList);
        qQ := apply(#redList,j -> liftS(qS_(j,0)));
        residual := b + sum(0..#redList-1,
            j -> qQ#j * gensList#(redPos#j));
        assert(rho(residual) == 0);
        qL := matrix{{residual}} // GL;
        assert(numRows qL == #linList);
        assert(residual == sum(0..#linList-1,
            j -> qL_(j,0)*linList#j));
        vv := new MutableList from toList(#gensList:0_Q);
        for j from 0 to #linPos-1 do vv#(linPos#j) = qL_(j,0);
        for j from 0 to #redPos-1 do vv#(redPos#j) = qQ#j;
        v := toList vv;
        assert(b == sum(0..#gensList-1,j -> gensList#j*v#j));
        fh << "-- certificate target index " << i << "  "
           << (data#"targetLabels")#i << endl;
        fh << "b_" << i << " = " << toExternalString b << endl;
        fh << "v_" << i << " = {";
        md := 0;
        for j from 0 to #v-1 do (
            if j > 0 then fh << ",";
            q := v#j;
            fh << toExternalString q;
            if q != 0 then md = max(md,first degree q));
        fh << "}" << endl << endl;
        maxDegrees = append(maxDegrees,(i,md));
        qS = null; qQ = null; residual = null; qL = null; vv = null; v = null;
        << " VERIFIED" << endl << flush;);
    close fh;
    moveFile(part,fn);
    << "ALL 24 PRUNED D5 DIRECT CERTIFICATES VERIFIED t4" << endl;
    << "max cofactor degrees by target: " << maxDegrees << endl;
    << "saved " << fn << endl << flush;
) else if member(mode,{"bankboostscan","bankboost"}) then (
    error "bank boost retired: pruned/deduplicated t4 closes all 24 targets at degree 5";
    -- Add the 22 already-certified P4 coefficients as redundant generators.
    -- In bankboost mode, substitute their exact original-ring certificates
    -- into the two remaining lifts before the final direct verification.
    assert(branch == "t4");
    linPos := select(toList(0..#gensList-1),
        i -> first degree(gensList#i) == 1);
    nonPos := select(toList(0..#gensList-1),
        i -> not member(i,linPos));
    linList := apply(linPos,i -> gensList#i);
    Lmat := matrix{linList};
    T := Q/(ideal linList);
    S := prune T;
    rho := T.minimalPresentationMap * map(T,Q);
    liftS := q -> lift(T.minimalPresentationMapInv(q),Q);
    assert all(linList,g -> rho(g) == 0);
    pairs0 := select(apply(nonPos,i -> {i,rho(gensList#i)}),p -> p#1 != 0);
    seenRed := new MutableHashTable;
    pairs := {};
    for p in pairs0 do if not seenRed#?(p#1) then (
        seenRed#(p#1) = true;
        pairs = append(pairs,p));
    redPos := apply(pairs,p -> p#0);
    redList := apply(pairs,p -> p#1);

    easyPos := delete(7,delete(4,toList(0..#bQ-1)));
    hardPos := {4,7};
    bankFile := "scripts/certs_lowmem_pruned_t4_d5.m2out";
    assert(fileExists bankFile);
    savedGens := gensList;
    use Q;
    load bankFile;
    assert(Gens == savedGens);
    assert(CertifiedTargetIndices == easyPos);
    assert(HardTargetIndices == hardPos);
    easyCerts := hashTable apply(easyPos,i -> (
        assert(b_(i) == bQ#i);
        assert(#v_(i) == #gensList);
        assert(bQ#i == sum(0..#gensList-1,j -> gensList#j*(v_(i))#j));
        i => v_(i)));
    use S;

    easyRed := apply(easyPos,i -> rho(bQ#i));
    -- Put the banked targets first so they become reducers immediately.
    AugList := easyRed | redList;
    AugMat := matrix{AugList};
    << "BANK BOOST t4: " << #easyPos << " certified reducers + "
       << #redList << " reduced original equations in " << numgens S
       << " variables" << endl << flush;

    if mode == "bankboostscan" then (
        for d in toList(2..6) do (
            elapsedTime GS := gb(AugMat,DegreeLimit=>d,HardDegreeLimit=>d);
            open := select(hardPos,i -> matrix{{rho(bQ#i)}} % GS != 0);
            << "BANK BOOST SCAN degree " << d << " hard-open=" << open
               << endl << flush;
            GS = null;
            gbRemove AugMat;);
        << "BANK BOOST SCAN COMPLETE t4" << endl << flush;
    ) else (
        boostString := getenv "CERT_BOOST_DEGREE";
        boostBound := if boostString === null then 5 else value boostString;
        assert(member(boostBound,toList(2..6)));
        elapsedTime G := gb(AugMat,DegreeLimit=>boostBound,
            HardDegreeLimit=>boostBound,ChangeMatrix=>true);
        for i in hardPos do assert(matrix{{rho(bQ#i)}} % G == 0);
        GL := gb(Lmat,DegreeLimit=>1,HardDegreeLimit=>1,ChangeMatrix=>true);
        << "BANK BOOST MEMBERSHIP GATE PASS t4 degree " << boostBound
           << endl << flush;

        fn := "scripts/certs_lowmem_banked_t4_hard.m2out";
        part := fn | ".part";
        if fileExists part then removeFile part;
        fh := openOut part;
        fh << "-- Two hard t4 certificates reconstructed against original Gens." << endl;
        fh << "-- The 22 temporary banked reducers have been substituted out." << endl;
        fh << "-- ring: " << toString describe Q << endl << endl;
        fh << "CertifiedTargetIndices = " << toExternalString hardPos << endl;
        fh << "BankedTargetIndices = " << toExternalString easyPos << endl << endl;
        fh << "Gens = {";
        for i from 0 to #gensList-1 do (
            if i > 0 then fh << ",";
            fh << toExternalString(gensList#i));
        fh << "}" << endl << endl;

        for i in hardPos do (
            << "BANKED LIFT t4 hard target index " << i << flush;
            b := bQ#i;
            qS := matrix{{rho(b)}} // G;
            assert(numRows qS == #AugList);
            vv := new MutableList from toList(#gensList:0_Q);
            -- Substitute each banked target's original 178-entry certificate.
            for k from 0 to #easyPos-1 do (
                co := liftS(qS_(k,0));
                ev := easyCerts#(easyPos#k);
                if co != 0 then for j from 0 to #gensList-1 do
                    if ev#j != 0 then vv#j = vv#j + co*ev#j;);
            -- Lift the coefficients on the reduced original equations.
            for k from 0 to #redPos-1 do (
                co := liftS(qS_(#easyPos+k,0));
                vv#(redPos#k) = vv#(redPos#k) + co;);
            residual := b + sum(0..#gensList-1,
                j -> gensList#j*vv#j);
            assert(rho(residual) == 0);
            qL := matrix{{residual}} // GL;
            assert(residual == sum(0..#linList-1,
                j -> qL_(j,0)*linList#j));
            for j from 0 to #linPos-1 do
                vv#(linPos#j) = vv#(linPos#j) + qL_(j,0);
            v := toList vv;
            assert(b == sum(0..#gensList-1,j -> gensList#j*v#j));
            fh << "-- certificate target index " << i << "  "
               << (data#"targetLabels")#i << endl;
            fh << "b_" << i << " = " << toExternalString b << endl;
            fh << "v_" << i << " = {";
            for j from 0 to #v-1 do (
                if j > 0 then fh << ",";
                fh << toExternalString(v#j));
            fh << "}" << endl << endl;
            qS = null; vv = null; residual = null; qL = null; v = null;
            << " VERIFIED AGAINST ORIGINAL 178 GENS" << endl << flush;);
        close fh;
        moveFile(part,fn);
        << "ALL 2 BANKED HARD DIRECT CERTIFICATES VERIFIED t4" << endl;
        << "saved " << fn << endl << flush;);
) else if mode == "certpruned" then (
    -- Eliminate the degree-one axioms exactly before the expensive tracked GB.
    -- Coefficients are reconstructed and verified back in the original ring Q.
    linPos := select(toList(0..#gensList-1),
        i -> first degree(gensList#i) == 1);
    nonPos := select(toList(0..#gensList-1),
        i -> not member(i,linPos));
    linList := apply(linPos,i -> gensList#i);
    Lmat := matrix{linList};
    T := Q/(ideal linList);
    S := prune T;
    rho := T.minimalPresentationMap * map(T,Q);
    liftS := q -> lift(T.minimalPresentationMapInv(q),Q);
    assert all(linList,g -> rho(g) == 0);
    pairs := select(apply(nonPos,i -> {i,rho(gensList#i)}),p -> p#1 != 0);
    redPos := apply(pairs,p -> p#0);
    redList := apply(pairs,p -> p#1);
    RedMat := matrix{redList};
    << "PRUNED branch " << branch << ": " << #linPos
       << " linear equations; " << numgens Q << " -> " << numgens S
       << " variables; " << #redList << " remaining equations" << endl << flush;

    G := gb(RedMat,DegreeLimit=>degreeBound,
        HardDegreeLimit=>degreeBound,ChangeMatrix=>true);
    GL := gb(Lmat,DegreeLimit=>1,HardDegreeLimit=>1,ChangeMatrix=>true);
    assert(1_S % G != 0);
    for b in bQ do assert(matrix{{rho(b)}} % G == 0);
    << "PRUNED GB MEMBERSHIP GATE PASS " << branch << endl << flush;

    fn := "scripts/certs_lowmem_pruned_" | branch | ".m2out";
    part := fn | ".part";
    if fileExists part then removeFile part;
    fh := openOut part;
    fh << "-- Direct certificates b = Gens * v, reconstructed in Q." << endl;
    fh << "-- Gens are associativity + Delta-multiplicativity only." << endl;
    fh << "-- ring: " << toString describe Q << endl << endl;
    fh << "Gens = {";
    for i from 0 to #gensList-1 do (
        if i > 0 then fh << ",";
        fh << toExternalString(gensList#i));
    fh << "}" << endl << endl;
    maxDegrees := {};
    for i from 0 to #bQ-1 do (
        << "PRUNED LIFT " << branch << " target " << i+1 << "/" << #bQ << flush;
        b := bQ#i;
        qS := matrix{{rho(b)}} // G;
        assert(numRows qS == #redList);
        -- Lift the reduced cofactors and compute the residual in Q explicitly,
        -- avoiding loss of graded-map metadata when rebuilding a matrix.
        qQ := apply(#redList,j -> liftS(qS_(j,0)));
        residual := b + sum(0..#redList-1,j -> qQ#j * gensList#(redPos#j));
        assert(rho(residual) == 0);
        qL := matrix{{residual}} // GL;
        assert(numRows qL == #linList);
        assert(residual == sum(0..#linList-1,j -> qL_(j,0)*linList#j));
        vv := new MutableList from toList(#gensList:0_Q);
        for j from 0 to #linPos-1 do vv#(linPos#j) = qL_(j,0);
        for j from 0 to #redPos-1 do vv#(redPos#j) = qQ#j;
        v := toList vv;
        assert(b == sum(0..#gensList-1,j -> gensList#j*v#j));
        fh << "-- certificate " << i << "  " << (data#"targetLabels")#i << endl;
        fh << "b_" << i << " = " << toExternalString b << endl;
        fh << "v_" << i << " = {";
        md := 0;
        for j from 0 to #v-1 do (
            if j > 0 then fh << ",";
            q := v#j;
            fh << toExternalString q;
            if q != 0 then md = max(md,first degree q));
        fh << "}" << endl << endl;
        maxDegrees = append(maxDegrees,md);
        qS = null; qQ = null; residual = null; qL = null; vv = null; v = null;
        << " VERIFIED" << endl << flush;);
    close fh;
    moveFile(part,fn);
    << "ALL PRUNED DIRECT CERTIFICATES VERIFIED " << branch << endl;
    << "max cofactor degrees: " << maxDegrees << endl;
    << "saved " << fn << endl << flush;
) else if mode == "cert" then (
    Gmat := matrix{gensList};
    << "GB branch " << branch << " hard degree " << degreeBound << flush;
    elapsedTime G := gb(Gmat,DegreeLimit=>degreeBound,
        HardDegreeLimit=>degreeBound,ChangeMatrix=>true);
    assert(1_Q % G != 0);
    for b in bQ do assert(matrix{{b}} % G == 0);
    << "\nGB MEMBERSHIP GATE PASS " << branch << endl << flush;

    fn := "scripts/certs_lowmem_" | branch | ".m2out";
    part := fn | ".part";
    if fileExists part then removeFile part;
    fh := openOut part;
    fh << "-- Direct certificates b = Gens * v." << endl;
    fh << "-- Gens are associativity + Delta-multiplicativity only." << endl;
    fh << "-- ring: " << toString describe Q << endl << endl;
    fh << "Gens = {";
    for i from 0 to #gensList-1 do (
        if i > 0 then fh << ",";
        fh << toExternalString(gensList#i));
    fh << "}" << endl << endl;
    maxDegrees := {};
    for i from 0 to #bQ-1 do (
        << "LIFT " << branch << " target " << i+1 << "/" << #bQ << flush;
        b := bQ#i;
        v := matrix{{b}} // G;
        assert(numRows v == #gensList);
        assert(Gmat*v == matrix{{b}});
        fh << "-- certificate " << i << "  " << (data#"targetLabels")#i << endl;
        fh << "b_" << i << " = " << toExternalString b << endl;
        fh << "v_" << i << " = {";
        md := 0;
        for j from 0 to numRows v-1 do (
            if j > 0 then fh << ",";
            q := v_(j,0);
            fh << toExternalString q;
            if q != 0 then md = max(md,first degree q));
        fh << "}" << endl << endl;
        maxDegrees = append(maxDegrees,md);
        v = null;
        << " VERIFIED" << endl << flush;);
    close fh;
    moveFile(part,fn);
    << "ALL DIRECT CERTIFICATES VERIFIED " << branch << endl;
    << "max cofactor degrees: " << maxDegrees << endl;
    << "saved " << fn << endl << flush;
    -- Each branch runs in a fresh process, so explicit final GC is wasteful:
    -- on macOS it caused a brief post-success RSS/CPU spike before exit.
) else error "CERT_MODE must be build, scan, check, certpruned5, bankboostscan, bankboost, certpruned, or cert";
