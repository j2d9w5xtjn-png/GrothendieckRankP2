-- search_deeper.m2
-- Equal-characteristic searches over R = k[eps]/(eps^NN) for NN = 3,4,5,
-- with and without the "special fiber killed by 2" condition.
-- Same conventions as gensearch.m2 (see that file for documentation).

kk = ZZ/2

runAll = (NN, useFiber2, fibKeys, name) -> (
    << endl << "############################################################" << endl;
    << "## " << name << "   (eps^" << NN << " = 0, fiber2 condition: " << useFiber2 << ")" << endl;
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
    f2  := unique select(fiber2E, f -> f != 0);
    bL  := unique select(flatten apply(P4L, v -> flatten apply(v, digitsQ)), f -> f != 0);
    Q2 := kk[ cIx | mIx ];
    toQ2 := map(Q2, Q, {0_Q2} | (gens Q2));
    gensJ := if useFiber2 then unique(hopf | f2) else hopf;
    J := ideal apply(gensJ, g -> toQ2 g);
    bQ2 := apply(bL, g -> toQ2 g);
    << "#vars: " << numgens Q2 << "  #eqs: " << numgens J
      << "  #P4 coefficients: " << #bQ2 << endl;
    done := false;
    for d in {2,3,4,5,6,8,10} do (
        if done then break;
        << "-- gb DegreeLimit " << d << ": " << flush;
        elapsedTime G := gb(J, DegreeLimit => d);
        rems := apply(bQ2, b -> b % G);
        nz := select(rems, r -> r != 0);
        << "   nonzero remainders: " << #nz << " / " << #bQ2
          << "   (1 in J? " << (1_Q2 % G == 0) << ")" << endl;
        if #nz == 0 then (
            << "   ==> ALL P4 coefficients in J (ideal membership certificate)." << endl;
            done = true));
    if not done then (
        << "-- full gb: " << flush;
        elapsedTime G := gb J;
        rems := apply(bQ2, b -> b % G);
        nz := select(rems, r -> r != 0);
        << "   nonzero remainders after full gb: " << #nz << " / " << #bQ2
          << "   (1 in J? " << (1_Q2 % G == 0) << ")" << endl;
        if #nz == 0 then << "   ==> ALL P4 coefficients in J." << endl
        else (
            << "   NOT all in J; testing radical membership (Frobenius powers)..." << endl;
            for b in bQ2 do if b % G != 0 then (
                pow := b; kq := 0; okp := false;
                while kq < 6 do (pow = pow^2; kq = kq+1;
                    if pow % G == 0 then (okp = true; break));
                << "   nonmember b, b^(2^k) in J for k = "
                  << (if okp then toString kq else "NO(<=64th power)") << endl)));
    );

fib1 = set { (1,2,3) };              -- fiber k[x,y]/(x^2,y^2)
fib2t = set { (1,1,2), (1,2,3) };    -- fiber k[t]/(t^4)

-- eps^4 and eps^5 with the fiber condition (highest priority)
runAll(4, true, fib1,  "fiber k[x,y]/(x^2,y^2), eps^4")
runAll(4, true, fib2t, "fiber k[t]/(t^4), eps^4")
runAll(5, true, fib1,  "fiber k[x,y]/(x^2,y^2), eps^5")
runAll(5, true, fib2t, "fiber k[t]/(t^4), eps^5")
<< endl << "DONE search_eps45" << endl;
