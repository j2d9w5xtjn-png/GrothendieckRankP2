-- universal_local_rank4_t4_monogenic.m2
--
-- Exact mixed-characteristic universal chart for the two geometric t4
-- local--local rank-four fibers.  This is an experimental, substantially
-- smaller companion to universal_local_rank4.m2.
--
-- If the closed fiber is k[t]/(t^4), any lift t of the special generator has
-- (1,t,t^2,t^3) as a basis by Nakayama.  Hence the augmented algebra has the
-- unique form
--
--     A = R[t]/(t^4-a1*t-a2*t^2-a3*t^3).
--
-- A coproduct is determined by Delta(t).  It is a well-defined algebra map
-- precisely when the displayed quartic relation is preserved.  Once this is
-- imposed, coassociativity and equality of power maps need only be checked on
-- t.  Thus the chart has 3 multiplication variables, 9 reduced coproduct
-- variables, 9 relation-compatibility equations, 27 coassociativity
-- equations, and 3 [4]^# targets.
--
-- The c1 parameter in the older four-pin t4 list is gauge: replacing t by
-- t+c1*t^3 removes it.  The two geometric fibers retained here are c4=0,1.
--
-- Environment:
--   RANK4_T4_C4          0 or 1 (default 0)
--   RANK4_TARGET         target coordinate 0..2 (default 0)
--   RANK4_GENERATE_ONLY  1 to stop before the exact syzygy (default 0)

kk = ZZ/2;

envMissing = s -> s === null or (class s === String and #s == 0);

c4String = getenv "RANK4_T4_C4";
c4bit = if envMissing c4String then 0 else value c4String;
if c4bit < 0 or c4bit > 1 then error "RANK4_T4_C4 must be 0 or 1";

targetString = getenv "RANK4_TARGET";
targetIndex = if envMissing targetString then 0 else value targetString;
if targetIndex < 0 or targetIndex > 2 then error "RANK4_TARGET must lie in 0..2";

generateString = getenv "RANK4_GENERATE_ONLY";
generateOnly = not envMissing generateString and generateString == "1";

nAlg = 3;
nCop = 9;
nVars = nAlg + nCop;
MM = monoid[Variables => nVars, MonomialOrder => GRevLex];
Q = ZZ MM;

a1 = Q_0;
a2 = Q_1;
a3 = Q_2;
cVar = (j,k) -> Q_(nAlg + 3*(j-1) + k-1);

ebas = i -> apply(4, r -> if r == i then 1_Q else 0_Q);
idx2 = (a,b) -> 4*a+b;
idx3 = (a,b,c) -> 16*a+4*b+c;

-- Coordinates of t^0,...,t^6 in the monogenic basis.  Products of basis
-- elements have degree at most six.
p4 = {0_Q,a1,a2,a3};
p5 = {0_Q,a1*a3,a1+a2*a3,a2+a3^2};
p6 = {
    0_Q,
    a1*(a2+a3^2),
    a1*a3+a2^2+a2*a3^2,
    a1+2*a2*a3+a3^3
    };
powT = {ebas 0,ebas 1,ebas 2,ebas 3,p4,p5,p6};

Stab = hashTable flatten for i from 0 to 3 list for j from 0 to 3 list
    (i,j) => powT#(i+j);

mulA = (u,v) -> (
    out := new MutableList from toList(4:0_Q);
    for i from 0 to 3 do if u#i != 0 then
        for j from 0 to 3 do if v#j != 0 then (
            sij := Stab#(i,j);
            for r from 0 to 3 do if sij#r != 0 then
                out#r = out#r + u#i*v#j*sij#r;
            );
    toList out
    );

-- Independent table gate: the displayed reductions of t^4,t^5,t^6 really
-- give an associative multiplication on the four-element basis.
assocCheckRaw = flatten flatten flatten for i from 0 to 3 list
    for j from 0 to 3 list for k from 0 to 3 list (
        left := mulA(Stab#(i,j),ebas k);
        right := mulA(ebas i,Stab#(j,k));
        for r from 0 to 3 list left#r-right#r
        );
badAssocTable = select(assocCheckRaw,f -> f != 0);

mulT2 = (u,v) -> (
    out := new MutableList from toList(16:0_Q);
    for i from 0 to 3 do for j from 0 to 3 do (
        uv := u#(idx2(i,j));
        if uv != 0 then for ii from 0 to 3 do for jj from 0 to 3 do (
            vv := v#(idx2(ii,jj));
            if vv != 0 then (
                si := Stab#(i,ii);
                sj := Stab#(j,jj);
                for r from 0 to 3 do if si#r != 0 then
                    for s from 0 to 3 do if sj#s != 0 then
                        out#(idx2(r,s)) = out#(idx2(r,s))
                            + uv*vv*si#r*sj#s;
                );
            );
        );
    toList out
    );

deltaTMutable = new MutableList from toList(16:0_Q);
deltaTMutable#(idx2(1,0)) = 1_Q;
deltaTMutable#(idx2(0,1)) = 1_Q;
for j from 1 to 3 do for k from 1 to 3 do (
    deltaTMutable#(idx2(j,k)) = cVar(j,k)
        + (if c4bit == 1 and (j,k) == (2,2) then 1_Q else 0_Q);
    );
deltaT = toList deltaTMutable;

deltaT2 = mulT2(deltaT,deltaT);
deltaT3 = mulT2(deltaT2,deltaT);
deltaT4 = mulT2(deltaT3,deltaT);
DEl = {
    apply(16, i -> if i == 0 then 1_Q else 0_Q),
    deltaT,
    deltaT2,
    deltaT3
    };

-- Delta respects the unique algebra relation.  Counit makes all coordinates
-- with a zero leg automatic, so the reduced 3x3 block is sufficient.
compatVec = apply(16, i -> deltaT4#i-a1*deltaT#i-a2*deltaT2#i-a3*deltaT3#i);
compatRaw = flatten for r from 1 to 3 list for s from 1 to 3 list
    compatVec#(idx2(r,s));
badCompatZeroLeg = select(toList(0..15),i -> i//4 == 0 or i % 4 == 0);
badCompatZeroLeg = select(apply(badCompatZeroLeg,i -> compatVec#i),f -> f != 0);

-- Coassociativity on the single algebra generator t.
coassocLeft = new MutableList from toList(64:0_Q);
coassocRight = new MutableList from toList(64:0_Q);
for r from 0 to 3 do for s from 0 to 3 do (
    u := deltaT#(idx2(r,s));
    if u != 0 then (
        dr := DEl#r;
        for a from 0 to 3 do for b from 0 to 3 do
            if dr#(idx2(a,b)) != 0 then
                coassocLeft#(idx3(a,b,s)) = coassocLeft#(idx3(a,b,s))
                    + u*dr#(idx2(a,b));
        ds := DEl#s;
        for b from 0 to 3 do for c from 0 to 3 do
            if ds#(idx2(b,c)) != 0 then
                coassocRight#(idx3(r,b,c)) = coassocRight#(idx3(r,b,c))
                    + u*ds#(idx2(b,c));
        );
    );
coassocRaw = flatten flatten for a from 1 to 3 list for b from 1 to 3 list
    for c from 1 to 3 list
        coassocLeft#(idx3(a,b,c))-coassocRight#(idx3(a,b,c));
coassocFull = apply(64,i -> coassocLeft#i-coassocRight#i);
zeroLegIndices = select(toList(0..63),i -> i//16 == 0
    or (i//4) % 4 == 0 or i % 4 == 0);
badCoassocZeroLeg = select(apply(zeroLegIndices,i -> coassocFull#i),f -> f != 0);

-- [2]^# on the basis, followed by a second application on t.  Once the
-- compatibility equations hold, [2]^# is an algebra map, but using all four
-- basis images keeps this formula purely polynomial before quotienting.
phiBasis = apply(DEl, di -> (
    out := new MutableList from toList(4:0_Q);
    for j from 0 to 3 do for k from 0 to 3 do
        if di#(idx2(j,k)) != 0 then (
            sjk := Stab#(j,k);
            for r from 0 to 3 do if sjk#r != 0 then
                out#r = out#r + di#(idx2(j,k))*sjk#r;
            );
    toList out
    ));

p4t = new MutableList from toList(4:0_Q);
for r from 0 to 3 do if (phiBasis#1)#r != 0 then
    for s from 0 to 3 do if (phiBasis#r)#s != 0 then
        p4t#s = p4t#s + (phiBasis#1)#r*(phiBasis#r)#s;
targets = (toList p4t)_{1..3};

compatEqs = unique select(compatRaw, f -> f != 0);
coassocEqs = unique select(coassocRaw, f -> f != 0);
eqs = unique (compatEqs | coassocEqs);

qgens = toList gens Q;
originQ = f -> sub(f,apply(qgens,x -> x => 0_Q));
originCoefficient = f -> lift(originQ f,ZZ);
closedMod2 = f -> promote(originCoefficient f,kk);
halfConstantMod2 = f -> promote((originCoefficient f)//2,kk);

badEqConstants = select(eqs,f -> closedMod2 f != 0);
badTargetConstants = select(targets,f -> closedMod2 f != 0);
badFiberSquare = select((phiBasis#1)_{1..3},f -> closedMod2 f != 0);
badTargetQ2Constants = select(targets,f -> promote(originCoefficient f,ZZ/4) != 0);

jacobianAtClosedPoint = fs -> matrix apply(fs,f ->
    {halfConstantMod2 f} | apply(qgens,x -> closedMod2 diff(x,f)));
eqJacobian = jacobianAtClosedPoint eqs;
targetJacobian = jacobianAtClosedPoint targets;
tangentRank = rank eqJacobian;
tangentDimension = nVars+1-tangentRank;
targetLinearRank = rank targetJacobian;

<< "############################################################" << endl;
<< "## universal monogenic t4 c4=" << c4bit << " coefficient_mode=ZZ_(2)" << endl;
<< "## variables=" << nVars
   << " category_unique=" << toString{#compatEqs,#coassocEqs}
   << " unique_nonzero_equations=" << #eqs
   << " targets=" << #targets << endl;
<< "TANGENT rank=" << tangentRank << " dimension=" << tangentDimension
   << " target_linear_rank=" << targetLinearRank << endl;
<< "GATE pinned equations vanish at origin: "
   << (if #badEqConstants == 0 then "OK" else "FAILED") << endl;
<< "GATE monogenic multiplication table associative: "
   << (if #badAssocTable == 0 then "OK" else "FAILED") << endl;
<< "GATE omitted compatibility zero-leg coordinates automatic: "
   << (if #badCompatZeroLeg == 0 then "OK" else "FAILED") << endl;
<< "GATE omitted coassociativity zero-leg coordinates automatic: "
   << (if #badCoassocZeroLeg == 0 then "OK" else "FAILED") << endl;
<< "GATE pinned fiber killed by 2: "
   << (if #badFiberSquare == 0 then "OK" else "FAILED") << endl;
<< "GATE P4 targets vanish at origin: "
   << (if #badTargetConstants == 0 then "OK" else "FAILED") << endl;
<< "GATE P4 has local order at least two: "
   << (if targetLinearRank == 0 then "OK" else "FAILED") << endl;
<< "GATE P4 constants divisible by four: "
   << (if #badTargetQ2Constants == 0 then "OK" else "FAILED") << endl;

if #badEqConstants != 0 or #badAssocTable != 0
    or #badCompatZeroLeg != 0 or #badCoassocZeroLeg != 0
    or #badFiberSquare != 0
    or #badTargetConstants != 0 or #badTargetQ2Constants != 0
    or targetLinearRank != 0
then error "monogenic t4 construction gate failed";

-- Tiny exact API gate before the large computation.
toyX = Q_0;
toyY = Q_1;
toyGen = (1_Q+toyX*toyY)*(2_Q+toyX*toyY);
toyTarget = (2_Q+toyX*toyY)^2;
toyRow = matrix{{toyTarget,toyGen}};
toyZ = syz toyRow;
assert(toyRow*toyZ == 0);
toyCols = numgens source toyZ;
toyWitnesses = select(toList(0..toyCols-1),
    j -> closedMod2(toyZ_(0,j)) != 0);
assert(#toyWitnesses > 0);
<< "GATE exact unit-cofactor syzygy API: OK" << endl;

if generateOnly then (
    << "GENERATE_ONLY complete; no Groebner basis launched" << endl;
    exit 0;
    );

<< "-- exact global syzygy for local target=" << targetIndex << ": " << flush;
globalRow = matrix{{targets#targetIndex} | eqs};
elapsedTime Z = syz globalRow;
assert(globalRow*Z == 0);
ncols = numgens source Z;
witnessColumns = if ncols == 0 then {} else select(toList(0..ncols-1),
    j -> closedMod2(Z_(0,j)) != 0);
<< "SYZYGY_COLUMNS " << ncols
   << " UNIT_TARGET_COLUMNS " << toString witnessColumns << endl;
if #witnessColumns > 0 then (
    witness := Z_{first witnessColumns};
    assert(globalRow*witness == 0);
    assert(closedMod2(witness_(0,0)) != 0);
    << "LOCAL_MEMBERSHIP_CERTIFICATE mode=ZZ_(2) t4_c4=" << c4bit
       << " target=" << targetIndex << endl;
    << "CERTIFICATE_COLUMN " << toExternalString witness << endl;
    )
else (
    << "COMPLETE_NO_UNIT_SYZYGY_COUNTEREXAMPLE_SEED mode=ZZ_(2) t4_c4="
       << c4bit << " target=" << targetIndex << endl;
    );
<< "DONE universal_local_rank4_t4_monogenic c4=" << c4bit
   << " target=" << targetIndex << endl;
