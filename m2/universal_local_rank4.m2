-- universal_local_rank4.m2
--
-- One-shot localized deformation test for six pinned local--local rank-four
-- charts in residue characteristic two.  The t4_10 and t4_11 charts are
-- retained as basis-change duplicates of t4_00 and t4_01 for auditing.
--
-- Mathematical scope.  Fix a basis 1,e1,e2,e3 lifting a chosen special
-- fiber.  There are 18 commutative augmented multiplication deformations
-- and 27 reduced coproduct deformations.  The local polynomial ring below
-- is the 45-variable deformation chart at that fiber.  Associativity,
-- compatibility, and coassociativity cut out the universal bialgebra chart.
-- Because the pinned closed fiber is Hopf, the antipode lifts over every
-- Artin-local point of this chart.  The nine targets are the augmentation
-- coordinates of [4]^#(e_i).
--
-- In the default equal-characteristic mode, a zero local normal form for all
-- targets proves killedness by four for every characteristic-two local
-- deformation of the selected fiber.  In integral mode the coefficient ring
-- is ZZ and the chart is localized at (2,all deformation variables); a unit
-- syzygy is an exact mixed/equal-characteristic membership certificate.
--
-- This file is designed for Slurm.  On a login node or laptop use only
-- RANK4_GENERATE_ONLY=1, which builds the exact equations and gates but does
-- not start a Groebner basis computation.
--
-- Environment:
--   RANK4_BRANCH       0=a2a2, 1=W2F, 2=t4_00, 3=t4_01,
--                      4=t4_10, 5=t4_11 (default 0)
--   RANK4_GENERATE_ONLY 1 to stop after exact construction (default 0)
--   RANK4_EXPORT_POLYS  1 to print exact equations/targets and stop
--   RANK4_INTEGRAL     1 for the true ZZ_(2) local chart (default 0)
--   RANK4_SYZYGY       1 for an exact global cofactor search in F2 mode
--   RANK4_TARGET       target 0..8 in either syzygy mode (default 0)
--   RANK4_DEGREE_LIMIT positive partial degree limit; 0 means full GB

kk = ZZ/2;

-- M2 1.25 returns the empty string for an unset variable on macOS, while
-- some container builds return null.
envMissing = s -> s === null or (class s === String and #s == 0);

branchString = getenv "RANK4_BRANCH";
branch = if envMissing branchString then 0 else value branchString;
if branch < 0 or branch > 5 then error "RANK4_BRANCH must lie in 0..5";

generateString = getenv "RANK4_GENERATE_ONLY";
generateOnly = generateString =!= null and generateString == "1";

exportString = getenv "RANK4_EXPORT_POLYS";
exportPolys = not envMissing exportString and exportString == "1";

degreeString = getenv "RANK4_DEGREE_LIMIT";
degreeLimit = if envMissing degreeString then 0 else value degreeString;
if degreeLimit < 0 then error "RANK4_DEGREE_LIMIT must be nonnegative";

integralString = getenv "RANK4_INTEGRAL";
integralMode = not envMissing integralString and integralString == "1";

syzygyString = getenv "RANK4_SYZYGY";
syzygyMode = integralMode or
    (not envMissing syzygyString and syzygyString == "1");

targetString = getenv "RANK4_TARGET";
targetIndex = if envMissing targetString then 0 else value targetString;
if targetIndex < 0 or targetIndex > 8 then error "RANK4_TARGET must lie in 0..8";

nMul = 18;
nCop = 27;
nVars = nMul + nCop;

-- Negative weights give Mora's local ordering in the F2-only mode.  Integral
-- mode stays in a global ZZ polynomial ring; a global syzygy with unit
-- target coefficient certifies exact localization at (2,variables).
MM = (
    if syzygyMode then monoid[Variables => nVars, MonomialOrder => GRevLex]
    else monoid[
        Variables => nVars,
        MonomialOrder => Weights => splice {nVars:-1},
        Global => false
        ]
    );
Q = (if integralMode then ZZ else kk) MM;

pairPosition = (a,b) -> (
    u := min(a,b);
    v := max(a,b);
    if u == 1 then v - 1
    else if u == 2 then v + 1
    else 5
    );

mVar = (i,j,r) -> Q_(3 * pairPosition(i,j) + r - 1);
cVar = (i,j,k) -> Q_(nMul + 9 * (i-1) + 3 * (j-1) + k - 1);

isT4 = branch >= 2;
t4Code = if isT4 then branch - 2 else 0;
c1bit = if isT4 then t4Code // 2 else 0;
c4bit = if isT4 then t4Code % 2 else 0;

branchName = (
    if branch == 0 then "a2a2"
    else if branch == 1 then "W2F"
    else "t4_" | toString(c1bit) | toString(c4bit)
    );

fiberMul = (
    if isT4 then set {(1,1,2),(1,2,3)}
    else set {(1,2,3)}
    );

pinCop = (i,j,k) -> (
    if not isT4 then (
        if (i,j,k) == (3,1,2) or (i,j,k) == (3,2,1) then 1_Q
        else if branch == 1 and (i,j,k) == (2,1,1) then 1_Q
        else 0_Q
        )
    else (
        if i == 1 then (
            if (j,k) == (1,2) or (j,k) == (2,1) then c1bit * 1_Q
            else if (j,k) == (2,3) or (j,k) == (3,2) then c1bit * 1_Q
            else if (j,k) == (2,2) then c4bit * 1_Q
            else 0_Q
            )
        else if i == 2 then 0_Q
        else (
            if (j,k) == (1,2) or (j,k) == (2,1) then 1_Q
            else if (j,k) == (2,3) or (j,k) == (3,2) then c1bit * 1_Q
            else 0_Q
            )
        )
    );

ebas = i -> apply(4, r -> if r == i then 1_Q else 0_Q);
idx2 = (a,b) -> 4*a + b;
idx3 = (a,b,c) -> 16*a + 4*b + c;

Mc = (i,j,r) -> (
    (if member((min(i,j),max(i,j),r), fiberMul) then 1_Q else 0_Q)
    + mVar(i,j,r)
    );

Cc = (i,j,k) -> pinCop(i,j,k) + cVar(i,j,k);

Stab = hashTable flatten for a from 0 to 3 list for b from 0 to 3 list
    (a,b) => (
        if a == 0 then ebas b
        else if b == 0 then ebas a
        else {0_Q,Mc(a,b,1),Mc(a,b,2),Mc(a,b,3)}
        );

DEl = for i from 0 to 3 list (
    if i == 0 then apply(16, t -> if t == 0 then 1_Q else 0_Q)
    else (
        v := new MutableList from toList(16:0_Q);
        v#(idx2(i,0)) = 1_Q;
        v#(idx2(0,i)) = 1_Q;
        for j from 1 to 3 do for k from 1 to 3 do
            v#(idx2(j,k)) = Cc(i,j,k);
        toList v
        )
    );

mulA = (u,v) -> (
    out := new MutableList from toList(4:0_Q);
    for i from 0 to 3 do if u#i != 0 then
        for j from 0 to 3 do if v#j != 0 then (
            sij := Stab#(i,j);
            for r from 0 to 3 do if sij#r != 0 then
                out#r = out#r + u#i * v#j * sij#r;
            );
    toList out
    );

DofVec = v -> (
    out := new MutableList from toList(16:0_Q);
    for r from 0 to 3 do if v#r != 0 then (
        dr := DEl#r;
        for t from 0 to 15 do if dr#t != 0 then
            out#t = out#t + v#r * dr#t;
        );
    toList out
    );

mulT2 = (u,v) -> (
    out := new MutableList from toList(16:0_Q);
    for a from 0 to 3 do for b from 0 to 3 do (
        ua := u#(idx2(a,b));
        if ua != 0 then for aa from 0 to 3 do for bb from 0 to 3 do (
            vb := v#(idx2(aa,bb));
            if vb != 0 then (
                sa := Stab#(a,aa);
                sb := Stab#(b,bb);
                for r from 0 to 3 do if sa#r != 0 then
                    for s from 0 to 3 do if sb#s != 0 then
                        out#(idx2(r,s)) = out#(idx2(r,s))
                            + ua * vb * sa#r * sb#s;
                );
            );
        );
    toList out
    );

-- Check all ordered augmentation triples.  Commutativity creates many
-- duplicates, removed below; checking only one bracketing per unordered
-- triple would miss the second independent pairing for three distinct
-- elements.  The constant coordinate is automatic from augmentation.
assocRaw = flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
    for k from 1 to 3 list (
        left := mulA(Stab#(i,j), ebas k);
        right := mulA(ebas i, Stab#(j,k));
        for r from 1 to 3 list left#r - right#r
        );

-- The tensor coordinates with a zero leg follow automatically from the
-- counital normal form, so retain only the 3x3 reduced block.
compatRaw = flatten flatten for i from 1 to 3 list for j from i to 3 list (
    left := DofVec(Stab#(i,j));
    right := mulT2(DEl#i,DEl#j);
    flatten for r from 1 to 3 list for s from 1 to 3 list
        left#(idx2(r,s)) - right#(idx2(r,s))
    );

coassocRaw = flatten flatten for i from 1 to 3 list (
    left := new MutableList from toList(64:0_Q);
    right := new MutableList from toList(64:0_Q);
    di := DEl#i;
    for r from 0 to 3 do for s from 0 to 3 do (
        u := di#(idx2(r,s));
        if u != 0 then (
            dr := DEl#r;
            for a from 0 to 3 do for b from 0 to 3 do
                if dr#(idx2(a,b)) != 0 then
                    left#(idx3(a,b,s)) = left#(idx3(a,b,s))
                        + u * dr#(idx2(a,b));
            ds := DEl#s;
            for b from 0 to 3 do for c from 0 to 3 do
                if ds#(idx2(b,c)) != 0 then
                    right#(idx3(r,b,c)) = right#(idx3(r,b,c))
                        + u * ds#(idx2(b,c));
            );
        );
    flatten for a from 1 to 3 list for b from 1 to 3 list
        for c from 1 to 3 list
            left#(idx3(a,b,c)) - right#(idx3(a,b,c))
    );

phiL = for i from 0 to 3 list (
    if i == 0 then ebas 0
    else (
        out := new MutableList from toList(4:0_Q);
        di := DEl#i;
        for j from 0 to 3 do for k from 0 to 3 do
            if di#(idx2(j,k)) != 0 then (
                sjk := Stab#(j,k);
                for r from 0 to 3 do if sjk#r != 0 then
                    out#r = out#r + di#(idx2(j,k)) * sjk#r;
                );
        toList out
        )
    );

p4L = for i from 1 to 3 list (
    out := new MutableList from toList(4:0_Q);
    for r from 1 to 3 do if (phiL#i)#r != 0 then
        for s from 1 to 3 do if (phiL#r)#s != 0 then
            out#s = out#s + (phiL#i)#r * (phiL#r)#s;
    toList out
    );

assocEqs = unique select(assocRaw, f -> f != 0);
compatEqs = unique select(compatRaw, f -> f != 0);
coassocEqs = unique select(coassocRaw, f -> f != 0);
eqs = unique (assocEqs | compatEqs | coassocEqs);
targets = flatten apply(p4L, v -> v_{1..3});

qgens = toList gens Q;
originQ = f -> sub(f, apply(qgens, x -> x => 0_Q));
originCoefficient = f -> (
    if integralMode then lift(originQ f,ZZ) else lift(originQ f,kk)
    );
closedMod2 = f -> (
    if integralMode then promote(originCoefficient f,kk) else originCoefficient f
    );
halfConstantMod2 = f -> promote((originCoefficient f)//2,kk);

badAugPhi = select(phiL_{1..3}, v -> v#0 != 0);
badEqConstants = select(eqs, f -> closedMod2 f != 0);
badTargetConstants = select(targets, f -> closedMod2 f != 0);
badFiberSquare = select(flatten apply(phiL_{1..3}, v -> v_{1..3}),
    f -> closedMod2 f != 0);
badTargetQ2Constants = (
    if integralMode then select(targets, f -> promote(originCoefficient f,ZZ/4) != 0)
    else {}
    );

jacobianAtClosedPoint = fs -> matrix apply(fs, f ->
    (if integralMode then {halfConstantMod2 f} else {})
    | apply(qgens, x -> closedMod2 diff(x,f)));
eqJacobian = jacobianAtClosedPoint eqs;
targetJacobian = jacobianAtClosedPoint targets;
tangentRank = rank eqJacobian;
tangentAmbientDimension = nVars + (if integralMode then 1 else 0);
tangentDimension = tangentAmbientDimension - tangentRank;
targetLinearRank = rank targetJacobian;

<< "############################################################" << endl;
<< "## universal local rank4 branch=" << branch << " name=" << branchName
   << " coefficient_mode=" << (if integralMode then "ZZ_(2)" else "F2") << endl;
<< "## variables=" << nVars
   << " raw_assoc=" << #assocRaw
   << " raw_compat=" << #compatRaw
   << " raw_coassoc=" << #coassocRaw
   << " category_unique=" << toString{#assocEqs,#compatEqs,#coassocEqs}
   << " unique_nonzero_equations=" << #eqs
   << " targets=" << #targets << endl;
<< "TANGENT rank=" << tangentRank << " dimension=" << tangentDimension
   << " target_linear_rank=" << targetLinearRank << endl;
<< "GATE doubling preserves augmentation symbolically: "
   << (if #badAugPhi == 0 then "OK" else "FAILED") << endl;
<< "GATE pinned equations vanish at origin: "
   << (if #badEqConstants == 0 then "OK" else "FAILED") << endl;
<< "GATE pinned fiber killed by 2: "
   << (if #badFiberSquare == 0 then "OK" else "FAILED") << endl;
<< "GATE P4 targets vanish at origin: "
   << (if #badTargetConstants == 0 then "OK" else "FAILED") << endl;
<< "GATE P4 has local order at least two: "
   << (if targetLinearRank == 0 then "OK" else "FAILED") << endl;
if integralMode then (
    << "GATE P4 constants divisible by four: "
       << (if #badTargetQ2Constants == 0 then "OK" else "FAILED") << endl
    );

if #badAugPhi != 0 or #badEqConstants != 0 or #badFiberSquare != 0
    or #badTargetConstants != 0 or #badTargetQ2Constants != 0
    or targetLinearRank != 0
then error "universal local construction gate failed";

-- Exercise the exact unit-cofactor API on a tiny identity before any large
-- syzygy computation.  This also guards the column-index and constant-term
-- conventions used below.
if syzygyMode then (
    toyX := Q_0;
    toyY := Q_1;
    if integralMode then (
        toyGen := (1_Q + toyX*toyY) * (2_Q + toyX*toyY);
        toyTarget := (2_Q + toyX*toyY)^2;
        )
    else (
        toyGen = toyX * (1_Q + toyY);
        toyTarget = toyX;
        );
    toyRow := matrix{{toyTarget,toyGen}};
    toyZ := syz toyRow;
    assert(toyRow * toyZ == 0);
    toyCols := numgens source toyZ;
    toyWitnesses := select(toList(0..toyCols-1),
        j -> closedMod2(toyZ_(0,j)) != 0);
    assert(#toyWitnesses > 0);
    << "GATE exact unit-cofactor syzygy API: OK" << endl;
    );

-- Canonical source-level interchange for independent low-order auditors.
-- The p_i names are the 45 variables in Q_(i) order.  Consumers may truncate
-- these exact integer polynomials only after parsing the complete sums.
if exportPolys then (
    << "EXPORT_EQS_BEGIN count=" << #eqs << endl;
    scan(#eqs, i -> << "E " << i << " " << toExternalString(eqs#i) << endl);
    << "EXPORT_EQS_END" << endl;
    << "EXPORT_TARGETS_BEGIN count=" << #targets << endl;
    scan(#targets, i -> << "T " << i << " " << toExternalString(targets#i) << endl);
    << "EXPORT_TARGETS_END" << endl;
    exit 0;
    );

if generateOnly then (
    << "GENERATE_ONLY complete; no Groebner basis launched" << endl;
    exit 0;
    );

J = ideal eqs;

if syzygyMode then (
    << "-- exact global syzygy for local target=" << targetIndex << ": " << flush;
    globalRow := matrix{{targets#targetIndex} | eqs};
    elapsedTime Z := syz globalRow;
    assert(globalRow * Z == 0);
    ncols := numgens source Z;
    witnessColumns := if ncols == 0 then {} else select(toList(0..ncols-1),
        j -> promote(originCoefficient(Z_(0,j)),kk) != 0);
    << "SYZYGY_COLUMNS " << ncols
       << " UNIT_TARGET_COLUMNS " << toString witnessColumns << endl;
    if #witnessColumns > 0 then (
        witness := Z_{first witnessColumns};
        assert(globalRow * witness == 0);
        assert(promote(originCoefficient(witness_(0,0)),kk) != 0);
        << "LOCAL_MEMBERSHIP_CERTIFICATE mode="
           << (if integralMode then "ZZ_(2)" else "F2")
           << " branch=" << branchName
           << " target=" << targetIndex << endl;
        << "CERTIFICATE_COLUMN " << toExternalString witness << endl;
        )
    else (
        << "COMPLETE_NO_UNIT_SYZYGY_COUNTEREXAMPLE_SEED mode="
           << (if integralMode then "ZZ_(2)" else "F2")
           << " branch=" << branchName
           << " target=" << targetIndex << endl;
        );
    << "DONE universal_local_rank4 syzygy mode="
       << (if integralMode then "ZZ_(2)" else "F2")
       << " branch=" << branchName
       << " target=" << targetIndex << endl;
    exit 0;
    );

<< "-- local standard basis start"
   << (if degreeLimit > 0 then " DegreeLimit=" | toString degreeLimit else " full")
   << ": " << flush;

elapsedTime G = if degreeLimit > 0
    then gb(J, DegreeLimit => degreeLimit)
    else gb J;

rems = apply(targets, f -> f % G);
open = positions(rems, f -> f != 0);
<< "LOCAL TARGETS OPEN: " << #open << " / " << #targets << endl;
if #open > 0 then << "OPEN TARGET INDICES: " << toString open << endl;
if #open == 0 then
    << "ALL_LOCAL_P4_TARGETS_ZERO branch=" << branchName << endl;
else
    << "PARTIAL_OR_NONTERMINAL_NO_THEOREM branch=" << branchName << endl;

<< "DONE universal_local_rank4 branch=" << branchName << endl;
