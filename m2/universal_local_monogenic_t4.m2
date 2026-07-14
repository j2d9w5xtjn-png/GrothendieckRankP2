-- universal_local_monogenic_t4.m2
--
-- Exact localized universal chart for the monogenic t^4 branch of the
-- rank-four problem.  Every augmented rank-four algebra whose closed fiber
-- is k[t]/t^4 has, after choosing a lift T of t, the unique presentation
--
--     A = R[T]/(T^4-a*T-b*T^2-d*T^3),   a,b,d in m_R.
--
-- A counital coproduct is determined by nine reduced coefficients in
-- Delta(T).  We pin its closed fiber to one of the two geometric charts
--
--     t4(0,c4): Delta_0(t)=t@1+1@t+c4*t^2@t^2, c4=0 or 1.
--
-- Quartic relation stability makes Delta multiplicative; coassociativity on
-- T then makes this a bialgebra.  The closed fiber is Hopf, so the antipode
-- lifts at every Artin-local point.  Thus the 12-variable chart is complete
-- for all local deformations of either geometric t4 fiber.
--
-- The three targets are the T,T^2,T^3 coordinates of [4]^#(T).  In integral
-- mode a global syzygy whose target coefficient has odd constant term is an
-- exact certificate after localization at (2,a,b,d,the nine c_ij).  Six
-- branch/target jobs therefore decide the complete monogenic local-local
-- branch, in equal and mixed characteristic, if they terminate.
--
-- On a login node use only RANK4_MONO_GENERATE_ONLY=1.
--
-- Environment:
--   RANK4_MONO_BRANCH        0=t4(0,0), 1=t4(0,1) (default 0)
--   RANK4_MONO_TARGET        target 0..2 (default 0)
--   RANK4_MONO_INTEGRAL      1 for the decisive ZZ_(2) chart (default 1)
--   RANK4_MONO_SYZYGY        1 for exact global syzygies (default 1)
--   RANK4_MONO_GENERATE_ONLY 1 to construct and gate only (default 0)
--   RANK4_MONO_COCOMM       1 to impose cocommutativity by using the six
--                            symmetric reduced coproduct coefficients
--   RANK4_MONO_PRINT_EQS    1 to print the exact defining equations

kk = ZZ/2;

envMissing = s -> s === null or (class s === String and #s == 0);

branchString = getenv "RANK4_MONO_BRANCH";
branch = if envMissing branchString then 0 else value branchString;
if branch < 0 or branch > 1 then error "RANK4_MONO_BRANCH must be 0 or 1";
c4bit = branch;
branchName = "t4_0" | toString c4bit;

targetString = getenv "RANK4_MONO_TARGET";
targetIndex = if envMissing targetString then 0 else value targetString;
if targetIndex < 0 or targetIndex > 2 then
    error "RANK4_MONO_TARGET must lie in 0..2";

integralString = getenv "RANK4_MONO_INTEGRAL";
integralMode = if envMissing integralString then true else integralString == "1";

syzygyString = getenv "RANK4_MONO_SYZYGY";
syzygyMode = integralMode or
    (if envMissing syzygyString then true else syzygyString == "1");

generateString = getenv "RANK4_MONO_GENERATE_ONLY";
generateOnly = not envMissing generateString and generateString == "1";

printTangentString = getenv "RANK4_MONO_PRINT_TANGENT";
printTangent = not envMissing printTangentString and printTangentString == "1";

cocommString = getenv "RANK4_MONO_COCOMM";
cocommMode = not envMissing cocommString and cocommString == "1";

printEqsString = getenv "RANK4_MONO_PRINT_EQS";
printEqs = not envMissing printEqsString and printEqsString == "1";


printStatsString = getenv "RANK4_MONO_PRINT_STATS";
printStats = not envMissing printStatsString and printStatsString == "1";

printQuadraticString = getenv "RANK4_MONO_PRINT_QUADRATIC";
printQuadratic = ((not envMissing printQuadraticString) and (printQuadraticString == "1"));

nVars = if cocommMode then 9 else 12;
MM = monoid[Variables => nVars, MonomialOrder => GRevLex];
Q = (if integralMode then ZZ else kk) MM;

a = Q_0;
b = Q_1;
d = Q_2;
cSymIndex = hashTable {
    (1,1) => 3,
    (1,2) => 4,
    (1,3) => 5,
    (2,2) => 6,
    (2,3) => 7,
    (3,3) => 8
    };
cVar = (i,j) -> (
    if cocommMode then
        Q_(cSymIndex#(if i <= j then (i,j) else (j,i)))
    else
        Q_(3 + 3*(i-1) + j-1)
    );

ebas = i -> apply(4, r -> if r == i then 1_Q else 0_Q);
idx2 = (i,j) -> 4*i+j;
idx3 = (i,j,k) -> 16*i+4*j+k;

mulByT = v -> {
    0_Q,
    v#0 + a*v#3,
    v#1 + b*v#3,
    v#2 + d*v#3
    };

powerT = new MutableList from toList(7:null);
powerT#0 = ebas 0;
for n from 1 to 6 do powerT#n = mulByT(powerT#(n-1));

Stab = hashTable flatten for i from 0 to 3 list for j from 0 to 3 list
    (i,j) => powerT#(i+j);

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

deltaT = new MutableList from toList(16:0_Q);
deltaT#(idx2(1,0)) = 1_Q;
deltaT#(idx2(0,1)) = 1_Q;
for ii from 1 to 3 do for jj from 1 to 3 do (
    pin := if c4bit == 1 and ii == 2 and jj == 2 then 1_Q else 0_Q;
    deltaT#(idx2(ii,jj)) = cVar(ii,jj) + pin;
    );
deltaT = toList deltaT;

-- Delta on powers of T, computed multiplicatively in A tensor A.
deltaPowers = new MutableList from toList(4:null);
deltaPowers#0 = apply(16, r -> if r == 0 then 1_Q else 0_Q);
deltaPowers#1 = deltaT;
for n from 2 to 3 do deltaPowers#n = mulT2(deltaPowers#(n-1),deltaT);

deltaOfVec = v -> (
    out := new MutableList from toList(16:0_Q);
    for i from 0 to 3 do if v#i != 0 then
        for r from 0 to 15 do if (deltaPowers#i)#r != 0 then
            out#r = out#r + v#i*(deltaPowers#i)#r;
    toList out
    );

-- The single multiplicativity condition: Delta carries the quartic
-- relation to zero.  Compute Delta(T)^4 via one further multiplication.
deltaT4 = mulT2(deltaPowers#3,deltaT);
dT1 = deltaPowers#1;
dT2 = deltaPowers#2;
dT3 = deltaPowers#3;
relationDelta = apply(16, ii ->
    deltaT4#ii - a*dT1#ii - b*dT2#ii - d*dT3#ii);

-- Coassociativity on the generator.  Coordinates with a zero leg vanish
-- automatically by the counital form, but retaining all 64 is a cheap gate;
-- unique below removes the automatic zeros and duplicates.
coassocRaw = (
    left := new MutableList from toList(64:0_Q);
    right := new MutableList from toList(64:0_Q);
    for r from 0 to 3 do for s from 0 to 3 do (
        u := deltaT#(idx2(r,s));
        if u != 0 then (
            dr := deltaPowers#r;
            for i from 0 to 3 do for j from 0 to 3 do
                if dr#(idx2(i,j)) != 0 then
                    left#(idx3(i,j,s)) = left#(idx3(i,j,s))
                        + u*dr#(idx2(i,j));
            ds := deltaPowers#s;
            for j from 0 to 3 do for k from 0 to 3 do
                if ds#(idx2(j,k)) != 0 then
                    right#(idx3(r,j,k)) = right#(idx3(r,j,k))
                        + u*ds#(idx2(j,k));
            );
        );
    flatten flatten flatten for i from 0 to 3 list for j from 0 to 3 list for k from 0 to 3 list
        left#(idx3(i,j,k)) - right#(idx3(i,j,k))
    );

relationEqs = unique select(relationDelta, f -> f != 0);
coassocEqs = unique select(coassocRaw, f -> f != 0);
eqs = unique(relationEqs | coassocEqs);

-- q=[2]^# is multiplication after Delta.  Because T generates A, the three
-- coordinates of q(q(T)) are exactly all [4]-targets.
qT = new MutableList from toList(4:0_Q);
for i from 0 to 3 do for j from 0 to 3 do
    if deltaT#(idx2(i,j)) != 0 then (
        sij := Stab#(i,j);
        for r from 0 to 3 do if sij#r != 0 then
            qT#r = qT#r + deltaT#(idx2(i,j))*sij#r;
        );
qT = toList qT;

qPowers = new MutableList from toList(4:null);
qPowers#0 = ebas 0;
qPowers#1 = qT;
for n from 2 to 3 do qPowers#n = mulA(qPowers#(n-1),qT);

p4T = new MutableList from toList(4:0_Q);
for i from 0 to 3 do if qT#i != 0 then
    for r from 0 to 3 do if (qPowers#i)#r != 0 then
        p4T#r = p4T#r + qT#i*(qPowers#i)#r;
p4T = toList p4T;
targets = p4T_{1..3};

-- Determinant character of universal right translation.  Column n is
-- Delta(T^n), viewed as a polynomial in the first tensor leg with
-- coefficients in the second copy of A.
translationEntry = (row,column) -> apply(4, jj ->
    (deltaPowers#column)#(idx2(row,jj)));
perms4 = permutations toList(0..3);
deltaVec = new MutableList from toList(4:0_Q);
for pp in perms4 do (
    inv := sum flatten for rr from 0 to 2 list for ss from rr+1 to 3 list
        if pp#rr > pp#ss then 1 else 0;
    sg := if inv % 2 == 0 then 1_Q else -1_Q;
    term := ebas 0;
    for rr from 0 to 3 do term = mulA(term,translationEntry(rr,pp#rr));
    for jj from 0 to 3 do deltaVec#jj = deltaVec#jj + sg*term#jj;
    );
deltaVec = toList deltaVec;
deltaDeviation = apply(4, jj -> deltaVec#jj - (ebas 0)#jj);

qgens = toList gens Q;
originQ = f -> sub(f,apply(qgens,x -> x => 0_Q));
originCoefficient = f -> (
    if integralMode then lift(originQ f,ZZ) else lift(originQ f,kk)
    );
closedMod2 = f -> (
    if integralMode then promote(originCoefficient f,kk) else originCoefficient f
    );
halfConstantMod2 = f -> promote((originCoefficient f)//2,kk);

badEqConstants = select(eqs, f -> closedMod2 f != 0);
badQFiber = select(qT_{1..3}, f -> closedMod2 f != 0);
badTargetConstants = select(targets, f -> closedMod2 f != 0);
badTargetQ2Constants = if integralMode then
    select(targets, f -> promote(originCoefficient f,ZZ/4) != 0) else {};

jacobianAtClosedPoint = fs -> matrix apply(fs, f ->
    (if integralMode then {halfConstantMod2 f} else {})
    | apply(qgens, x -> closedMod2 diff(x,f)));
eqJacobian = jacobianAtClosedPoint eqs;
targetJacobian = jacobianAtClosedPoint targets;
deltaJacobian = jacobianAtClosedPoint deltaDeviation;
tangentRank = rank eqJacobian;
tangentAmbient = nVars + (if integralMode then 1 else 0);
targetLinearRank = rank targetJacobian;
combinedDeltaJacobian = jacobianAtClosedPoint(eqs | deltaDeviation);
combinedDeltaRank = rank combinedDeltaJacobian;
deltaCotangentRank = combinedDeltaRank - tangentRank;

-- In cocommutative integral mode, compute the quadratic equations in the
-- minimal Cohen presentation.  The ten local variables are ordered
--
--   (two,a,b,d,c11,c12,c13,c22,c23,c33).
--
-- Rows 1,3,6,8,9 have the independent linear terms
-- d,two,c13,c23,c33.  Subtracting these pivot rows and then setting the
-- five pivot variables to zero is formal implicit-function elimination to
-- second order.  Coefficient 2-adic digits supply the terms involving
-- the local variable "two".
if printQuadratic and (not integralMode or not cocommMode) then
    error "RANK4_MONO_PRINT_QUADRATIC requires integral cocommutative mode";

if printQuadratic then (
    localPairs := flatten for ii from 0 to nVars list
        for jj from ii to nVars list (ii,jj);
    coefficientQuadratic := (f,pp) -> (
        ii := pp#0;
        jj := pp#1;
        if ii == 0 and jj == 0 then
            promote((originCoefficient f)//4,kk)
        else if ii == 0 then
            promote((originCoefficient diff(qgens#(jj-1),f))//2,kk)
        else if ii < jj then
            promote(originCoefficient diff(qgens#(ii-1),
                diff(qgens#(jj-1),f)),kk)
        else
            promote((originCoefficient diff(qgens#(ii-1),
                diff(qgens#(ii-1),f)))//2,kk)
        );
    quadraticMatrix = matrix apply(eqs, f ->
        apply(localPairs, pp -> coefficientQuadratic(f,pp)));
    pivotRows := {1,3,6,8,9};
    pivotCols := {3,0,6,8,9};
    freeCols := {1,2,4,5,7};
    freePairPositions := select(toList(0..#localPairs-1), cc -> (
        pp := localPairs#cc;
        member(pp#0,freeCols) and member(pp#1,freeCols)));
    residualQuadraticMatrix = matrix apply(toList(0..#eqs-1), rr ->
        apply(freePairPositions, cc ->
            quadraticMatrix_(rr,cc)
            + sum(toList(0..#pivotRows-1), tt ->
                eqJacobian_(rr,pivotCols#tt)
                    *quadraticMatrix_(pivotRows#tt,cc))));
    residualQuadraticRank = rank residualQuadraticMatrix;
    );

<< "############################################################" << endl;
<< "## universal monogenic t4 branch=" << branchName
   << " coefficient_mode=" << (if integralMode then "ZZ_(2)" else "F2")
   << " cocommutative=" << cocommMode << endl;
<< "## variables=" << nVars
   << " raw_relation=" << #relationDelta
   << " raw_coassoc=" << #coassocRaw
   << " category_unique=" << toString{#relationEqs,#coassocEqs}
   << " unique_nonzero_equations=" << #eqs
   << " targets=" << #targets << endl;
<< "TANGENT rank=" << tangentRank
   << " dimension=" << tangentAmbient-tangentRank
   << " target_linear_rank=" << targetLinearRank
   << " delta_cotangent_rank=" << deltaCotangentRank << endl;
<< "GATE pinned equations vanish at closed point: "
   << (if #badEqConstants == 0 then "OK" else "FAILED") << endl;
<< "GATE pinned fiber killed by two: "
   << (if #badQFiber == 0 then "OK" else "FAILED") << endl;
<< "GATE P4 targets vanish at closed point: "
   << (if #badTargetConstants == 0 then "OK" else "FAILED") << endl;
<< "GATE P4 has local order at least two: "
   << (if targetLinearRank == 0 then "OK" else "FAILED") << endl;
<< "GATE determinant deviation has local order at least two: "
   << (if deltaCotangentRank == 0 then "OK" else "FAILED") << endl;
if printTangent then (
    << "TANGENT_COLUMN_ORDER "
       << (if cocommMode then
           "{two,a,b,d,c11,c12,c13,c22,c23,c33}"
           else "{two,a,b,d,c11,c12,c13,c21,c22,c23,c31,c32,c33}")
       << endl;
    << "EQUATION_TANGENT_MATRIX " << toExternalString eqJacobian << endl;
    << "DELTA_TANGENT_MATRIX " << toExternalString deltaJacobian << endl;
    );
if printEqs then (
    << "EXACT_EQUATION_ORDER " << toExternalString eqs << endl;
    );
if printStats then (
    << "EQUATION_DEGREES " << toString apply(eqs, degree) << endl;
    << "EQUATION_TERM_COUNTS " << toString apply(eqs, f -> # support f) << endl;
    << "POWER_T " << toExternalString toList powerT << endl;
    << "DELTA_T_DEGREES " << toString apply(deltaT, degree) << endl;
    << "DELTA_POWER_DEGREES "
       << toString apply(toList deltaPowers, vv -> apply(vv, degree)) << endl;
    << "DELTA_T4_DEGREES " << toString apply(deltaT4, degree) << endl;
    << "RELATION_RAW_DEGREES " << toString apply(relationDelta, degree) << endl;
    << "COASSOC_RAW_DEGREES " << toString apply(coassocRaw, degree) << endl;
    );
if printQuadratic then (
    << "MINIMAL_FREE_VARIABLES {a,b,c11,c12,c22}" << endl;
    << "MINIMAL_QUADRATIC_MONOMIALS "
       << toString apply(freePairPositions, cc -> localPairs#cc) << endl;
    << "MINIMAL_QUADRATIC_MATRIX "
       << toExternalString residualQuadraticMatrix << endl;
    << "MINIMAL_QUADRATIC_RANK " << residualQuadraticRank << endl;
    );
if integralMode then << "GATE P4 constants divisible by four: "
   << (if #badTargetQ2Constants == 0 then "OK" else "FAILED") << endl;

if #badEqConstants != 0 or #badQFiber != 0 or #badTargetConstants != 0
    or #badTargetQ2Constants != 0 or targetLinearRank != 0
    or deltaCotangentRank != 0
then error "universal monogenic t4 construction gate failed";

-- Tiny exact API gate before a potentially large syzygy.
if syzygyMode then (
    toyX := Q_0;
    toyY := Q_1;
    if integralMode then (
        toyGen := (1_Q+toyX*toyY)*(2_Q+toyX*toyY);
        toyTarget := (2_Q+toyX*toyY)^2;
        )
    else (
        toyGen = toyX*(1_Q+toyY);
        toyTarget = toyX;
        );
    toyRow := matrix{{toyTarget,toyGen}};
    toyZ := syz toyRow;
    assert(toyRow*toyZ == 0);
    toyCols := numgens source toyZ;
    toyWitnesses := select(toList(0..toyCols-1),
        j -> closedMod2(toyZ_(0,j)) != 0);
    assert(#toyWitnesses > 0);
    << "GATE exact unit-cofactor syzygy API: OK" << endl;
    );

if generateOnly then (
    << "GENERATE_ONLY complete; no Groebner basis launched" << endl;
    exit 0;
    );

if not syzygyMode then error "only exact syzygy mode is supported";

<< "-- exact global syzygy for local target=" << targetIndex << ": " << flush;
globalRow = matrix{{targets#targetIndex} | eqs};
elapsedTime Z = syz globalRow;
assert(globalRow*Z == 0);
ncols = numgens source Z;
witnessColumns = if ncols == 0 then {} else select(toList(0..ncols-1),
    j -> promote(originCoefficient(Z_(0,j)),kk) != 0);
<< "SYZYGY_COLUMNS " << ncols
   << " UNIT_TARGET_COLUMNS " << toString witnessColumns << endl;
if #witnessColumns > 0 then (
    witness := Z_{first witnessColumns};
    assert(globalRow*witness == 0);
    assert(promote(originCoefficient(witness_(0,0)),kk) != 0);
    << "LOCAL_MEMBERSHIP_CERTIFICATE mode="
       << (if integralMode then "ZZ_(2)" else "F2")
       << " branch=" << branchName << " target=" << targetIndex << endl;
    << "CERTIFICATE_COLUMN " << toExternalString witness << endl;
    )
else (
    << "COMPLETE_NO_UNIT_SYZYGY_COUNTEREXAMPLE_SEED mode="
       << (if integralMode then "ZZ_(2)" else "F2")
       << " branch=" << branchName << " target=" << targetIndex << endl;
    );
<< "DONE universal_local_monogenic_t4 mode="
   << (if integralMode then "ZZ_(2)" else "F2")
   << " branch=" << branchName << " target=" << targetIndex << endl;
