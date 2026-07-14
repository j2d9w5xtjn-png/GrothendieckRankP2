-- A readable, self-contained verification of the rank-four counterexample.
--
-- Run from the project root with
--
--   M2 --script m2/verify_rank4_counterexample_simple.m2
--
-- Every calculation is exact over ZZ.  A failed assertion stops the script.

------------------------------------------------------------------------
-- 1. The base ring
------------------------------------------------------------------------

R0 = ZZ[r,s,MonomialOrder=>Lex];
f1 = r^3+2;
f2 = s^3+2;
f3 = r*s^2;
I0 = ideal(f1,f2,f3);
G0 = gb I0;

-- The three equations are a regular sequence.  The ideal-quotient
-- identities say successively that f1, f2 mod f1, and f3 mod (f1,f2)
-- are nonzerodivisors.
J0 = ideal(0_R0);
J1 = ideal(f1);
J2 = ideal(f1,f2);
assert((J0:ideal(f1)) == J0);
assert((J1:ideal(f2)) == J1);
assert((J2:ideal(f3)) == J2);

-- Consequences of the three base equations.
assert((4 % G0) == 0);
assert((2*r % G0) == 0);
assert((2*s^2 % G0) == 0);
assert((r^4 % G0) == 0);
assert((s^5 % G0) == 0);

-- The coefficient which will occur in the fourth-power word survives.
assert((2*s % G0) != 0);

-- The quotient by (r,s) is F_2.  Together with nilpotence of r and s
-- above, this proves that C is local with maximal ideal (r,s)=(2,r,s).
assert(I0+ideal(r,s) == ideal(2,r,s));

-- Loewy filtration and socle.  These are equalities of ideals upstairs
-- in ZZ[r,s]; after quotienting by I0 they say
--   m^3=(2,r^2*s), m^4=(2*s), m^5=0,
-- and Soc(C)=F_2*(2*s).
m0 = ideal(r,s);
assert(I0+m0^3 == I0+ideal(2,r^2*s,2*s));
assert(I0+m0^4 == I0+ideal(2*s));
assert(I0+m0^5 == I0);
assert((I0:m0) == I0+ideal(2*s));

-- A useful deformation quotient.  The kernel m^3 is square-zero and
-- C/m^3 is exactly F_2[r,s]/(r,s)^3.  The still smaller socle ideal
-- (2s) is square-zero as well.
assert(I0+m0^3 == ideal(2)+m0^3);
assert(I0+(m0^3)*(m0^3) == I0);
assert((I0+ideal((2*s)^2)) == I0);
assert(I0+ideal((r*s)^2) == I0);
assert(((2*s*r) % G0) == 0);
assert(((2*s*s) % G0) == 0);

-- The claimed tangent cone has Hilbert function (1,2,3,2,1).
-- The ideal-power assertions above identify its successive layers with
-- those of C, while the strong Groebner basis below gives total length 9.
k2 = ZZ/2;
HC = k2[rr,ss,Degrees=>{1,1},MonomialOrder=>GRevLex]/ideal(rr*ss^2,rr^3+ss^3);
assert(apply(toList(0..5),i->hilbertFunction(i,HC)) == {1,2,3,2,1,0});

-- The strong Groebner basis printed below gives the additive normal form
--   (ZZ/4){1,s} + (ZZ/2){s^2,r,rs,r^2,r^2*s},
-- hence length 9.  It also gives a radical certificate: 4,r^4,s^5 lie
-- in I0 and I0 lies in (2,r,s).
assert(isSubset(I0,ideal(2,r,s)));
print "BASE PASS";
print "strong Groebner basis of the base ideal:";
print gens G0;

------------------------------------------------------------------------
-- 2. The rank-four algebra and its internal identities
------------------------------------------------------------------------

S = ZZ[U,V,r,s,MonomialOrder=>Lex];
Kbase = ideal(r^3+2,s^3+2,r*s^2);
qU = U^2-r^2*U+r*s*V;
qV = V^2-s^2*V;
K = Kbase+ideal(qU,qV);
G = gb K;

W = U*V;
theta = r*U+s*V+r*s*W;
lambda = 1+theta;
L = 1+r*U;
M = 1+s*V;

-- Freeness on 1,U,V,UV is formal: first quotient by the monic quadratic
-- in V, then by the monic quadratic in U.  The following checks the
-- multiplication and the nonzero socle class.
assert((Kbase:ideal(qV)) == Kbase);
assert(((Kbase+ideal(qV)):ideal(qU)) == Kbase+ideal(qV));
assert(((U*W-r^2*W) % G) == 0);
assert(((V*W-s^2*W) % G) == 0);
assert((W^2 % G) == 0);
assert((2*s*W % G) != 0);

-- lambda=1+theta is a unit infinitesimally close to 1.
assert(((M^2-1) % G) == 0);
assert(((L^2-1-2*s*V) % G) == 0);
assert((theta^2 % G) == 0);
assert(((2*theta-2*s*V) % G) == 0);
assert(((lambda^2-1-2*s*V) % G) == 0);
assert(((2*s*V) % G) != 0);
assert((lambda*(1-theta)-1) % G == 0);

-- The four auxiliary reductions recorded in Appendix A of the paper.
assert(((s^2*(lambda-1)+2*V) % G) == 0);
assert(((r*s*(lambda-1)-r^2*s*U) % G) == 0);
assert(((r*s*(lambda^2-1)) % G) == 0);
assert(((2*lambda*U+r^2*(lambda^2-lambda)+r^2*s*V) % G) == 0);

-- The fourth-power class is the full socle of the total coordinate ring.
n0 = ideal(r,s,U,V);
assert((K:n0) == K+ideal(2*s*W));
assert(K+n0 == ideal(2,r,s,U,V));

-- The special fiber is F_2[U,V]/(U^2,V^2), and lambda specializes to 1.
F = (ZZ/2)[u,v,MonomialOrder=>Lex];
toF = map(F,S,{u,v,0,0});
assert(toF(K) == ideal(u^2,v^2));
assert(toF(lambda) == 1);

-- The counit U,V |-> 0 is a well-defined algebra map A -> C.
epsA = map(R0,S,{0,0,R0_0,R0_1});
assert(epsA(K) == I0);

print "ALGEBRA PASS: free rank-four presentation, square-zero theta, socle";

------------------------------------------------------------------------
-- 3. Multiplication: preservation of the equations and group-likeness
------------------------------------------------------------------------

T = ZZ[U1,V1,U2,V2,r1,s1,MonomialOrder=>Lex];
IT = ideal(r1^3+2,s1^3+2,r1*s1^2,
           U1^2-r1^2*U1+r1*s1*V1,
           V1^2-s1^2*V1,
           U2^2-r1^2*U2+r1*s1*V2,
           V2^2-s1^2*V2);
GT = gb IT;

lambda1 = (1+r1*U1)*(1+s1*V1);
lambda2 = (1+r1*U2)*(1+s1*V2);
L1 = 1+r1*U1;
L2 = 1+r1*U2;
M1 = 1+s1*V1;
M2 = 1+s1*V2;

-- These are the product coordinates inherited from
--   (u,v,z)(u',v',z')=(u+z*u',v*z'+v',z*z').
deltaU = U1+lambda1*U2;
deltaV = V1*lambda2+V2;
deltaLambda = (1+r1*deltaU)*(1+s1*deltaV);

-- The two quadrics are preserved and lambda is group-like.
assert(((deltaU^2-r1^2*deltaU+r1*s1*deltaV) % GT) == 0);
assert(((deltaV^2-s1^2*deltaV) % GT) == 0);
assert(((deltaLambda-lambda1*lambda2) % GT) == 0);
DeltaMap = map(T,S,{deltaU,deltaV,r1,s1});
assert(isSubset(DeltaMap(K),IT));
-- The minimal character obstruction lambda^2-1=2sV is primitive.
assert(((2*s1*deltaV-2*s1*V1-2*s1*V2) % GT) == 0);

-- Two useful internal square-zero Hopf quotients.  Modulo theta=lambda-1,
-- both coordinates become primitive.  The primitive source 2sV also
-- generates a Hopf ideal, whereas the final defect ideal (2sW) does not.
GmodThetaT = gb(IT+ideal(lambda1-1,lambda2-1));
assert(((deltaLambda-1) % GmodThetaT) == 0);
assert(((deltaU-U1-U2) % GmodThetaT) == 0);
assert(((deltaV-V1-V2) % GmodThetaT) == 0);
deltaW = deltaU*deltaV;
primitiveWFormula = 2*s1*(U1*V1+U1*V2+V1*U2+U2*V2);
assert(((2*s1*deltaW-primitiveWFormula) % GT) == 0);
GdefectTensor = gb(IT+ideal(2*s1*U1*V1,2*s1*U2*V2));
assert((2*s1*deltaW % GdefectTensor) != 0);

-- The displayed graph-factorization from the paper also reduces exactly.
E = r1*s1*V1*U2;
graphRHS = L1*M2*E*(2+r1*U2+s1*V1+E);
assert(((deltaLambda-lambda1*lambda2-graphRHS) % GT) == 0);

-- Both counit identities on U,V and on the group-like element lambda.
-- leftEps applies epsilon to the first tensor factor, while rightEps
-- applies it to the second.
leftEps  = map(S,T,{0,0,U,V,r,s});
rightEps = map(S,T,{U,V,0,0,r,s});
assert(isSubset(leftEps(IT),K));
assert(isSubset(rightEps(IT),K));
assert(((leftEps(deltaU)-U) % G) == 0);
assert(((leftEps(deltaV)-V) % G) == 0);
assert(((leftEps(deltaLambda)-lambda) % G) == 0);
assert(((rightEps(deltaU)-U) % G) == 0);
assert(((rightEps(deltaV)-V) % G) == 0);
assert(((rightEps(deltaLambda)-lambda) % G) == 0);

-- The coproduct is not cocommutative.  The second equality records the
-- conceptual defect theta tensor U - U tensor theta.
opDeltaU = U2+lambda2*U1;
theta1 = lambda1-1;
theta2 = lambda2-1;
assert(((deltaU-opDeltaU-(theta1*U2-U1*theta2)) % GT) == 0);
assert(((deltaU-opDeltaU) % GT) != 0);

print "MULTIPLICATION PASS: both quadrics and the graph equation are closed";
print "COUNIT PASS";
print "NONCOMMUTATIVITY PASS: Delta(U) is not cocommutative";

------------------------------------------------------------------------
-- 4. A direct three-factor associativity check
------------------------------------------------------------------------

Q = ZZ[X1,Y1,X2,Y2,X3,Y3,r2,s2,MonomialOrder=>GRevLex];
IQ = ideal(r2^3+2,s2^3+2,r2*s2^2,
           X1^2-r2^2*X1+r2*s2*Y1,Y1^2-s2^2*Y1,
           X2^2-r2^2*X2+r2*s2*Y2,Y2^2-s2^2*Y2,
           X3^2-r2^2*X3+r2*s2*Y3,Y3^2-s2^2*Y3);
GQ = gb IQ;

l1 = (1+r2*X1)*(1+s2*Y1);
l2 = (1+r2*X2)*(1+s2*Y2);
l3 = (1+r2*X3)*(1+s2*Y3);

x12 = X1+l1*X2;
y12 = Y1*l2+Y2;
l12 = (1+r2*x12)*(1+s2*y12);

x23 = X2+l2*X3;
y23 = Y2*l3+Y3;
l23 = (1+r2*x23)*(1+s2*y23);

xLeft  = x12+l12*X3;
yLeft  = y12*l3+Y3;
xRight = X1+l1*x23;
yRight = Y1*l23+y23;

assert(((xLeft-xRight) % GQ) == 0);
assert(((yLeft-yRight) % GQ) == 0);
print "ASSOCIATIVITY PASS";

------------------------------------------------------------------------
-- 5. Antipode
------------------------------------------------------------------------

lambdaInv = 1-theta;
SU = (-lambdaInv*U) % G;
SV = (-V*lambdaInv) % G;
SW = (SU*SV) % G;
Slambda = (1+r*SU+s*SV+r*s*SW) % G;

-- Explicit formulas from the paper.
assert(((SU-(U-s*W+r^2*s*V)) % G) == 0);
assert(((SV-(V+r*W)) % G) == 0);

-- The antipode respects the quadrics and sends lambda to lambda^{-1}.
assert(((SU^2-r^2*SU+r*s*SV) % G) == 0);
assert(((SV^2-s^2*SV) % G) == 0);
assert(((Slambda-lambdaInv) % G) == 0);
Smap = map(S,S,{SU,SV,r,s});
assert(isSubset(Smap(K),K));

-- Left and right convolution identities on the algebra generators.
assert(((SU+Slambda*U) % G) == 0);
assert(((U+lambda*SU) % G) == 0);
assert(((SV*lambda+V) % G) == 0);
assert(((V*Slambda+SV) % G) == 0);

-- Antipode stability for the two internal square-zero Hopf ideals.
GmodTheta = gb(K+ideal(theta));
assert(((Slambda-1) % GmodTheta) == 0);
assert((((2*s*V)^2) % G) == 0);
assert(((2*s*SV+2*s*V) % G) == 0);
print "ANTIPODE PASS";

------------------------------------------------------------------------
-- 6. The fourth- and eighth-power words
------------------------------------------------------------------------

-- First check the conceptual geometric sums.
N4 = 1+lambda+lambda^2+lambda^3;
N8 = N4+lambda^4*N4;
assert(((N4-2*s*V) % G) == 0);
assert(((lambda^4-1) % G) == 0);
assert((N8 % G) == 0);

-- Then compute the word maps directly by iterating the square word
-- phi=m o Delta.  The map fixes the base variables r,s.
phiU = ((1+lambda)*U) % G;
phiV = (V*(1+lambda)) % G;
phi = map(S,S,{phiU,phiV,r,s});

fourU = phi(phiU) % G;
fourV = phi(phiV) % G;
eightU = phi(fourU) % G;
eightV = phi(fourV) % G;
fourW = (fourU*fourV) % G;

assert(fourU == 2*s*W);
assert(fourV == 0);
assert(fourW == 0);
assert(eightU == 0);
assert(eightV == 0);

-- Modulo the square-zero ideal m^3 of the base, doubling becomes
--     U |-> sW,  V |-> rW,  W |-> 0,
-- so its square is the unit word.  Over C itself the correction term
-- -r^2*s*V in [2](U) produces the carry 2sW on squaring again.
assert(phiU == ((-s*W-r^2*s*V) % G));
assert(phiV == (r*W % G));
assert(((phiU*phiV) % G) == 0);
GmodM3 = gb(K+ideal(2,r^2*s));
assert(((phiU-s*W) % GmodM3) == 0);
assert(((phiV-r*W) % GmodM3) == 0);
assert((s*W % GmodM3) != 0);
assert((fourU % GmodM3) == 0);
assert((fourV % GmodM3) == 0);

-- Modulo the square-zero bridge ideal (rs), the algebra is the tensor
-- product of its two rank-two factors.  L=1+rU and M=1+sV become
-- separate group-like involutions; only their product is group-like
-- before this reduction.
GmodBridge = gb(K+ideal(r*s));
GTmodBridge = gb(IT+ideal(r1*s1));
deltaL = 1+r1*deltaU;
deltaM = 1+s1*deltaV;
assert(((deltaL-L1*L2-r1*s1*L1*V1*U2) % GT) == 0);
assert(((deltaM-M1*M2-r1*s1*V1*U2*M2) % GT) == 0);
assert(((L^2-1) % GmodBridge) == 0);
assert(((M^2-1) % GmodBridge) == 0);
assert(((deltaL-L1*L2) % GTmodBridge) == 0);
assert(((deltaM-M1*M2) % GTmodBridge) == 0);
assert(((phiU-s*W) % GmodBridge) == 0);
assert(((phiV-r*W) % GmodBridge) == 0);
assert((fourU % GmodBridge) == 0);
assert(((2*s) % GmodBridge) == 0);
assert(((2*s*W+r^2*(r*s)*W) % G) == 0);

-- If one lifts the bridge-free tensor-product algebra from C/(rs) to C
-- while naively keeping beta=0, exactly one bialgebra relation fails.
-- Its curvature is rq V_1 U_2, where q=rs.  The bridge beta=-q cancels
-- this term.
Tnaive = ZZ[Un1,Vn1,Un2,Vn2,rn,sn,MonomialOrder=>Lex];
Inaive = ideal(rn^3+2,sn^3+2,rn*sn^2,
               Un1^2-rn^2*Un1,Vn1^2-sn^2*Vn1,
               Un2^2-rn^2*Un2,Vn2^2-sn^2*Vn2);
Gnaive = gb Inaive;
ln1 = (1+rn*Un1)*(1+sn*Vn1);
ln2 = (1+rn*Un2)*(1+sn*Vn2);
dUn = Un1+ln1*Un2;
dVn = Vn1*ln2+Vn2;
dln = (1+rn*dUn)*(1+sn*dVn);
assert(((dUn^2-rn^2*dUn-rn^2*sn*Vn1*Un2) % Gnaive) == 0);
assert(((dVn^2-sn^2*dVn) % Gnaive) == 0);
assert(((dln-ln1*ln2) % Gnaive) == 0);
assert(((rn^2*sn*Vn1*Un2) % Gnaive) != 0);

-- On the first infinitesimal neighborhood C/m^2, the algebra is
-- F_2[r,s]/(r,s)^2[U,V]/(U^2,V^2), and the coproduct is the primitive
-- coproduct plus the two displayed first-order bialgebra cocycles.
Gfirst = gb(K+ideal(2,r^2,r*s,s^2));
GTfirst = gb(IT+ideal(2,r1^2,r1*s1,s1^2));
assert((U^2 % Gfirst) == 0);
assert((V^2 % Gfirst) == 0);
assert(((deltaU-(U1+U2+r1*U1*U2+s1*V1*U2)) % GTfirst) == 0);
assert(((deltaV-(V1+V2+r1*V1*U2+s1*V1*V2)) % GTfirst) == 0);

-- The minimal quotient killing the fourth-power defect is the
-- square-zero socle quotient C/(2s).  The difference [4]-e is the
-- nonzero e-derivation d(U)=2sW, d(V)=0; these are its linearized
-- relation checks at the identity.
GmodSoc = gb(K+ideal(2*s));
GbaseModSoc = gb(I0+ideal(2*R0_1));
assert((2 % GbaseModSoc) != 0);
assert((fourU % GmodSoc) == 0);
assert((fourV % GmodSoc) == 0);
assert((phiU % GmodSoc) != 0);
assert(((lambda^2-1) % GmodSoc) == 0);
assert((N4 % GmodSoc) == 0);
dU = fourU;
dV = fourV;
assert(((r^2*dU-r*s*dV) % G) == 0);
assert(((s^2*dV) % G) == 0);

-- The inverse obtained abstractly as the seventh-power word agrees with
-- the explicit antipode.
N7 = 1+lambda+lambda^2+lambda^3+lambda^4+lambda^5+lambda^6;
sevenU = (N7*U) % G;
sevenV = (V*N7) % G;
assert(sevenU == SU);
assert(sevenV == SV);

-- The ideal (V) defines the rank-two subgroup: it is stable under
-- coproduct, counit, and antipode.  Its square word is the unit word.
GH0T = gb(IT+ideal(V1,V2));
GH0 = gb(K+ideal(V));
assert((deltaV % GH0T) == 0);
assert(epsA(V) == 0);
assert((SV % GH0) == 0);
assert((phiU % GH0) == 0);

-- This subgroup is nonnormal: the following is the nonzero universal
-- coefficient in the V-coordinate of conjugation.
assert(((r*V-r^2*W) % G) != 0);

print "POWER WORDS ([4]U,[4]V,[8]U,[8]V):";
print fourU;
print fourV;
print eightU;
print eightV;
print "NONNORMAL RANK-TWO SUBGROUP PASS";
print "SQUARE-ZERO DEFORMATION PASS";
print "ALL CHECKS PASSED";
