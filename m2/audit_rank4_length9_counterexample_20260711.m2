-- Independent, bounded audit of the length-nine rank-four example.
-- Run locally with:
--   M2 --script m2/audit_rank4_length9_counterexample_20260711.m2

-- Base and coordinate algebra.  Lex order with U,V first makes the
-- rank-four normal forms especially transparent.
S = ZZ[U,V,x,y,MonomialOrder => Lex];
IR = ideal(x^3,y^3,x*y^2-2);
K = IR + ideal(U^2-x*y*U-x^2*V,V^2-y^2*V);
GR = gb IR;
G = gb K;

assert((4 % GR) == 0);
assert((2 % GR) != 0);
assert((2*x % GR) != 0);

theta = y*U+x*V+x*y*U*V;
lambda = 1+theta;
assert((theta^2 % G) == 0);
assert(((lambda*(1-theta)-1) % G) == 0);

-- The squaring word phi=[2]^# is multiplication after the coproduct.
phiU = (U+lambda*U) % G;
phiV = (V*lambda+V) % G;
phiW = (phiU*phiV) % G;
assert(((phiU-(x^2*y*V-x*U*V)) % G) == 0);
assert(((phiV+y*U*V) % G) == 0);
assert(phiW == 0);

phi = map(S,S,{phiU,phiV,x,y});
fourU = phi(phiU) % G;
fourV = phi(phiV) % G;
eightU = phi(fourU) % G;
eightV = phi(fourV) % G;
assert(fourU == 2*x*U*V);
assert(fourV == 0);
assert((fourU % G) != 0);
assert(eightU == 0);
assert(eightV == 0);

-- Check that the displayed coproduct descends to A tensor_R A and that
-- lambda is group-like.  These are literal ideal-membership tests over ZZ.
T = ZZ[U1,V1,U2,V2,x1,y1,MonomialOrder => Lex];
JT = ideal(
    x1^3,y1^3,x1*y1^2-2,
    U1^2-x1*y1*U1-x1^2*V1,V1^2-y1^2*V1,
    U2^2-x1*y1*U2-x1^2*V2,V2^2-y1^2*V2
    );
GT = gb JT;
lambda1 = 1+y1*U1+x1*V1+x1*y1*U1*V1;
lambda2 = 1+y1*U2+x1*V2+x1*y1*U2*V2;
deltaU = U1+lambda1*U2;
deltaV = V1*lambda2+V2;
deltaLambda = 1+y1*deltaU+x1*deltaV+x1*y1*deltaU*deltaV;
assert(((deltaU^2-x1*y1*deltaU-x1^2*deltaV) % GT) == 0);
assert(((deltaV^2-y1^2*deltaV) % GT) == 0);
assert(((deltaLambda-lambda1*lambda2) % GT) == 0);
swapDeltaU = U2+lambda2*U1;
assert(((deltaU-swapDeltaU) % GT) != 0);

-- Direct antipode checks in A.
lambdaInv = 1-theta;
SU = (-lambdaInv*U) % G;
SV = (-V*lambdaInv) % G;
SW = (SU*SV) % G;
Slambda = (1+y*SU+x*SV+x*y*SW) % G;
assert(((SU^2-x*y*SU-x^2*SV) % G) == 0);
assert(((SV^2-y^2*SV) % G) == 0);
assert(((Slambda-lambdaInv) % G) == 0);
assert(((SU+Slambda*U) % G) == 0);
assert(((U+lambda*SU) % G) == 0);
assert(((SV*lambda+V) % G) == 0);
assert(((V*Slambda+SV) % G) == 0);

print "BASE STRONG GROEBNER BASIS:";
print gens GR;
print "NONZERO NORMAL FORMS:";
print (2 % GR);
print (2*x % GR);
print (2*x*U*V % G);
print "POWER NORMAL FORMS ([2]U,[2]V,[2]UV,[4]U,[4]V,[8]U,[8]V):";
print phiU;
print phiV;
print phiW;
print fourU;
print fourV;
print eightU;
print eightV;
print "COPRODUCT, GROUP-LIKE, AND ANTIPODE REMAINDERS: ALL ZERO";
print "NONCOCOMMUTATIVITY REMAINDER:";
print ((deltaU-swapDeltaU) % GT);
print "ALL INDEPENDENT MACAULAY2 AUDITS PASSED";
