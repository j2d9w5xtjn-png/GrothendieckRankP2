-- Exact audit of the three-relation rank-four counterexample.
-- Run on the local Mac with:
--   M2 --script m2/audit_rank4_three_relation_counterexample_20260711.m2

-- Base ring R = ZZ[r,s]/(r^3+2,s^3+2,r*s^2).
R0 = ZZ[r,s,MonomialOrder=>Lex];
IR = ideal(r^3+2,s^3+2,r*s^2);
GR = gb IR;
assert((4 % GR) == 0);
assert((2*r % GR) == 0);
assert((2*s^2 % GR) == 0);
assert((2*s % GR) != 0);
print "BASE PASS: three relations, with nonzero carry 2s";
print "STRONG GROEBNER BASIS:";
print gens GR;

-- Coordinate algebra, free on 1,U,V,W=UV by successive monic reduction.
S = ZZ[U,V,r,s,MonomialOrder=>Lex];
Ibase = ideal(r^3+2,s^3+2,r*s^2);
K = Ibase + ideal(U^2-r^2*U+r*s*V,V^2-s^2*V);
G = gb K;
W = U*V;
theta = r*U+s*V+r*s*W;
lambda = 1+theta;

assert((2*s*W % G) != 0);
assert((theta^2 % G) == 0);
assert(((2*theta-2*s*V) % G) == 0);
assert(((lambda*(1-theta)-1) % G) == 0);

-- Product coordinates in A tensor_R A.
T = ZZ[U1,V1,U2,V2,r1,s1,MonomialOrder=>Lex];
IT = ideal(r1^3+2,s1^3+2,r1*s1^2,
           U1^2-r1^2*U1+r1*s1*V1,V1^2-s1^2*V1,
           U2^2-r1^2*U2+r1*s1*V2,V2^2-s1^2*V2);
GT = gb IT;
lambda1 = 1+r1*U1+s1*V1+r1*s1*U1*V1;
lambda2 = 1+r1*U2+s1*V2+r1*s1*U2*V2;
deltaU = U1+lambda1*U2;
deltaV = V1*lambda2+V2;
deltaLambda = 1+r1*deltaU+s1*deltaV+r1*s1*deltaU*deltaV;

assert(((deltaU^2-r1^2*deltaU+r1*s1*deltaV) % GT) == 0);
assert(((deltaV^2-s1^2*deltaV) % GT) == 0);
assert(((deltaLambda-lambda1*lambda2) % GT) == 0);

-- A direct three-factor associativity check, independent of the formal
-- group-like/skew-primitive argument.
Q = ZZ[X1,Y1,X2,Y2,X3,Y3,r2,s2,MonomialOrder=>GRevLex];
IQ = ideal(r2^3+2,s2^3+2,r2*s2^2,
           X1^2-r2^2*X1+r2*s2*Y1,Y1^2-s2^2*Y1,
           X2^2-r2^2*X2+r2*s2*Y2,Y2^2-s2^2*Y2,
           X3^2-r2^2*X3+r2*s2*Y3,Y3^2-s2^2*Y3);
GQ = gb IQ;
l1 = 1+r2*X1+s2*Y1+r2*s2*X1*Y1;
l2 = 1+r2*X2+s2*Y2+r2*s2*X2*Y2;
l3 = 1+r2*X3+s2*Y3+r2*s2*X3*Y3;
x12 = X1+l1*X2;
y12 = Y1*l2+Y2;
l12 = 1+r2*x12+s2*y12+r2*s2*x12*y12;
x23 = X2+l2*X3;
y23 = Y2*l3+Y3;
l23 = 1+r2*x23+s2*y23+r2*s2*x23*y23;
xLeft = x12+l12*X3;
yLeft = y12*l3+Y3;
xRight = X1+l1*x23;
yRight = Y1*l23+y23;
assert(((xLeft-xRight) % GQ) == 0);
assert(((yLeft-yRight) % GQ) == 0);

-- Antipode and convolution identities.
lambdaInv = 1-theta;
SU = (-lambdaInv*U) % G;
SV = (-V*lambdaInv) % G;
SW = (SU*SV) % G;
Slambda = (1+r*SU+s*SV+r*s*SW) % G;
assert(((SU-(U-s*W+r^2*s*V)) % G) == 0);
assert(((SV-(V+r*W)) % G) == 0);
assert(((SU^2-r^2*SU+r*s*SV) % G) == 0);
assert(((SV^2-s^2*SV) % G) == 0);
assert(((Slambda-lambdaInv) % G) == 0);
assert(((SU+Slambda*U) % G) == 0);
assert(((U+lambda*SU) % G) == 0);
assert(((SV*lambda+V) % G) == 0);
assert(((V*Slambda+SV) % G) == 0);

-- Power words.
phiU = (U+lambda*U) % G;
phiV = (V*lambda+V) % G;
phi = map(S,S,{phiU,phiV,r,s});
fourU = phi(phiU) % G;
fourV = phi(phiV) % G;
eightU = phi(fourU) % G;
eightV = phi(fourV) % G;
assert(fourU == 2*s*U*V);
assert(fourV == 0);
assert(eightU == 0);
assert(eightV == 0);

print "HOPF PASS: quadrics, group-like bridge, direct associativity, antipode";
print "POWER NORMAL FORMS ([4]U,[4]V,[8]U,[8]V):";
print fourU;
print fourV;
print eightU;
print eightV;
print "ALL THREE-RELATION AUDITS PASSED";
