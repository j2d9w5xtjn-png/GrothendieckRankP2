-- Exact audit of the deliberately unoptimized five-coefficient bridge over
-- its untruncated coefficient ring.
-- Run on the local Mac with:
--   M2 --script m2/audit_rank4_unoptimized_bridge_20260711.m2

-- First audit the coefficient ring itself.
B0 = ZZ[al,be,ga,r,s,MonomialOrder=>Lex];
IB = ideal(al*r+2,ga*s+2,ga*r,be*s,be*r+al*s);
GB = gb IB;
assert((4 % GB) == 0);
assert((2*s % GB) != 0);
carryNormalForm = 2*s % GB;

print "UNTRUNCATED COEFFICIENT-RING PASS";
print "NONZERO CARRY 2s:";
print carryNormalForm;

-- Audit the human-sized three-coefficient specialization
--   D = ZZ[r,s,g]/(r^2*s+2,s^3,g*s+2,g*r),
-- with al=r*s, be=s^2, ga=g.
D0 = ZZ[gd,rd,sd,MonomialOrder=>Lex];
ID = ideal(rd^2*sd+2,sd^3,gd*sd+2,gd*rd);
GD = gb ID;
ald = rd*sd;
bed = sd^2;
assert(((ald*rd+2) % GD) == 0);
assert(((gd*sd+2) % GD) == 0);
assert(((gd*rd) % GD) == 0);
assert(((bed*sd) % GD) == 0);
assert(((bed*rd+ald*sd) % GD) == 0);
assert(((2*sd) % GD) != 0);
print "THREE-COEFFICIENT UNTRUNCATED SPECIALIZATION PASS";

-- Coordinate algebra, free on 1,U,V,W=UV by successive monic reduction.
S = ZZ[U,V,al,be,ga,r,s,MonomialOrder=>Lex];
Ibase = ideal(al*r+2,ga*s+2,ga*r,be*s,be*r+al*s);
K = Ibase + ideal(U^2-al*U-be*V,V^2-ga*V);
G = gb K;
W = U*V;
theta = r*U+s*V+r*s*W;
lambda = 1+theta;

assert((2*s*W % G) != 0);
assert((theta^2 % G) == 0);
assert(((2*theta-2*s*V) % G) == 0);
assert(((lambda*(1-theta)-1) % G) == 0);

-- Product coordinates in A tensor_B A.  Their closure is precisely
-- multiplicativity of the coproduct and group-likeness of lambda.
T = ZZ[U1,V1,U2,V2,al1,be1,ga1,r1,s1,MonomialOrder=>Lex];
IT = ideal(al1*r1+2,ga1*s1+2,ga1*r1,be1*s1,
           be1*r1+al1*s1) + ideal(
           U1^2-al1*U1-be1*V1,V1^2-ga1*V1,
           U2^2-al1*U2-be1*V2,V2^2-ga1*V2);
GT = gb IT;
lambda1 = 1+r1*U1+s1*V1+r1*s1*U1*V1;
lambda2 = 1+r1*U2+s1*V2+r1*s1*U2*V2;
deltaU = U1+lambda1*U2;
deltaV = V1*lambda2+V2;
deltaLambda = 1+r1*deltaU+s1*deltaV+r1*s1*deltaU*deltaV;

assert(((deltaU^2-al1*deltaU-be1*deltaV) % GT) == 0);
assert(((deltaV^2-ga1*deltaV) % GT) == 0);
assert(((deltaLambda-lambda1*lambda2) % GT) == 0);

-- Antipode and both convolution identities.
lambdaInv = 1-theta;
SU = (-lambdaInv*U) % G;
SV = (-V*lambdaInv) % G;
SW = (SU*SV) % G;
Slambda = (1+r*SU+s*SV+r*s*SW) % G;
assert(((SU-(U-s*W+al*s*V)) % G) == 0);
assert(((SV-(V+r*W)) % G) == 0);
assert(((SU^2-al*SU-be*SV) % G) == 0);
assert(((SV^2-ga*SV) % G) == 0);
assert(((Slambda-lambdaInv) % G) == 0);
assert(((SU+Slambda*U) % G) == 0);
assert(((U+lambda*SU) % G) == 0);
assert(((SV*lambda+V) % G) == 0);
assert(((V*Slambda+SV) % G) == 0);

-- Power words.
phiU = (U+lambda*U) % G;
phiV = (V*lambda+V) % G;
phi = map(S,S,{phiU,phiV,al,be,ga,r,s});
fourU = phi(phiU) % G;
fourV = phi(phiV) % G;
eightU = phi(fourU) % G;
eightV = phi(fourV) % G;
assert(fourU == 2*s*U*V);
assert(fourV == 0);
assert(eightU == 0);
assert(eightV == 0);

print "HOPF PASS: both quadrics, group-like bridge, coassociativity, antipode";
print "POWER NORMAL FORMS ([2]U,[2]V,[4]U,[4]V,[8]U,[8]V):";
print phiU;
print phiV;
print fourU;
print fourV;
print eightU;
print eightV;

-- Over C -> C/(rs), all framed lifts in the triangular chart with r,s
-- fixed have
--   alpha=r^2+ea*(2s), gamma=s^2+ec*(2s),
--   beta=-rs+ej*(2s),  ea,ec,ej in {0,1}.
-- The identity r^2*(rs)=-2s lets us use top=r^2*(rs).
-- Check all eight choices, including Hopf closure and the common carry.
scan({0,1},ea->scan({0,1},ec->scan({0,1},ej->(
 R8:=ZZ[X1,Y1,X2,Y2,rr,ss,MonomialOrder=>Lex];
 qq:=rr*ss;
 top:=rr^2*qq;
 aa:=rr^2+ea*top;
 cc:=ss^2+ec*top;
 bb:=-qq+ej*top;
 I8:=ideal(rr^3+2,ss^3+2,rr*ss^2,
           X1^2-aa*X1-bb*Y1,Y1^2-cc*Y1,
           X2^2-aa*X2-bb*Y2,Y2^2-cc*Y2);
 G8:=gb I8;
 l8a:=(1+rr*X1)*(1+ss*Y1);
 l8b:=(1+rr*X2)*(1+ss*Y2);
 dX:=X1+l8a*X2;
 dY:=Y1*l8b+Y2;
 dl8:=(1+rr*dX)*(1+ss*dY);
 assert((dX^2-aa*dX-bb*dY)%G8==0);
 assert((dY^2-cc*dY)%G8==0);
 assert((dl8-l8a*l8b)%G8==0);
 assert((((1+l8a+l8a^2+l8a^3)*X1)-2*ss*X1*Y1)%G8==0);
 ))));

print "ALL EIGHT TRIANGULAR SQUARE-ZERO LIFTS PASS";
print "ALL UNOPTIMIZED-BRIDGE AUDITS PASSED";
