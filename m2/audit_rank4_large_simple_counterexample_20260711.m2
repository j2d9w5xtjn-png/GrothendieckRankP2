-- A deliberately redundant five-parameter rank-four counterexample.
-- Run locally with:
--   M2 --script m2/audit_rank4_large_simple_counterexample_20260711.m2

S = ZZ[a,b,c,p,q, MonomialOrder=>GRevLex];
IB = ideal(
     4,
     2*p, 2*a, 2*b, 2*c,
     p^3, q^3, b^2, c^2, a*b, a*c, c*p, b*q,
     a*p-2, c*q-2, b*p-a*q, a^2-2*q, b*c-2*q
     );
GB = gb IB;
assert((2*q % GB) != 0);

-- The coordinate algebra and the norm identities.
SA = ZZ[a,b,c,p,q,U,V, MonomialOrder=>GRevLex];
IA = ideal(
     4,
     2*p, 2*a, 2*b, 2*c,
     p^3, q^3, b^2, c^2, a*b, a*c, c*p, b*q,
     a*p-2, c*q-2, b*p-a*q, a^2-2*q, b*c-2*q,
     U^2-a*U-b*V, V^2-c*V
     );
GA = gb IA;
W = U*V;
theta = p*U+q*V+p*q*W;
lambda = 1+theta;
assert((theta^2 % GA) == 0);
assert(((2*theta-2*q*V) % GA) == 0);
assert(((lambda*(1-theta)-1) % GA) == 0);

N4 = sum(0..3,i -> lambda^i);
N8 = sum(0..7,i -> lambda^i);
assert(((N4-2*q*V) % GA) == 0);
assert(((N4*U-2*q*W) % GA) == 0);
assert(((V*N4) % GA) == 0);
assert((2*q*W % GA) != 0);
assert((N8 % GA) == 0);

-- An explicit antipode.
SU = U+b*p*V-q*W;
SV = V+p*W;
SW = SU*SV;
Slambda = 1+p*SU+q*SV+p*q*SW;
assert(((SU^2-a*SU-b*SV) % GA) == 0);
assert(((SV^2-c*SV) % GA) == 0);
assert(((Slambda-(1-theta)) % GA) == 0);
assert(((SU+Slambda*U) % GA) == 0);
assert(((U+lambda*SU) % GA) == 0);
assert(((SV*lambda+V) % GA) == 0);
assert(((V*Slambda+SV) % GA) == 0);

-- Tensor-square audit: preservation of the two quadrics and group-likeness
-- of lambda.  These are precisely the nonformal bialgebra checks.
ST = ZZ[U1,V1,U2,V2,a,b,c,p,q, MonomialOrder=>Lex];
IT = ideal(
     4,
     2*p, 2*a, 2*b, 2*c,
     p^3, q^3, b^2, c^2, a*b, a*c, c*p, b*q,
     a*p-2, c*q-2, b*p-a*q, a^2-2*q, b*c-2*q,
     U1^2-a*U1-b*V1, V1^2-c*V1,
     U2^2-a*U2-b*V2, V2^2-c*V2
     );
GT = gb IT;
lambda1 = (1+p*U1)*(1+q*V1);
lambda2 = (1+p*U2)*(1+q*V2);
deltaU = U1+lambda1*U2;
deltaV = V1*lambda2+V2;
deltaLambda = (1+p*deltaU)*(1+q*deltaV);
assert(((deltaU^2-a*deltaU-b*deltaV) % GT) == 0);
assert(((deltaV^2-c*deltaV) % GT) == 0);
assert(((deltaLambda-lambda1*lambda2) % GT) == 0);

-- The coproduct is genuinely noncocommutative.
swapDeltaU = U2+lambda2*U1;
assert(((deltaU-swapDeltaU) % GT) != 0);

<< "PASS large simple rank-four audit" << endl;
<< "[4]#(U) = 2*q*U*V != 0; [4]#(V) = 0; [8] = e" << endl;
