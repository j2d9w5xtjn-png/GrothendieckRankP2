-- Exact bounded audit of the uniform rank-p^2 construction at p=5.
--
-- This is a representative odd-prime check.  It verifies the two actual
-- monic relation defects, group-likeness of the exact-ratio character,
-- its inverse, and the [25] carry.  The arbitrary-prime proof is in
-- notes/A_RANK_P_SQUARED_COUNTEREXAMPLE_FOR_EVERY_PRIME_2026-07-12.tex.

T = ZZ[U1,V1,U2,V2,a,b,MonomialOrder=>Lex];

Wa = u -> u + 2*a*u^2 + 2*a^2*u^3 + a^3*u^4;
Wb = v -> v + 2*b*v^2 + 2*b^2*v^3 + b^3*v^4;
FF = (u,v) -> u^5-a*b^4*Wa(u)+b^5*Wb(v);
GG = v -> v^5-a^5*Wb(v);
Sp = x -> x+2*x^2+2*x^3+x^4;

I = ideal(a^6,b^9,a^5*b^4+5,
          FF(U1,V1),GG(V1),FF(U2,V2),GG(V2));
GI = gb I;

L = u -> 1+a*u;
M = v -> 1+b*v;
lambda = (u,v) -> L(u)*(M(v))^4;
lambdaInv = (u,v) -> M(v)*(L(u))^4*(1-5*Sp(b*v));

lambda1 = lambda(U1,V1);
lambda2 = lambda(U2,V2);
lambdaInv1 = lambdaInv(U1,V1);
lambdaInv2 = lambdaInv(U2,V2);

assert(((lambda1*lambdaInv1-1) % GI) == 0);
assert(((lambda2*lambdaInv2-1) % GI) == 0);

Ustar = U1+lambda1*U2;
Vstar = V1*lambdaInv2+V2;

defectF = FF(Ustar,Vstar) % GI;
defectG = GG(Vstar) % GI;
defectLambda = (lambda(Ustar,Vstar)-lambda1*lambda2) % GI;

assert(defectF == 0);
assert(defectG == 0);
assert(defectLambda == 0);

assert((((M(V1))^5-1) % GI) == 0);
assert((((L(U1))^5-(1+5*Sp(b*V1))) % GI) == 0);

N25 = 0;
power25 = 1;
for j from 0 to 24 do (
    N25 = (N25+power25) % GI;
    power25 = (power25*lambda1) % GI;
    );
assert(((power25-1) % GI) == 0);

N25Inv = 0;
power25Inv = 1;
for j from 0 to 24 do (
    N25Inv = (N25Inv+power25Inv) % GI;
    power25Inv = (power25Inv*lambdaInv1) % GI;
    );
assert(((power25Inv-1) % GI) == 0);
carry = (5*b^4*U1*V1^4) % GI;

assert(((N25-5*b^4*V1^4) % GI) == 0);
assert(((N25*U1-carry) % GI) == 0);
assert(carry != 0);
assert(((N25Inv*V1) % GI) == 0);
assert(((5*N25) % GI) == 0);
assert(((5*N25Inv) % GI) == 0);

print "p=5 closure defects (F,G,lambda):";
print defectF;
print defectG;
print defectLambda;
print "p=5 [25] carry:";
print carry;
print "ALL UNIFORM p=5 ASSERTIONS PASSED";
exit 0;
