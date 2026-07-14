-- Companion audit for the rank-four affine-group counterexample.
--
-- This file is intentionally organized by mathematical claim rather than by
-- implementation detail.  Every equality is checked by exact strong
-- Groebner reduction over ZZ (except for the explicitly indicated special
-- fiber over GF(2)).  No floating-point calculation is used.
--
-- Run from the project root on the local Mac with
--
--   M2 --script m2/verify_rank4_affine_article_20260712.m2
--
-- Tested with Macaulay2 1.25.11.

pass = s -> print ("PASS " | s);

------------------------------------------------------------------------
-- 1.  The base ring
--
-- R = ZZ[a,b]/(a^3,b^3,a^2*b+2),  q=b^2.
------------------------------------------------------------------------

RB = ZZ[a,b,MonomialOrder=>Lex];
IR = ideal(a^3,b^3,a^2*b+2);
GR = gb IR;
q = b^2;

expectedBaseLeadingTerms = matrix{{4,2*b^2,b^3,2*a,a^2*b,a^3}};
assert(leadTerm gens GR-expectedBaseLeadingTerms == 0);

assert((4 % GR) == 0);
assert((2 % GR) != 0);
assert((2*b % GR) != 0);
assert((q % GR) != 0);
assert((a*q % GR) != 0);
assert((a^2*q % GR) != 0);
assert(((a^2*q+2*b) % GR) == 0);
assert((q^2 % GR) == 0);
assert((b*q % GR) == 0);
assert((2*q % GR) == 0);

-- The displayed seven additive generators have exactly
-- 4^2*2^5=512 distinct normal forms.  The strong basis printed below,
-- together with a^3=b^3=0 and a^2*b=-2, shows that they also span.
-- Thus #R=512=2^9, i.e. length(R)=9 at its F_2-valued closed point.
twoTorsion = {a,a^2,a*b,b^2,a*b^2};
baseRepresentative = i -> (
     (i % 4)
     + ((i // 4) % 4)*b
     + sum(0..4,j -> ((i // (16*2^j)) % 2)*twoTorsion#j)
     );
baseNormalForms = toList apply(0..511,i -> baseRepresentative(i) % GR);
assert(#unique baseNormalForms == 512);

-- The m-adic sizes give Hilbert function (1,2,3,2,1).
mR = ideal(a,b);
filtrationSizes = toList apply(0..5,k -> (
          Gk := gb(IR+mR^k);
          #select(baseNormalForms,f -> ((f % Gk) == 0))
          ));
assert(filtrationSizes == {512,256,64,8,2,1});

-- m is nilpotent, R/m=F_2, and the socle consists of 0 and 2b.
assert(all(flatten entries gens(mR^5),f -> ((f % GR) == 0)));
Gresidue = gb(IR+mR);
assert((2 % Gresidue) == 0);
socleNormalForms = select(baseNormalForms,f ->
     (((a*f) % GR) == 0) and (((b*f) % GR) == 0));
assert(#socleNormalForms == 2);
assert(member(0_RB,socleNormalForms));
assert(member((2*b) % GR,socleNormalForms));

-- A direct regular-sequence check.  The first element is regular because
-- ZZ[a,b] is a domain; the two colon equalities check the remaining steps.
Ione = ideal(a^3);
Itwo = Ione+ideal(b^3);
assert(trim(Ione:ideal(b^3)) == trim Ione);
assert(trim(Itwo:ideal(a^2*b+2)) == trim Itwo);

-- The successive products q, a*q, and a^2*q have the asserted values.
QnormalForms = unique toList apply(0..7,i ->
     (((i % 2)*q
       + ((i // 2) % 2)*a*q
       + ((i // 4) % 2)*a^2*q) % GR));
assert(#QnormalForms == 8);
annAinQ = select(QnormalForms,t -> (((a*t) % GR) == 0));
assert(#annAinQ == 2);
assert(member(0_RB,annAinQ));
assert(member((2*b) % GR,annAinQ));
bridgeSolutions = select(QnormalForms,t ->
     (((a*(q-t)) % GR) == 0));
assert(#bridgeSolutions == 2);
assert(member(q % GR,bridgeSolutions));
assert(member((q+2*b) % GR,bridgeSolutions));

-- The square-zero extension R -> R/Q is nonsplit in precisely the stated
-- sense: every lift b+x of bar(b), x in Q, still has square q.
assert(all(QnormalForms,x -> ((((b+x)^2-q) % GR) == 0)));

pass "1: base ring, length nine, Hilbert function, socle, CI, and Q-chain";
print "      strong Groebner basis of the base ideal:";
print gens GR;

------------------------------------------------------------------------
-- 2.  The rank-four coordinate algebra and its character
--
-- A = R[U,V]/(U^2-abU+b^2V, V^2-a^2V).
------------------------------------------------------------------------

S = ZZ[U,V,a,b,MonomialOrder=>Lex];
IRmain = ideal(a^3,b^3,a^2*b+2);
F = U^2-a*b*U+b^2*V;
P = V^2-a^2*V;
IA = IRmain+ideal(F,P);
GA = gb IA;

-- The strong basis has no new U,V leading monomials besides U^2,V^2.
-- Formally, successive division by the two monic quadrics proves that
-- 1,U,V,UV are an R-basis; the computed basis is an independent audit that
-- no hidden mixed relation appears.
assert((F % GA) == 0);
assert((P % GA) == 0);
assert((U % GA) != 0);
assert((V % GA) != 0);
assert((U*V % GA) != 0);
assert(#flatten entries gens GA == 8);
expectedLeadingTerms = matrix{{
     4,2*b^2,b^3,2*a,a^2*b,a^3,V^2,U^2
     }};
assert(leadTerm gens GA-expectedLeadingTerms == 0);

W = U*V;
theta = a*U+b*V+a*b*W;
lambda = 1+theta;
lambdaInv = 1-theta;
assert(((lambda-(1+a*U)*(1+b*V)) % GA) == 0);
assert((theta^2 % GA) == 0);
assert(((2*theta-2*b*V) % GA) == 0);
assert(((lambda*lambdaInv-1) % GA) == 0);

pass "2: monic rank-four algebra and invertible affine character";

------------------------------------------------------------------------
-- 3.  Coproduct closure, group-likeness, counit, and noncommutativity
------------------------------------------------------------------------

T = ZZ[U1,V1,U2,V2,aT,bT,MonomialOrder=>Lex];
IT = ideal(
     aT^3,bT^3,aT^2*bT+2,
     U1^2-aT*bT*U1+bT^2*V1,V1^2-aT^2*V1,
     U2^2-aT*bT*U2+bT^2*V2,V2^2-aT^2*V2
     );
GT = gb IT;
lambda1 = (1+aT*U1)*(1+bT*V1);
lambda2 = (1+aT*U2)*(1+bT*V2);
deltaU = U1+lambda1*U2;
deltaV = V1*lambda2+V2;
deltaLambda = (1+aT*deltaU)*(1+bT*deltaV);

assert(((deltaU^2-aT*bT*deltaU+bT^2*deltaV) % GT) == 0);
assert(((deltaV^2-aT^2*deltaV) % GT) == 0);
assert(((deltaLambda-lambda1*lambda2) % GT) == 0);

-- Both counit identities, including the unit point (U,V,lambda)=(0,0,1).
epsFirst = map(S,T,{0_S,0_S,U,V,a,b});
epsSecond = map(S,T,{U,V,0_S,0_S,a,b});
assert(((epsFirst(deltaU)-U) % GA) == 0);
assert(((epsFirst(deltaV)-V) % GA) == 0);
assert(((epsFirst(deltaLambda)-lambda) % GA) == 0);
assert(((epsSecond(deltaU)-U) % GA) == 0);
assert(((epsSecond(deltaV)-V) % GA) == 0);
assert(((epsSecond(deltaLambda)-lambda) % GA) == 0);

-- The coproduct is not cocommutative, hence the group is noncommutative.
swapDeltaU = U2+lambda2*U1;
swapDeltaV = V2*lambda1+V1;
assert(((deltaU-swapDeltaU) % GT) != 0);
assert(((deltaV-swapDeltaV) % GT) != 0);

pass "3: coproduct closure, group-like lambda, counit, and noncommutativity";

------------------------------------------------------------------------
-- 4.  Direct coassociativity / associativity in a triple tensor product
------------------------------------------------------------------------

T3 = ZZ[X1,Y1,X2,Y2,X3,Y3,a3,b3,MonomialOrder=>Lex];
I3 = ideal(
     a3^3,b3^3,a3^2*b3+2,
     X1^2-a3*b3*X1+b3^2*Y1,Y1^2-a3^2*Y1,
     X2^2-a3*b3*X2+b3^2*Y2,Y2^2-a3^2*Y2,
     X3^2-a3*b3*X3+b3^2*Y3,Y3^2-a3^2*Y3
     );
G3 = gb I3;
l1 = (1+a3*X1)*(1+b3*Y1);
l2 = (1+a3*X2)*(1+b3*Y2);
l3 = (1+a3*X3)*(1+b3*Y3);

X12 = X1+l1*X2;
Y12 = Y1*l2+Y2;
l12 = (1+a3*X12)*(1+b3*Y12);
Xleft = X12+l12*X3;
Yleft = Y12*l3+Y3;

X23 = X2+l2*X3;
Y23 = Y2*l3+Y3;
l23 = (1+a3*X23)*(1+b3*Y23);
Xright = X1+l1*X23;
Yright = Y1*l23+Y23;

assert(((Xleft-Xright) % G3) == 0);
assert(((Yleft-Yright) % G3) == 0);
assert(((l12-l1*l2) % G3) == 0);
assert(((l23-l2*l3) % G3) == 0);
assert((((1+a3*Xleft)*(1+b3*Yleft)-l1*l2*l3) % G3) == 0);

pass "4: direct triple-product associativity (equivalently coassociativity)";

------------------------------------------------------------------------
-- 5.  Antipode and both convolution identities
------------------------------------------------------------------------

use S;
SU = (-lambdaInv*U) % GA;
SV = (-V*lambdaInv) % GA;
Slambda = ((1+a*SU)*(1+b*SV)) % GA;

-- The substitution defines an algebra endomorphism of A.
assert(((SU^2-a*b*SU+b^2*SV) % GA) == 0);
assert(((SV^2-a^2*SV) % GA) == 0);
assert(((Slambda-lambdaInv) % GA) == 0);

-- m(S tensor id) Delta = unit*epsilon and
-- m(id tensor S) Delta = unit*epsilon, on both algebra generators.
assert(((SU+Slambda*U) % GA) == 0);
assert(((U+lambda*SU) % GA) == 0);
assert(((SV*lambda+V) % GA) == 0);
assert(((V*Slambda+SV) % GA) == 0);

pass "5: antipode is well-defined and satisfies both convolution identities";

------------------------------------------------------------------------
-- 6.  Power words and non-killedness
------------------------------------------------------------------------

twoU = (U+lambda*U) % GA;
twoV = (V*lambda+V) % GA;
doubleMap = map(S,S,{twoU,twoV,a,b});
fourU = doubleMap(twoU) % GA;
fourV = doubleMap(twoV) % GA;
eightU = doubleMap(fourU) % GA;
eightV = doubleMap(fourV) % GA;

assert(fourU == (2*b*U*V) % GA);
assert(fourV == 0_S);
assert(fourU != 0_S);
assert(eightU == 0_S);
assert(eightV == 0_S);

-- Modulo q=b^2, the fourth-power word becomes the unit word.
GDmain = gb(IA+ideal(b^2));
assert((fourU % GDmain) == 0);
assert((fourV % GDmain) == 0);

pass "6: [4](U)=2bUV is nonzero, [4](V)=0, [8]=e, and [4]=e downstairs";
print "      ([4]U,[4]V,[8]U,[8]V) =";
print {fourU,fourV,eightU,eightV};

------------------------------------------------------------------------
-- 7.  Closed fiber alpha_2 x alpha_2
------------------------------------------------------------------------

CF = GF(2)[Uf,Vf,MonomialOrder=>Lex];
redFiber = map(CF,S,{Uf,Vf,0_CF,0_CF});
assert(redFiber(F) == Uf^2);
assert(redFiber(P) == Vf^2);
assert(redFiber(lambda) == 1_CF);

CFT = GF(2)[Uf1,Vf1,Uf2,Vf2,MonomialOrder=>Lex];
redTensor = map(CFT,T,{Uf1,Vf1,Uf2,Vf2,0_CFT,0_CFT});
assert(redTensor(deltaU) == Uf1+Uf2);
assert(redTensor(deltaV) == Vf1+Vf2);
assert(redTensor(deltaLambda) == 1_CFT);

pass "7: closed fiber has two primitive square-zero coordinates";

------------------------------------------------------------------------
-- 8.  The same subgroup inside (Ga^2) semidirect Gm, weights (1,-1)
------------------------------------------------------------------------

HS = ZZ[x1,y1,z1,w1,x2,y2,z2,w2,as,bs,MonomialOrder=>Lex];
F11 = x1^2-as*bs*x1+bs^2*z1*y1;
F21 = z1*y1^2-as^2*y1;
F31 = z1-(1+as*x1)*(1+bs*z1*y1);
F12 = x2^2-as*bs*x2+bs^2*z2*y2;
F22 = z2*y2^2-as^2*y2;
F32 = z2-(1+as*x2)*(1+bs*z2*y2);
IH = ideal(as^3,bs^3,as^2*bs+2,
           z1*w1-1,z2*w2-1,F11,F21,F31,F12,F22,F32);
GH = gb IH;
xstar = x1+z1*x2;
ystar = y1+w1*y2;
zstar = z1*z2;
F1star = xstar^2-as*bs*xstar+bs^2*zstar*ystar;
F2star = zstar*ystar^2-as^2*ystar;
F3star = zstar-(1+as*xstar)*(1+bs*zstar*ystar);

assert((F1star % GH) == 0);
assert((F2star % GH) == 0);
assert((F3star % GH) == 0);

pass "8: all three standard semidirect-product equations are multiplicatively closed";

------------------------------------------------------------------------
-- 9.  Universal five-relation bridge lemma
------------------------------------------------------------------------

BU = ZZ[P1,Q1,P2,Q2,al,be,ga,rr,ss,MonomialOrder=>Lex];
scalarRelations = ideal(
     al*rr+2,ga*ss+2,ga*rr,be*ss,be*rr+al*ss
     );
IU = scalarRelations+ideal(
     P1^2-al*P1-be*Q1,Q1^2-ga*Q1,
     P2^2-al*P2-be*Q2,Q2^2-ga*Q2
     );
GU = gb IU;
ell1 = (1+rr*P1)*(1+ss*Q1);
ell2 = (1+rr*P2)*(1+ss*Q2);
Pstar = P1+ell1*P2;
Qstar = Q1*ell2+Q2;
ellstar = (1+rr*Pstar)*(1+ss*Qstar);

assert(((Pstar^2-al*Pstar-be*Qstar) % GU) == 0);
assert(((Qstar^2-ga*Qstar) % GU) == 0);
assert(((ellstar-ell1*ell2) % GU) == 0);

-- Scalar consequences used in the hand proof.
GSU = gb scalarRelations;
assert((4 % GSU) == 0);
assert((2*al % GSU) == 0);
assert((2*be % GSU) == 0);
assert((2*ga % GSU) == 0);
assert((2*rr % GSU) == 0);
assert(((rr^2*be-2*ss) % GSU) == 0);
assert((2*ss^2 % GSU) == 0);

-- Universal power formula from the same five relations.
AU = ZZ[P0,Q0,al0,be0,ga0,rr0,ss0,MonomialOrder=>Lex];
IAU = ideal(
     al0*rr0+2,ga0*ss0+2,ga0*rr0,be0*ss0,
     be0*rr0+al0*ss0,
     P0^2-al0*P0-be0*Q0,Q0^2-ga0*Q0
     );
GAU = gb IAU;
ell0 = (1+rr0*P0)*(1+ss0*Q0);
theta0 = ell0-1;
assert((theta0^2 % GAU) == 0);
assert(((2*theta0-2*ss0*Q0) % GAU) == 0);
twoP0 = (P0+ell0*P0) % GAU;
twoQ0 = (Q0*ell0+Q0) % GAU;
doubleU = map(AU,AU,{twoP0,twoQ0,al0,be0,ga0,rr0,ss0});
fourP0 = doubleU(twoP0) % GAU;
fourQ0 = doubleU(twoQ0) % GAU;
eightP0 = doubleU(fourP0) % GAU;
eightQ0 = doubleU(fourQ0) % GAU;
assert(((fourP0-2*ss0*P0*Q0) % GAU) == 0);
assert(fourQ0 == 0_AU);
assert(eightP0 == 0_AU);
assert(eightQ0 == 0_AU);

pass "9: universal five-relation closure and power formulas";

------------------------------------------------------------------------
-- 9a.  The Oort--Tate matched-product criterion
------------------------------------------------------------------------

OT2 = ZZ[xO1,xO2,cO2,dO2,MonomialOrder=>Lex];
IOT2 = ideal(
     cO2*dO2+2,
     xO1^2-cO2*xO1,xO2^2-cO2*xO2
     );
GOT2 = gb IOT2;
chiO1 = 1+dO2*xO1;
chiO2 = 1+dO2*xO2;
xOstar = xO1+chiO1*xO2;
assert(((chiO1^2-1) % GOT2) == 0);
assert(((xOstar^2-cO2*xOstar) % GOT2) == 0);
assert((((1+dO2*xOstar)-chiO1*chiO2) % GOT2) == 0);
assert(((xO1+chiO1*xO1) % GOT2) == 0);

OT = ZZ[uO,vO,cO,dO,eO,fO,MonomialOrder=>Lex];
IOTbase = ideal(
     cO*dO+2,eO*fO+2,
     uO^2-cO*uO,vO^2-eO*vO
     );
GOTbase = gb IOTbase;
LO = 1+dO*uO;
MO = 1+fO*vO;
reverseUO = MO*uO;
reverseVO = vO*LO;

-- Before imposing the cross conditions, these are exactly the two
-- obstructions to passing the Oort--Tate factors through one another.
assert(((reverseUO^2-cO*reverseUO+cO*fO*uO*vO)
        % GOTbase) == 0);
assert(((reverseVO^2-eO*reverseVO+eO*dO*uO*vO)
        % GOTbase) == 0);

IOT = IOTbase+ideal(cO*fO,eO*dO);
GOT = gb IOT;
reverseCharacterO = (1+dO*reverseUO)*(1+fO*reverseVO);
assert(((LO^2-1) % GOT) == 0);
assert(((MO^2-1) % GOT) == 0);
assert(((2*dO) % GOT) == 0);
assert(((2*fO) % GOT) == 0);
assert(((reverseUO^2-cO*reverseUO) % GOT) == 0);
assert(((reverseVO^2-eO*reverseVO) % GOT) == 0);
assert(((reverseCharacterO-MO*LO) % GOT) == 0);

pass "9a: necessary and sufficient Oort--Tate matched-product identities";

------------------------------------------------------------------------
-- 10.  Exact square-zero closure defect and its correction
------------------------------------------------------------------------

TD = ZZ[J1,K1,J2,K2,tt,ad,bd,MonomialOrder=>Lex];
IDpre = ideal(
     ad^3,bd^3,ad^2*bd+2,
     tt^2,bd*tt,2*tt,
     J1^2-ad*bd*J1+tt*K1,K1^2-ad^2*K1,
     J2^2-ad*bd*J2+tt*K2,K2^2-ad^2*K2
     );
GDpre = gb IDpre;
mu1 = (1+ad*J1)*(1+bd*K1);
mu2 = (1+ad*J2)*(1+bd*K2);
Jstar = J1+mu1*J2;
Kstar = K1*mu2+K2;
mustar = (1+ad*Jstar)*(1+bd*Kstar);
defectJ = (Jstar^2-ad*bd*Jstar+tt*Kstar) % GDpre;
defectK = (Kstar^2-ad^2*Kstar) % GDpre;
defectMu = (mustar-mu1*mu2) % GDpre;
expectedDefectJ = ad*(bd^2-tt)*K1*J2;

assert(((defectJ-expectedDefectJ) % GDpre) == 0);
assert(defectK == 0_TD);
assert(defectMu == 0_TD);

-- The explicit tensor-factor notation and graph factorization in Appendix A.
LL1 = 1+ad*J1;
MM1 = 1+bd*K1;
LL2 = 1+ad*J2;
MM2 = 1+bd*K2;
graphAlpha = ad*J2;
graphBeta = bd*K1;
graphE = graphAlpha*graphBeta;
graphFactor = LL1*MM2*graphE*(2+graphAlpha+graphBeta+graphE);
assert(((mustar-mu1*mu2-graphFactor) % GDpre) == 0);
assert(((2*graphE) % GDpre) == 0);
assert(((graphE*graphAlpha) % GDpre) == 0);
assert(((graphE*graphBeta) % GDpre) == 0);
assert(((graphE^2) % GDpre) == 0);

-- The explicit inverse lambda^{-1}=lambda*(1+a^2*t*V).
mu1Inv = mu1*(1+ad^2*tt*K1);
mu2Inv = mu2*(1+ad^2*tt*K2);
assert(((mu1*mu1Inv-1) % GDpre) == 0);
assert(((mu2*mu2Inv-1) % GDpre) == 0);

-- The geometric displacement eta_t=-tV has exactly the needed linearized
-- change in the multiplication defect -a*t*V_1*U_2.
bridgeCoboundary = (-tt*(Kstar-K1-K2)) % GDpre;
assert(((bridgeCoboundary+ad*tt*K1*J2) % GDpre) == 0);
assert(((defectJ-ad*bd^2*K1*J2-bridgeCoboundary) % GDpre) == 0);

-- t=0 is the coefficientwise lift: its sole defect is a*b^2 V_1 U_2.
GDnaive = gb(IDpre+ideal(tt));
coefficientwiseDefect = (ad*bd^2*K1*J2) % GDnaive;
assert(coefficientwiseDefect != 0_TD);
assert(((defectJ-coefficientwiseDefect) % GDnaive) == 0);
assert((defectK % GDnaive) == 0);
assert((defectMu % GDnaive) == 0);

-- t=q=b^2 is the corrected lift: all three defects vanish exactly.
GDcorrected = gb(IDpre+ideal(tt-bd^2));
assert((defectJ % GDcorrected) == 0);
assert((defectK % GDcorrected) == 0);
assert((defectMu % GDcorrected) == 0);

-- Downstairs (q=t=0), the two rank-two walls are themselves subgroup
-- graphs, and their product is the matched-product subgroup G_0.
GDdown = gb(IDpre+ideal(tt,bd^2));
assert((defectJ % GDdown) == 0);
assert((defectK % GDdown) == 0);
assert((defectMu % GDdown) == 0);
pMu1 = 1+ad*J1;
pMu2 = 1+ad*J2;
pJstar = J1+pMu1*J2;
assert(((pJstar^2-ad*bd*pJstar) % GDdown) == 0);
assert((((1+ad*pJstar)-pMu1*pMu2) % GDdown) == 0);
kMu1 = 1+bd*K1;
kMu2 = 1+bd*K2;
kKstar = K1*kMu2+K2;
assert(((kKstar^2-ad^2*kKstar) % GDdown) == 0);
assert((((1+bd*kKstar)-kMu1*kMu2) % GDdown) == 0);

pass "10: exact closure-defect vector and its correction";
print "       exact defect vector before imposing a*(t-b^2)=0:";
print {defectJ,defectK,defectMu};

-- Explicit pointwise structure of G_0 over D=R/(b^2).
Ldown = 1+ad*J1;
Mdown = 1+bd*K1;
ellDown = Ldown*Mdown;
assert(((Ldown^2-1) % GDdown) == 0);
assert(((Mdown^2-1) % GDdown) == 0);
assert(((ellDown^2-1) % GDdown) == 0);
assert(((2*ellDown-2) % GDdown) == 0);
assert(((2*(1+ellDown)) % GDdown) == 0);

-- The matched actions refactor k(V)p(U) as
-- p((1+bV)U) k(V(1+aU)).
reverseU = Mdown*J1;
reverseV = K1*Ldown;
reverseEll = (1+ad*reverseU)*(1+bd*reverseV);
assert(((reverseU^2-ad*bd*reverseU) % GDdown) == 0);
assert(((reverseV^2-ad^2*reverseV) % GDdown) == 0);
assert(((reverseEll-Mdown*Ldown) % GDdown) == 0);

-- The matched-product formula agrees with the ambient formula.
matchedJstar = J1+Ldown*Mdown*J2;
matchedKstar = K1*(1+ad*J2)*(1+bd*K2)+K2;
assert(((matchedJstar-Jstar) % GDdown) == 0);
assert(((matchedKstar-Kstar) % GDdown) == 0);

-- The square word is (bUV,aUV), so G_0 is not killed by two.
doubleJdown = (J1+ellDown*J1) % GDdown;
doubleKdown = (K1*ellDown+K1) % GDdown;
assert(((doubleJdown-bd*J1*K1) % GDdown) == 0);
assert(((doubleKdown-ad*J1*K1) % GDdown) == 0);
assert(doubleJdown != 0_TD);
assert(doubleKdown != 0_TD);

-- The ambient inverse restricts to the stated matched inverse.
invJdown = (-ellDown*J1) % GDdown;
invKdown = (-K1*ellDown) % GDdown;
invEllDown = ((1+ad*invJdown)*(1+bd*invKdown)) % GDdown;
assert(((invJdown-reverseU) % GDdown) == 0);
assert(((invKdown-reverseV) % GDdown) == 0);
assert(((invEllDown-ellDown) % GDdown) == 0);
assert(((J1+ellDown*invJdown) % GDdown) == 0);
assert(((K1*invEllDown+invKdown) % GDdown) == 0);
assert(((invJdown+invEllDown*J1) % GDdown) == 0);
assert(((invKdown*ellDown+K1) % GDdown) == 0);

-- Direct ambient conjugation proves that neither displayed factor is
-- normal: the cross coordinates bUV and aUV survive.
hMul = (g,h) -> {
     g#0+g#2*h#0,
     g#1*h#2+h#1,
     g#2*h#2
     };
pDown = {J1,0_TD,Ldown};
kDown = {0_TD,K1,Mdown};
pInvDown = {-Ldown*J1,0_TD,Ldown};
kInvDown = {0_TD,-K1*Mdown,Mdown};
conjKDown = hMul(hMul(pDown,kDown),pInvDown);
conjPDown = hMul(hMul(kDown,pDown),kInvDown);
assert(((conjKDown#0-bd*J1*K1) % GDdown) == 0);
assert(((conjKDown#1-K1*Ldown) % GDdown) == 0);
assert(((conjKDown#2-Mdown) % GDdown) == 0);
assert(((conjPDown#0-Mdown*J1) % GDdown) == 0);
assert(((conjPDown#1-ad*J1*K1) % GDdown) == 0);
assert(((conjPDown#2-Ldown) % GDdown) == 0);
assert(((bd*J1*K1) % GDdown) != 0_TD);
assert(((ad*J1*K1) % GDdown) != 0_TD);

-- The coefficient obstructions in the no-semidirect corollary.
GDwithB = gb ideal(ad^3,bd^2,ad^2*bd+2,bd);
GDwithA = gb ideal(ad^3,bd^2,ad^2*bd+2,ad);
assert((ad % GDwithB) != 0_TD);
assert((bd % GDwithA) != 0_TD);

-- Universal graph identities used to exclude every alternative normal
-- rank-two factor.  The first graph is v=c*u and is conjugated by K;
-- the second is u=c*v and is conjugated by P.
NG = ZZ[uN,yN,vN,xN,cN,aN,bN,MonomialOrder=>Lex];
ING = ideal(
     aN^3,bN^2,aN^2*bN+2,
     uN^2-aN*bN*uN,yN^2-aN^2*yN,
     vN^2-aN^2*vN,xN^2-aN*bN*xN
     );
GNG = gb ING;

MY = 1+bN*yN;
wGraphP = (1+aN*uN)*(1+bN*cN*uN);
conjGraphPU = MY*uN;
conjGraphPV = (cN*uN+yN*(wGraphP-1))*MY;
assert(((conjGraphPV-cN*conjGraphPU
         -(aN+bN*cN)*uN*yN) % GNG) == 0);

LX = 1+aN*xN;
wGraphK = (1+aN*cN*vN)*(1+bN*vN);
conjGraphKU = LX*cN*vN+(1-wGraphK)*xN;
conjGraphKV = vN*LX;
assert(((conjGraphKU-cN*conjGraphKV
         -(bN+aN*cN)*xN*vN) % GNG) == 0);

pass "10a: explicit downstairs law, inverse, matched actions, and no semidirect factor";

------------------------------------------------------------------------
-- 11.  The downstairs complete intersection and its conormal frame
------------------------------------------------------------------------

HC = ZZ[Uc,Vc,zc,wc,ac,bc,MonomialOrder=>Lex];
IHambient = ideal(
     ac^3,bc^3,ac^2*bc+2,bc^2,zc*wc-1
     );
PhiC = Uc^2-ac*bc*Uc;
PsiC = Vc^2-ac^2*Vc;
lambdaC = (1+ac*Uc)*(1+bc*Vc);
XiC = zc-lambdaC;

-- These colon equalities say successively that Phi, Psi, Xi form a
-- regular sequence in O(H_D).  Consequently their conormal classes are
-- a free O(G_0)-basis of I_0/I_0^2.
assert(trim(IHambient:ideal(PhiC)) == trim IHambient);
IHone = IHambient+ideal(PhiC);
assert(trim(IHone:ideal(PsiC)) == trim IHone);
IHtwo = IHone+ideal(PsiC);
assert(trim(IHtwo:ideal(XiC)) == trim IHtwo);

pass "11: downstairs equations are a regular sequence with the stated conormal frame";

------------------------------------------------------------------------
-- 12.  Supplementary rigidity and fourth-word checks
------------------------------------------------------------------------

CG = ZZ[Ug,Vg,phig,psig,ag,bg,MonomialOrder=>Lex];
IG = ideal(ag^3,bg^3,ag^2*bg+2);
GG = gb IG;
qg = bg^2;
Ugprime = Ug+qg*phig;
Vgprime = Vg+qg*psig;
gaugeDifference = (
     Ugprime^2-ag*bg*Ugprime+qg*Vgprime
     -(Ug^2-ag*bg*Ug+qg*Vg)
     );
assert((gaugeDifference % GG) == 0);

-- The fourth-word error lands in QA, is square-zero, and satisfies the
-- generator-level Leibniz checks for a derivation relative to the unit map.
use S;
assert(((fourU+a^2*b^2*U*V) % GA) == 0);
assert(((b^2*fourU) % GA) == 0);
assert(((a*b*fourU) % GA) == 0);
assert(((fourU^2) % GA) == 0);
assert(((fourU*fourV) % GA) == 0);
assert(((fourV^2) % GA) == 0);

-- The word error is one further a-step beyond the coefficientwise
-- closure defect:
-- omega_4(U)=-a*diag^*(kappa(Phi)).
TN = ZZ[XN1,YN1,XN2,YN2,aa,bb,MonomialOrder=>Lex];
IN = ideal(
     aa^3,bb^3,aa^2*bb+2,
     XN1^2-aa*bb*XN1,YN1^2-aa^2*YN1,
     XN2^2-aa*bb*XN2,YN2^2-aa^2*YN2
     );
GN = gb IN;
kappaPhi = (aa*bb^2*YN1*XN2) % GN;
assert(kappaPhi != 0_TN);
diagN = map(S,TN,{U,V,U,V,a,b});
assert(((fourU+a*diagN(kappaPhi)) % GA) == 0);

pass "12: rigidity, fourth-word error, and closure-defect identity";

print "ALL CLAIM-BY-CLAIM RANK-FOUR AFFINE-GROUP AUDITS PASSED";
