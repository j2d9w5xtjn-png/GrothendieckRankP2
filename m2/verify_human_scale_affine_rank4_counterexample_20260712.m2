-- Exact audit for the human-scale affine-group counterexample.
-- Run on the local Mac with:
--   M2 --script m2/verify_human_scale_affine_rank4_counterexample_20260712.m2

-- Base and coordinate algebra.
S = ZZ[U,V,a,b,MonomialOrder=>Lex];
IR = ideal(a^3,b^3,a^2*b+2);
K = IR + ideal(U^2-a*b*U+b^2*V,V^2-a^2*V);
GR = gb IR;
G = gb K;

assert((4 % GR) == 0);
assert((2 % GR) != 0);
assert((2*b % GR) != 0);
assert((b^2 % GR) != 0);
assert((a*b^2 % GR) != 0);
assert((a^2*b^2 % GR) != 0);
assert((b^4 % GR) == 0);
assert((b^3 % GR) == 0);
assert((2*b^2 % GR) == 0);
assert(((a^2*b^2+2*b) % GR) == 0);
assert((2*b*U*V % G) != 0);

W = U*V;
theta = a*U+b*V+a*b*W;
lambda = 1+theta;
assert((theta^2 % G) == 0);
assert(((2*theta-2*b*V) % G) == 0);
assert(((lambda*(1-theta)-1) % G) == 0);

-- Exact coproduct closure in A tensor_R A.
T = ZZ[U1,V1,U2,V2,a1,b1,MonomialOrder=>Lex];
IT = ideal(
     a1^3,b1^3,a1^2*b1+2,
     U1^2-a1*b1*U1+b1^2*V1,V1^2-a1^2*V1,
     U2^2-a1*b1*U2+b1^2*V2,V2^2-a1^2*V2
     );
GT = gb IT;
lambda1 = (1+a1*U1)*(1+b1*V1);
lambda2 = (1+a1*U2)*(1+b1*V2);
deltaU = U1+lambda1*U2;
deltaV = V1*lambda2+V2;
deltaLambda = (1+a1*deltaU)*(1+b1*deltaV);

assert(((deltaU^2-a1*b1*deltaU+b1^2*deltaV) % GT) == 0);
assert(((deltaV^2-a1^2*deltaV) % GT) == 0);
assert(((deltaLambda-lambda1*lambda2) % GT) == 0);

swapDeltaU = U2+lambda2*U1;
assert(((deltaU-swapDeltaU) % GT) != 0);

-- Universal audit of the one closure lemma: these are the only five
-- scalar bridge relations used in the paper.
TU = ZZ[P1,Q1,P2,Q2,al,be,ga,rr,ss,MonomialOrder=>Lex];
IU = ideal(
     al*rr+2,ga*ss+2,ga*rr,be*ss,be*rr+al*ss,
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

-- Square-zero deformation chart.  The variable tt is a possible bridge
-- coefficient in Q=(b^2), so tt^2=b*tt=2*tt=0.  Once the two diagonal
-- rank-two factors are fixed, the only remaining closure equation is
-- a*(tt-b^2)=0.
TD = ZZ[J1,K1,J2,K2,tt,ad,bd,MonomialOrder=>Lex];
IDpre = ideal(
     ad^3,bd^3,ad^2*bd+2,tt^2,bd*tt,2*tt,
     J1^2-ad*bd*J1+tt*K1,K1^2-ad^2*K1,
     J2^2-ad*bd*J2+tt*K2,K2^2-ad^2*K2
     );
GDpre = gb IDpre;
ID = IDpre + ideal(ad*(tt-bd^2));
GD = gb ID;
mu1 = (1+ad*J1)*(1+bd*K1);
mu2 = (1+ad*J2)*(1+bd*K2);
Jstar = J1+mu1*J2;
Kstar = K1*mu2+K2;
mustar = (1+ad*Jstar)*(1+bd*Kstar);
deformationCurvatures = {
     (Jstar^2-ad*bd*Jstar+tt*Kstar) % GDpre,
     (Kstar^2-ad^2*Kstar) % GDpre,
     (mustar-mu1*mu2) % GDpre
     };
assert(((Jstar^2-ad*bd*Jstar+tt*Kstar) % GD) == 0);
assert(((Kstar^2-ad^2*Kstar) % GD) == 0);
assert(((mustar-mu1*mu2) % GD) == 0);

-- The same closure check in the standard semidirect-product coordinates
-- (x,y,z), where z acts on Ga^2 with weights +1 and -1.
HS = ZZ[x1,y1,z1,t1,x2,y2,z2,t2,as,bs,MonomialOrder=>Lex];
F11 = x1^2-as*bs*x1+bs^2*z1*y1;
F21 = z1*y1^2-as^2*y1;
F31 = z1-(1+as*x1)*(1+bs*z1*y1);
F12 = x2^2-as*bs*x2+bs^2*z2*y2;
F22 = z2*y2^2-as^2*y2;
F32 = z2-(1+as*x2)*(1+bs*z2*y2);
IH = ideal(as^3,bs^3,as^2*bs+2,
           z1*t1-1,z2*t2-1,F11,F21,F31,F12,F22,F32);
GH = gb IH;
xstar = x1+z1*x2;
ystar = y1+t1*y2;
zstar = z1*z2;
F1star = xstar^2-as*bs*xstar+bs^2*zstar*ystar;
F2star = zstar*ystar^2-as^2*ystar;
F3star = zstar-(1+as*xstar)*(1+bs*zstar*ystar);
assert((F1star % GH) == 0);
assert((F2star % GH) == 0);
assert((F3star % GH) == 0);

-- Antipode and both convolution identities.
lambdaInv = 1-theta;
SU = (-lambdaInv*U) % G;
SV = (-V*lambdaInv) % G;
SW = (SU*SV) % G;
Slambda = (1+a*SU)*(1+b*SV) % G;

assert(((SU-(U-b*W+a*b^2*V)) % G) == 0);
assert(((SV-(V+a*W)) % G) == 0);
assert(((SU^2-a*b*SU+b^2*SV) % G) == 0);
assert(((SV^2-a^2*SV) % G) == 0);
assert(((Slambda-lambdaInv) % G) == 0);
assert(((SU+Slambda*U) % G) == 0);
assert(((U+lambda*SU) % G) == 0);
assert(((SV*lambda+V) % G) == 0);
assert(((V*Slambda+SV) % G) == 0);

-- Power words from the affine-group norm.
phiU = (U+lambda*U) % G;
phiV = (V*lambda+V) % G;
phi = map(S,S,{phiU,phiV,a,b});
fourU = phi(phiU) % G;
fourV = phi(phiV) % G;
eightU = phi(fourU) % G;
eightV = phi(fourV) % G;

assert(fourU == 2*b*U*V);
assert(fourV == 0);
assert(eightU == 0);
assert(eightV == 0);

-- Before inserting the bridge beta=-b^2, the lifted tensor-product
-- algebra fails by the single mixed curvature a*b^2 V_1 U_2.
TN = ZZ[X1,Y1,X2,Y2,aa,bb,MonomialOrder=>Lex];
IN = ideal(
     aa^3,bb^3,aa^2*bb+2,
     X1^2-aa*bb*X1,Y1^2-aa^2*Y1,
     X2^2-aa*bb*X2,Y2^2-aa^2*Y2
     );
GN = gb IN;
ln1 = (1+aa*X1)*(1+bb*Y1);
ln2 = (1+aa*X2)*(1+bb*Y2);
dXN = X1+ln1*X2;
dYN = Y1*ln2+Y2;
dLambdaN = (1+aa*dXN)*(1+bb*dYN);
naiveGraphCurvature = (dLambdaN-ln1*ln2) % GN;
naiveCurvature = (aa*bb^2*Y1*X2) % GN;
bridgeCoboundary = (-bb^2*(dYN-Y1-Y2)) % GN;
assert(((ln1^2-1) % GN) == 0);
assert(((dXN^2-aa*bb*dXN-aa*bb^2*Y1*X2) % GN) == 0);
assert(naiveCurvature != 0);
assert(((naiveCurvature+bridgeCoboundary) % GN) == 0);
assert(((dYN^2-aa^2*dYN) % GN) == 0);
assert(naiveGraphCurvature == 0);

-- The first-order fourth-word defect is one further a-step beyond the
-- naive multiplication curvature: omega_4(U)=-a*diag^*(kappa(Phi)).
diagN = map(S,TN,{U,V,U,V,a,b});
assert(((fourU+a*diagN(naiveCurvature)) % G) == 0);

-- Beginner toy 1: x*y=x+y+e*x*y as a graph in Aff_1, with the finite
-- characteristic-two quotient x^2=0.
TA = GF(2)[xa1,xa2,ee,MonomialOrder=>Lex];
IA = ideal(xa1^2,xa2^2,ee^2);
GA = gb IA;
xastar = xa1+xa2+ee*xa1*xa2;
za1 = 1+ee*xa1;
za2 = 1+ee*xa2;
assert((xastar^2 % GA) == 0);
assert(((za1*za2-(1+ee*xastar)) % GA) == 0);

-- Beginner toy 2: the scaled Heisenberg cocycle is associative.
TH = ZZ[eh,xh1,yh1,zh1,xh2,yh2,zh2,xh3,yh3,zh3,
        MonomialOrder=>Lex];
GH = gb ideal(eh^2);
zLeft = zh1+zh2+eh*xh1*yh2+zh3+eh*(xh1+xh2)*yh3;
zRight = zh1+zh2+zh3+eh*xh2*yh3+eh*xh1*(yh2+yh3);
assert(((zLeft-zRight) % GH) == 0);

-- Beginner toy 3: the finite bridge over F_2[r,s]/(r^2,s^2).
TB = GF(2)[JB1,KB1,JB2,KB2,tb,rb,sb,MonomialOrder=>Lex];
IBpre = ideal(
     rb^2,sb^2,tb^2,sb*tb,
     JB1^2-rb*JB1+tb*KB1,KB1^2,
     JB2^2-rb*JB2+tb*KB2,KB2^2
     );
GBpre = gb IBpre;
nub1 = (1+rb*JB1)*(1+sb*KB1);
nub2 = (1+rb*JB2)*(1+sb*KB2);
JBstar = JB1+nub1*JB2;
KBstar = KB1*nub2+KB2;
nubstar = (1+rb*JBstar)*(1+sb*KBstar);
toyBridgeCurvatures = {
     (JBstar^2-rb*JBstar+tb*KBstar) % GBpre,
     (KBstar^2) % GBpre,
     (nubstar-nub1*nub2) % GBpre
     };
IB = IBpre + ideal(rb*(sb-tb));
GB = gb IB;
assert(((JBstar^2-rb*JBstar+tb*KBstar) % GB) == 0);
assert((KBstar^2 % GB) == 0);
assert(((nubstar-nub1*nub2) % GB) == 0);

IBactual = IBpre + ideal(tb-sb);
GBactual = gb IBactual;
assert(((nub1^2-1) % GBactual) == 0);
assert(((1+nub1+nub1^2+nub1^3) % GBactual) == 0);
toyTwoU = ((1+nub1)*JB1) % GBactual;
toyTwoV = (KB1*(1+nub1)) % GBactual;
assert(((toyTwoU-(sb*JB1*KB1+rb*sb*KB1)) % GBactual) == 0);
assert(((toyTwoV-rb*JB1*KB1) % GBactual) == 0);
assert(toyTwoU != 0);
assert(toyTwoV != 0);
swapJBstar = JB2+nub2*JB1;
assert(((JBstar-swapJBstar) % GBactual) != 0);

print "BASE PASS: two cubic nilpotents and one mixed characteristic-four relation";
print "BASE STRONG GROEBNER BASIS:";
print gens GR;
print "HOPF PASS: both quadrics, group-like character, antipode";
print "UNIVERSAL CLOSURE PASS: five bridge equations imply all three closure identities";
print "DEFORMATION CHART PASS: one residual equation a*(tt-b^2)=0 gives closure";
print "DEFORMATION CHART CURVATURES BEFORE THE RESIDUAL EQUATION:";
print deformationCurvatures;
print "STANDARD SEMIDIRECT PASS: all three defining equations are closed";
print "POWER NORMAL FORMS ([4]U,[4]V,[8]U,[8]V):";
print fourU;
print fourV;
print eightU;
print eightV;
print "SQUARE-ZERO CURVATURE PASS: a*b^2 V1 U2 is nonzero and is canceled by the bridge";
print "COBOUNDARY PASS: -b^2*(Vstar-V1-V2) cancels the unique curvature";
print "EMBEDDED DEFORMATION PASS: q, a*q, a^2*q survive while q^2=b*q=2*q=0";
print "WORD-DEFECT LINK PASS: [4]U=-a*diag(naive curvature)";
print "TOY AFFINE PASS: graph law and finite rank-two quotient";
print "TOY HEISENBERG PASS: the square-zero cocycle is associative";
print "TOY BRIDGE CURVATURES:";
print toyBridgeCurvatures;
print "TOY BRIDGE PASS: one residual coefficient, nonzero doubling, N4(lambda)=0";
print "ALL HUMAN-SCALE AFFINE-GROUP AUDITS PASSED";
