R = QQ[x,y]
G = matrix{{x^2, x*y}}
B = matrix{{x^3, x^2*y}}
V = quotient(B, G, DegreeLimit => {3}, MinimalGenerators => false)
assert(G*V == B)
<< "quotient rows=" << numrows V << " cols=" << numcols V << " V=" << V << endl;
J = ideal G
H = gb(J, DegreeLimit => 3)
V2 = B // forceGB gens H
assert((gens H)*V2 == B)
<< "gb lift rows=" << numrows V2 << " cols=" << numcols V2 << endl;
collectGarbage()
<< "collectGarbage OK" << endl;
<< "CERT_BRANCH=" << getenv "CERT_BRANCH" << endl;
