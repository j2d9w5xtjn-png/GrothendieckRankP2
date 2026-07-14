-- Fresh-process verifier for certs_lowmem_<branch>.m2out.
-- It does no Groebner computation: every displayed coefficient vector is
-- multiplied by the displayed original-generator row and compared exactly
-- with its displayed target polynomial.

kk = ZZ/2;
cIx = flatten flatten flatten for i from 1 to 3 list for j from 1 to 3 list
          for k from 1 to 3 list for d from 0 to 2 list c_(i,j,k,d);
mIx = flatten flatten flatten for i from 1 to 3 list for j from i to 3 list
          for r from 1 to 3 list for d from 1 to 2 list m_(i,j,r,d);
Q = kk[cIx | mIx, MonomialOrder => GRevLex];
use Q;

branch = getenv "CERT_BRANCH";
expected = (if branch == "xy" then 21
            else if branch == "t4" then 24
            else error "CERT_BRANCH must be xy or t4");

variant = getenv "CERT_VARIANT";
fn = (if variant == "pruned5" then (
          assert(branch == "t4");
          "scripts/certs_lowmem_pruned_t4_d5.m2out")
      else if variant == "pruned" then
          "scripts/certs_lowmem_pruned_" | branch | ".m2out"
      else "scripts/certs_lowmem_" | branch | ".m2out");
assert(fileExists fn);
load fn;
Gmat = matrix{Gens};
assert(numcols Gmat == (if branch == "xy" then 157 else 178));

for i from 0 to expected-1 do (
    vv := v_(i);
    assert(#vv == numcols Gmat);
    V := transpose matrix{vv};
    -- Reconstructing V from a printed list loses the original free-module
    -- degree metadata, so compare the polynomial entry rather than Matrix ==.
    assert((Gmat*V)_(0,0) == b_(i));
    << "FRESH VERIFY " << branch << " " << i+1 << "/" << expected
       << " PASS" << endl << flush;
    V = null;);

<< "FRESH VERIFICATION COMPLETE " << branch << endl << flush;
