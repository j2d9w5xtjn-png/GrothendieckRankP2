import sys, itertools
sys.path.insert(0,'/mnt/data/groth_v42/scripts')
from z3 import *
from s2check import build_blocks
from order4sat import fresh

class KBiDual:
    name='Kdual[U,V]/(U^2,V^2)'; n=8
    monoms=[(0,0,0),(1,0,0),(0,1,0),(1,1,0),(0,0,1),(1,0,1),(0,1,1),(1,1,1)]
    idx={m:i for i,m in enumerate(monoms)}
    def zero(self): return tuple(BitVecVal(0,1) for _ in range(8))
    def one(self): return tuple(BitVecVal(1 if i==0 else 0,1) for i in range(8))
    def var(self,tag): nm=fresh(tag); return tuple(BitVec(nm+f'_{i}',1) for i in range(8))
    def add(self,a,b): return tuple(x^y for x,y in zip(a,b))
    def sub(self,a,b): return self.add(a,b)
    def mul(self,a,b):
        out=[BitVecVal(0,1)]*8
        for i,mi in enumerate(self.monoms):
          for j,mj in enumerate(self.monoms):
            exp=(mi[0]+mj[0],mi[1]+mj[1],mi[2]+mj[2])
            if all(e<=1 for e in exp): out[self.idx[exp]]=out[self.idx[exp]]^(a[i]&b[j])
        return tuple(out)
    def eq0(self,a): return And(*[x==0 for x in a])
    def neq0(self,a): return Or(*[x!=0 for x in a])
    def lowzero(self,a): return And(a[0]==0,a[1]==0)
    def deform(self,tag): v=self.var(tag); return (BitVecVal(0,1),BitVecVal(0,1))+v[2:]
R=KBiDual(); fib={(1,2,3):1}
models={
'W2F':{(2,1,1):1,(3,1,2):1,(3,2,1):1},
'mu2a2':{(1,1,1):1,(3,1,2):1,(3,2,1):1,(3,1,3):1,(3,3,1):1},
}
def pin(c,m):
    cons=[]
    for key,val in c.items():
        cons += [val[0]==(1 if m.get(key,0) else 0), val[1]==0]
    return cons
# K ops
def kzero(): return (BitVecVal(0,1),BitVecVal(0,1))
def kadd(a,b): return (a[0]^b[0],a[1]^b[1])
def kmul(a,b): return (a[0]&b[0], (a[0]&b[1])^(a[1]&b[0]))
def keq(a,b): return And(a[0]==b[0],a[1]==b[1])
def kneq0(a): return Or(a[0]!=0,a[1]!=0)
def coeff(el,mon):
    return {'U':(el[2],el[3]),'V':(el[4],el[5]),'UV':(el[6],el[7]),'K':(el[0],el[1])}[mon]
def kconst(a,b): return (BitVecVal(a,1),BitVecVal(b,1))
KELS=[kconst(a,b) for a,b in itertools.product([0,1],[0,1])]
def not_in_rankideal(N,p,q):
    # N not in (p,q^2)
    return And(*[Not(keq(N,kadd(kmul(p,S), kmul(kmul(q,q),H)))) for S in KELS for H in KELS])

def solve(model,label,bad,timeout=300000):
    A,M,C,F,phi,c,Mtab=build_blocks(R,fib)
    s=Solver(); s.set('timeout',timeout)
    for e in A+M+C+F+pin(c,models[model]): s.add(e)
    s.add(bad(phi))
    res=s.check(); print(model,label,res,flush=True)
    if res==sat:
      mm=s.model()
      for name,mon in [('P','U'),('Q','V'),('T','UV')]:
        print(name)
        for i in range(1,4): print([tuple(mm.eval(x,model_completion=True).as_long() for x in coeff(phi[i][r],mon)) for r in range(1,4)])

def bad_rank_shape_W(phi):
    # P: x,z zero; y only x. Q same.
    bad=[]
    for mon in ['U','V']:
      # x row all zero, z row all zero, y row no y/z coords
      for r in range(1,4): bad.append(kneq0(coeff(phi[1][r],mon)))
      for r in range(1,4): bad.append(kneq0(coeff(phi[3][r],mon)))
      bad.append(kneq0(coeff(phi[2][2],mon))); bad.append(kneq0(coeff(phi[2][3],mon)))
    return Or(*bad)
def bad_Tx_W(phi): return Or(kneq0(coeff(phi[1][2],'UV')), kneq0(coeff(phi[1][3],'UV')))
def bad_div_W(phi):
    p=coeff(phi[2][1],'U'); q=coeff(phi[2][1],'V')
    rho=coeff(phi[2][2],'UV') # (Ty)_y
    N=kmul(q,rho)
    return not_in_rankideal(N,p,q)

def bad_rank_shape_E(phi):
    # mu2a2 mirror: P,Q: y,z zero; x only y.
    bad=[]
    for mon in ['U','V']:
      for r in range(1,4): bad.append(kneq0(coeff(phi[2][r],mon)))
      for r in range(1,4): bad.append(kneq0(coeff(phi[3][r],mon)))
      bad.append(kneq0(coeff(phi[1][1],mon))); bad.append(kneq0(coeff(phi[1][3],mon)))
    return Or(*bad)
def bad_Ty_E(phi): return Or(kneq0(coeff(phi[2][1],'UV')), kneq0(coeff(phi[2][3],'UV')))
def bad_div_E(phi):
    p=coeff(phi[1][2],'U'); q=coeff(phi[1][2],'V')
    rho=coeff(phi[1][1],'UV') # (Tx)_x in mirror
    N=kmul(q,rho)
    return not_in_rankideal(N,p,q)



def shape_constraints_W(phi):
    cons=[]; z=kzero()
    for mon in ['U','V']:
      for r in range(1,4): cons.append(keq(coeff(phi[1][r],mon), z))
      for r in range(1,4): cons.append(keq(coeff(phi[3][r],mon), z))
      cons.append(keq(coeff(phi[2][2],mon), z)); cons.append(keq(coeff(phi[2][3],mon), z))
    return cons

def solve_Tx():
    A,M,C,F,phi,c,Mtab=build_blocks(R,fib)
    s=Solver(); s.set('timeout',600000)
    for e in A+M+C+F+pin(c,models['W2F'])+shape_constraints_W(phi): s.add(e)
    s.add(Or(kneq0(coeff(phi[1][2],'UV')), kneq0(coeff(phi[1][3],'UV'))))
    res=s.check(); print('W2F T(x) not in kx over dual coeff',res,flush=True)
    if res==sat:
      mm=s.model();
      for name,mon in [('P','U'),('Q','V'),('T','UV')]:
        print(name)
        for i in range(1,4): print([tuple(mm.eval(x,model_completion=True).as_long() for x in coeff(phi[i][r],mon)) for r in range(1,4)])
set_param('parallel.enable', True)
solve_Tx()
