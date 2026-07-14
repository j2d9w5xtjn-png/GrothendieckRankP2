from z3 import Solver, BitVec, BitVecVal, Or, sat
from order4sat_beyond import F2epsN
from s2check import build_blocks
from s3gates import KF2, digit
T4={(1,1,2):1,(1,2,3):1}; K=KF2(); NN=6

def ksum(xs):
    out=K.zero()
    for x in xs: out=K.add(out,x)
    return out

def dmat(P,s,shift=0):
    out={}
    for i in range(1,4):
      for ss in range(1,4):
        terms=[]
        for n in range(1,s):
          m=s-n
          if (n+shift) in P and (m+shift) in P:
            for r in range(1,4): terms.append(K.mul(P[n+shift][(i,r)],P[m+shift][(r,ss)]))
        out[(i,ss)]=ksum(terms)
    return out
R=F2epsN(NN); A,Mb,C,F,phi,c,Mtab=build_blocks(R,T4); base=A+Mb+C+F
c1=BitVec('pin_c1_s6md',1); c4=BitVec('pin_c4_s6md',1)
def pin0(i,j,k):
    if i==1:
        if (j,k) in [(1,2),(2,1),(2,3),(3,2)]: return c1
        if (j,k)==(2,2): return c4
        return BitVecVal(0,1)
    if i==2: return BitVecVal(0,1)
    if (j,k) in [(1,2),(2,1)]: return BitVecVal(1,1)
    if (j,k) in [(2,3),(3,2)]: return c1
    return BitVecVal(0,1)
for i in range(1,4):
  for j in range(1,4):
    for k in range(1,4): base.append(digit(R,c[(i,j,k)],0)==pin0(i,j,k))
P={n:{(i,r):digit(R,phi[i][r],n) for i in range(1,4) for r in range(1,4)} for n in range(1,NN)}
known=[]
for s in (2,3,4,5): known += list(dmat(P,s).values())
D6=dmat(P,6)
for s_idx in (2,3):
  Sh=dmat(P,s_idx,shift=1)
  ss=Solver(); ss.set('timeout',120000)
  ss.add(*base); ss.add(*[K.eq0(x) for x in known])
  ss.add(Or(*[K.neq0(v) for v in Sh.values()]))
  res=ss.check(); print('susp',s_idx,res)
  if res==sat:
    m=ss.model()
    for n in range(1,6):
      print('P',n)
      for i in range(1,4):
        print(' ', [m.evaluate(P[n][(i,j)], model_completion=True).as_long() for j in range(1,4)])
    print('Shift matrix')
    for i in range(1,4): print(' ', [m.evaluate(Sh[(i,j)], model_completion=True).as_long() for j in range(1,4)])
    print('D6 matrix in same model')
    for i in range(1,4): print(' ', [m.evaluate(D6[(i,j)], model_completion=True).as_long() for j in range(1,4)])
