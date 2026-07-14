#!/usr/bin/env python3
import sys
sys.path.insert(0,'/mnt/data/groth_v42/scripts')
from z3 import *
from order4sat_beyond import BiDual
from s2check import build_blocks
R=BiDual; fib={(1,2,3):1}
models={
 'W2F':{(2,1,1):1,(3,1,2):1,(3,2,1):1},
 'mu2a2':{(1,1,1):1,(3,1,2):1,(3,2,1):1,(3,1,3):1,(3,3,1):1},
}
def pin(c,m): return [val[0]==(1 if m.get(key,0) else 0) for key,val in c.items()]
def shape_W(phi):
 cons=[]
 for idx in [1,2]:
  for r in range(1,4): cons.append(phi[1][r][idx]==0)
  for r in range(1,4): cons.append(phi[3][r][idx]==0)
  cons += [phi[2][2][idx]==0, phi[2][3][idx]==0]
 return cons
def Tx_W(phi): return [phi[1][2][3]==0, phi[1][3][3]==0]
def shape_E(phi):
 cons=[]
 for idx in [1,2]:
  for r in range(1,4): cons.append(phi[2][r][idx]==0)
  for r in range(1,4): cons.append(phi[3][r][idx]==0)
  cons += [phi[1][1][idx]==0, phi[1][3][idx]==0]
 return cons
def Ty_E(phi): return [phi[2][1][3]==0, phi[2][3][3]==0]
def run_W():
 A,M,C,F,phi,c,Mtab=build_blocks(R,fib); s=Solver(); s.set('timeout',120000)
 for e in A+M+C+F+pin(c,models['W2F'])+shape_W(phi)+Tx_W(phi): s.add(e)
 p=phi[2][1][1]; q=phi[2][1][2]; rho=phi[2][2][3]
 # over F2, rho notin (p,q) iff p=q=0 and rho=1
 s.add(p==0,q==0,rho!=0)
 print('W2F rho not in (lambda_u,lambda_v) over F2:', s.check())
def run_E():
 A,M,C,F,phi,c,Mtab=build_blocks(R,fib); s=Solver(); s.set('timeout',120000)
 for e in A+M+C+F+pin(c,models['mu2a2'])+shape_E(phi)+Ty_E(phi): s.add(e)
 p=phi[1][2][1]; q=phi[1][2][2]; rho=phi[1][1][3]
 s.add(p==0,q==0,rho!=0)
 print('mu2a2 rho not in (lambda_u,lambda_v) over F2:', s.check())
set_param('parallel.enable', True)
run_W(); run_E()
