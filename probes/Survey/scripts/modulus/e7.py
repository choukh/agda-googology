import sys; sys.path.insert(0,'.')
from ebo import *
def P(u,a): return (u,a,None)
Z=None
one=P(Z,Z)
def psi0Om(u): return P(Z,P(u,Z))
def wkq(t,cap):
    n=0
    while t is not None and n<cap: t=step(t,1); n+=1
    return n if t is None else None
for name,t in [('psi0(O2)',psi0Om(natT(2))),('psi0(O3)',psi0Om(natT(3))),('psi0(O_e0)',psi0Om(psi0Om(one))),('psi0(O_BO)',psi0Om(psi0Om(psi0Om(None))))]:
    print(name,wkq(t,6000),flush=True)
