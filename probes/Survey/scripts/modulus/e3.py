import sys; sys.path.insert(0,'.')
from ebo import *
import random
random.seed(int(sys.argv[1])); cap=int(sys.argv[2]); ROUNDS=int(sys.argv[3])
def P(u,a): return (u,a,None)
Z=None
def plus(a,b): return unl(lst(a)+lst(b))
one=P(Z,Z)
def nat(n): return natT(n)
def O(u): return P(u,Z)
def psi0(a): return P(Z,a)
w=psi0(one)
O1=O(one); O2=O(nat(2))
eps=psi0(O1)
BO=psi0(P(one,O(nat(2)))) # placeholder big countable
bh=psi0(O(w))
seeds={'psi0(O_w)':bh,'psi0(O_eps)':psi0(O(eps)),'psi0(O_w+1)':psi0(O(sucT(w))),'psi0(O_bh)':psi0(O(bh)),
 'BO':psi0(P(one,P(nat(2),O(nat(3))))) ,'psi0(O_BO)':psi0(O(psi0(P(one,O(nat(2)))))),
 'psi0(psi_w(O_(w+1)))':psi0(P(w,O(sucT(w)))),
 'psi0(O_O)':psi0(O(O1)),'psi0(O_O_O)':psi0(O(O(O1))),'psi0(psi_O(O_{O+1}))':psi0(P(O1,O(sucT(O1)))),
 'psi0(O_{O+w})':psi0(O(plus(O1,w))), 'psi0(O_O*2)':psi0(O(plus(O1,O1))),'psi0(O_O+O_O)':psi0(plus(O(O1),O(O1)))}
stats=dict(pts=0,hit=0,over=0,bad=0,nonNF=0,mod=0,modbad=0)
bads=[]
def chk(t,name):
    if not isOT(t): stats['nonNF']+=1; return
    if not cnt(t) or cof(t)[0]!='cw': return
    for n in range(0,3):
        a,b=fsn(t,n),fsn(t,n+1)
        x=b;i=0;hit=False
        while x is not None and i<cap:
            x=step(x,1);i+=1
            if x==a: hit=True;break
        stats['pts']+=1
        if hit: stats['hit']+=1
        elif x is None: stats['bad']+=1; bads.append((name,t,n))
        else: stats['over']+=1
for name,t0 in seeds.items():
    print(name,'NF',isOT(t0),'cnt',cnt(t0),'cof',cof(t0)[0],flush=True)
    if not isOT(t0): continue
    for r in range(ROUNDS):
        t=t0
        for d in range(random.randint(0,12)):
            if t is None: break
            c=cof(t)[0]
            if c=='c0': break
            k=random.choice([0,1,1,2,3])
            t=step(t,k)
            if t is not None and sz(t)>400 if False else False: break
        if t is None: continue
        chk(t,name)
print(stats)
for b in bads[:6]: print('BAD',b)
