import sys; sys.path.insert(0,'.')
from ebo import *
from functools import lru_cache
N=int(sys.argv[1]); cap=int(sys.argv[2]); szcap=int(sys.argv[3]); nmax=int(sys.argv[4])
def size(t):
    n=0;st=[t]
    while st:
        x=st.pop()
        if x is None: continue
        n+=1;st.extend(x)
        if n>szcap: return n
    return n
tt=[t for s in range(N+1) for t in terms(s) if isOT(t) and cnt(t)]
lim_=[t for t in tt if cof(t)[0]=='cw']
print('NF countable',len(tt),'limit',len(lim_),flush=True)
hit=over=bad=nf=0;bads=[];maxk=0
for t in lim_:
    for n in range(nmax):
        a,b=fsn(t,n),fsn(t,n+1)
        if size(a)>szcap or size(b)>szcap: over+=1; continue
        x=b;i=0;r=None
        while True:
            x=step(x,1);i+=1
            if x==a: r='h';break
            if x is None: r='b';break
            if i>=cap or size(x)>szcap: r='o';break
        if r=='h': hit+=1; maxk=max(maxk,i)
        elif r=='b': bad+=1; bads.append((t,n))
        else: over+=1
print('hit',hit,'over',over,'bad',bad,'maxsteps',maxk,flush=True)
for b_ in bads[:6]: print('BAD',b_)
# modulus check: j<i both NF cnt, i limit: first m with j<=i[m] must be <= wk(j)+1 ; also compare with 'norm'
md=0;mbad=0;tight=0
import random
random.seed(3)
small=[t for t in tt if size(t)<=N]
wkc={}
def wkf(t):
    if t in wkc: return wkc[t]
    x=t;i=0
    while x is not None and i<cap:
        if size(x)>szcap: wkc[t]=None; return None
        x=step(x,1);i+=1
    wkc[t]= i if x is None else None
    return wkc[t]
for _ in range(40000):
    j,i=random.choice(small),random.choice(lim_)
    if cmpT(j,i)!='lt': continue
    w=wkf(j)
    if w is None: continue
    m=0;f=None
    while m<=w+1:
        c=fsn(i,m)
        if size(c)>szcap*4: break
        if cmpT(j,c)!='gt': f=m;break
        m+=1
    md+=1
    if f is None:
        if m>w+1: mbad+=1; print('MODBAD',j,i,w)
    else:
        tight=max(tight,f-w)
print('modulus pairs',md,'mbad',mbad,'max(M-wk)',tight,flush=True)
