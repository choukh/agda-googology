# NF built on p-adic bot's G(X,Y)<|Z, extended; compared with Setzer-derived isNF and isOT; order axioms on samples
from eboi import *
import functools as ft, itertools, collections
def G_(X,Y,Z):
    return all(GP(X,y,Z) for y in Y)
def GP(X,y,Z):
    if y==IP: return True
    if y[0]=='L':
        if cmpT(X,(y,))<0: return cmpT(y[1],Z)<0 and G_(X,y[1],Z)
        return True
    w,c=y[1],y[2]
    if cmpT(X,w)<=0: return cmpT(c,Z)<0 and G_(X,w,Z) and G_(X,c,Z)
    return True
def GI_(Y,Z): return all(GIP(y,Z) for y in Y)
def GIP(y,Z):
    if y==IP: return True
    if y[0]=='L': return cmpT(y[1],Z)<0 and GI_(y[1],Z)
    w,c=y[1],y[2]
    if cmpT(I,w)<=0: return cmpT(c,Z)<0 and GI_(w,Z) and GI_(c,Z)
    return GI_(w,Z)
@ft.lru_cache(maxsize=None)
def NF(t):
    for i in range(len(t)-1):
        if cmpP(t[i+1],t[i])>0: return False
    for x in t:
        if x==IP: continue
        if x[0]=='L':
            if not (NF(x[1]) and GI_(x[1],x[1])): return False
        else:
            u,a=x[1],x[2]
            if not (NF(u) and NF(a) and G_(u,a,a)): return False
            if not a and len(u)==1 and isFi(u[0]): return False
    return True
@ft.lru_cache(maxsize=None)
def genT(n):
    if n==0: return (Z,)
    out=[]
    for k in range(1,n+1):
        for x in genP(k):
            for r in genT(n-k): out.append((x,)+r)
    return tuple(out)
@ft.lru_cache(maxsize=None)
def genP(n):
    out=[]
    if n==1: out.append(IP)
    if n>=1:
        for a in genT(n-1): out.append(('L',a))
        for i in range(n):
            for u in genT(i):
                for a in genT(n-1-i): out.append(('p',u,a))
    return tuple(out)
if __name__!="__main__": raise SystemExit if False else ImportError
N=int(sys.argv[1]) if len(sys.argv)>1 else 6
allt=[t for n in range(0,N) for t in genT(n)]
m=[t for t in allt if NF(t)!=isOT(tau(t))]
print('raw',len(allt),'NF',sum(NF(t) for t in allt),'NF(bot-based) vs OT mismatch',len(m),[show(t) for t in m[:10]])
m2=[t for t in allt if NF(t)!=isNF(t)]
print('NF(bot-based) vs isNF(Setzer-shaped) mismatch',len(m2),[show(t) for t in m2[:10]])
# order axioms
anti=sum(1 for s,t in itertools.product(allt[:1500],repeat=2) if cmpT(s,t)!=-cmpT(t,s))
print('antisymmetry failures on raw (first 1500)^2',anti)
nf=[t for t in allt if NF(t)][:400]
tri=0
for a,b,c in itertools.product(nf[:130],repeat=3):
    if cmpT(a,b)<0 and cmpT(b,c)<0 and not cmpT(a,c)<0: tri+=1
print('transitivity failures on NF triples',tri, 'cmp eq but distinct', sum(1 for s,t in itertools.product(nf,repeat=2) if s!=t and cmpT(s,t)==0))
raw=allt[:150];trr=[(a,b,c) for a,b,c in itertools.product(raw,repeat=3) if cmpT(a,b)<0 and cmpT(b,c)<0 and not cmpT(a,c)<0]
print('transitivity failures on raw triples',len(trr),[tuple(map(show,x)) for x in trr[:3]])
