import sys,random
from eboi import *
from closure import closure
import functools as ft
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
def ag(t):
    if not t: return '[]'
    return '('+' ∷ '.join(agP(x) for x in t)+' ∷ [])'
def agP(x):
    if x==IP: return 'I'
    if x[0]=='L': return '(ψI %s)'%ag(x[1])
    return '(ψ %s %s)'%(ag(x[1]),ag(x[2]))
NP=int(sys.argv[1]);SZ=int(sys.argv[2])
seen,steps=closure(4000,700)
R=random.Random(7);L=sorted(seen,key=repr);R.shuffle(L);pool=L[:NP]
raw=[t for n in range(0,SZ+1) for t in genT(n)]
om=[t for t in pool if cof(t)[0]=='w']
hdr=open('hdr.txt').read()
out=[hdr,'pool : List T','pool = '+' ∷\n  '.join(ag(t) for t in pool)+' ∷ []',
'raw : List T','raw = '+' ∷\n  '.join(ag(t) for t in raw)+' ∷ []',
'-- image of raw in OT iff isNF','_ : allB (λ t → eqB (isNF t) (C.isOT (τT t))) raw ≡ true','_ = refl',
'-- every pool term NF and in OT','_ : allB (λ t → isNF t ∧ C.isOT (τT t)) pool ≡ true','_ = refl',
'-- order agrees on all pairs of the pool','_ : allB (λ s → allB (λ t → eqB (s <? t) (O.lt (τT s) (τT t))) pool) pool ≡ true','_ = refl',
'-- closure under fsn, in the real OT and real order; monotone in n',
'ns : List ℕ','ns = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []',
'_ : allB (λ t → cofω t ⇒ allB (λ n → C.isOT (τT (fsn t n)) ∧ isNF (fsn t n) ∧ O.lt (τT (fsn t n)) (τT t) ∧ O.lt (τT (fsn t n)) (τT (fsn t (suc n)))) ns) pool ≡ true','_ = refl','']
open('../setzer/SetzerTest.agda','w').write('\n'.join(out)+'\n')
print('pool',len(pool),'of which w',len(om),'raw',len(raw),'pairs',len(pool)**2,'steps',len(om)*4)
