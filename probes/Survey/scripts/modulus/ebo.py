import sys, itertools, functools
sys.setrecursionlimit(100000)
MUT=''
nil=None
def cons(a,b,t): return (a,b,t)
def lst(t):
    o=[]
    while t is not None: o.append((t[0],t[1])); t=t[2]
    return o
def unl(l):
    r=None
    for (a,b) in reversed(l): r=(a,b,r)
    return r
# ---- OURS, written over python lists of pairs (terms are None/tuple but processed clause by clause)
def cmpT(x,y):
    X,Y=lst(x),lst(y)
    i=0
    while True:
        if i==len(X) and i==len(Y): return 'eq'
        if i==len(X): return 'lt'
        if i==len(Y): return 'gt'
        c=cmpT(X[i][0],Y[i][0])
        if c!='eq': return c
        c=cmpT(X[i][1],Y[i][1])
        if c!='eq': return c
        i+=1
ONE=[(nil,nil)]
one=unl(ONE)
def sucT(a): return unl(lst(a)+ONE)
def pred(a):
    L=lst(a)
    if not L: return nil
    if L[-1]==(nil,nil): return unl(L[:-1])
    return a
@functools.lru_cache(maxsize=None)
def cof(a):
    L=lst(a)
    if not L: return ('c0',)
    if len(L)>1: return cof(unl(L[-1:]))
    u,b=L[0]
    if b is not None: return cofA(u,cof(b))
    if u is None: return ('c1',)
    return cofpsi0(u,cof(u))
def cofpsi0(u,c):
    if c[0]=='c0': return c
    if c[0]=='c1': return ('cO',pred(u))
    return c
def cofA(u,c):
    if c[0] in('c0','c1','cw'): return ('cw',)
    return cofpsiP(u,c[1],cmpT(sucT(c[1]),u))
def cofpsiP(u,mu,m): return ('cO',mu) if m in('lt','eq') else ('cw',)
def natT(n): return unl(ONE*n)
def Ot(mu): return unl([(mu,nil)])
def fsT(a,eta):
    L=lst(a)
    if not L: return nil
    if len(L)>1: return unl([L[0]])[:2]+(fsT(unl(L[1:]),eta),)
    u,b=L[0]
    if b is not None: return fsTp(u,b,cof(b),eta)
    if u is None: return nil
    return fsT0(u,cof(u),eta)
def fsT0(u,c,eta):
    if c[0]=='c1': return eta
    if c[0]=='cO': return unl([(fsT(u,eta),nil)])
    return unl([(u,nil)])
def fsTp(u,b,c,eta):
    if c[0]!='cO': return unl([(u,b)])
    m=cmpT(sucT(c[1]),u)
    if m in('lt','eq'): return unl([(u,fsT(b,eta))])
    return unl([(u,b)])
def gT(beta,mu,k):
    if k==0:
        if MUT=='gamma0': return one
        return Ot(mu)
    return unl([(mu,fsT(beta,gT(beta,mu,k-1)))])
def fsn(t,n):
    L=lst(t)
    if not L: return nil
    if len(L)>1: return unl([L[0]])[:2]+(fsn(unl(L[1:]),n),)
    u,b=L[0]
    if b is not None:
        c=cof(b)
        if c[0]=='c0': return nil
        if c[0]=='c1':
            if MUT=='rep': return unl([(u,pred(b))]*(n+1))
            return unl([(u,pred(b))]*n)
        if c[0]=='cw': return unl([(u,fsn(b,n))])
        nu=c[1]; m=cmpT(sucT(nu),u)
        if m=='gt': return unl([(u,fsT(b,gT(b,nu,n)))])
        return unl([(u,fsT(b,natT(n)))])
    if u is None: return nil
    c=cof(u)
    if c[0]=='c0': return nil
    if c[0]=='c1': return natT(n)
    if c[0]=='cw': return unl([(fsn(u,n),nil)])
    return unl([(fsT(u,natT(n)),nil)])
def GE(X,Y,Z): return all(GEP(X,w,c,Z) for (w,c) in lst(Y))
def GEP(X,w,c,Z):
    return (cmpT(c,Z)=='lt' and GE(X,w,Z) and GE(X,c,Z)) if cmpT(X,w)!='gt' else True
@functools.lru_cache(maxsize=None)
def isOT(t):
    L=lst(t)
    for i,(u,a) in enumerate(L):
        if not isOT(u): return False
        if a is not None and not (isOT(a) and GE(u,a,a)): return False
        if i+1<len(L):
            if cmpT(unl([L[i+1]]),unl([L[i]]))=='gt': return False
    return True
def cnt(t): return all(u is None for (u,a) in lst(t))
def step(t,k):
    c=cof(t)
    if c[0]=='c0': return None
    if c[0]=='c1': return pred(t)
    return fsn(t,k)
def walk(t,k,cap=20000):
    "returns list of terms on the k-walk, or None on overrun"
    o=[t]
    while t is not None:
        t=step(t,k)
        o.append(t)
        if len(o)>cap: return None
    return o
def wlen(t,k,cap=20000):
    n=0
    while t is not None:
        t=step(t,k); n+=1
        if n>cap: return None
    return n
@functools.lru_cache(maxsize=None)
def terms(s):
    "all raw terms of size exactly s (size= number of psi nodes)"
    if s==0: return (nil,)
    r=[]
    for su in range(s):
        for sa in range(s-su):
            st=s-1-su-sa
            for u in terms(su):
              for a in terms(sa):
                for t in terms(st):
                    r.append((u,a,t))
    return tuple(r)
