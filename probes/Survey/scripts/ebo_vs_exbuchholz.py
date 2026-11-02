# Own transliteration of EBO.lagda.md (cof, pred, fsT, gammaT, fsn) and of the Lean ExBuchholz dom/fs,
# compared under the bijection [] <-> nil, psi u a :: t <-> cons u a t. Exhaustive on small terms. Test, not proof.
import sys, itertools, functools
sys.setrecursionlimit(100000)
MUT = sys.argv[1] if len(sys.argv)>1 else ''
# ---- one shared representation: Lean-style nil=None, cons=(a,b,t); ours reads it as list via the bijection
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
# ---- LEAN (transliteration of FS.lean dom, fs)
t1=(nil,nil,nil); tw=(nil,t1,nil)
def Lcmp(x,y):
    if x is None and y is None: return 'eq'
    if x is None: return 'lt'
    if y is None: return 'gt'
    c=Lcmp(x[0],y[0])
    if c!='eq': return c
    c=Lcmp(x[1],y[1])
    if c!='eq': return c
    return Lcmp(x[2],y[2])
@functools.lru_cache(maxsize=None)
def dom(X):
    if X is None: return None
    if X[2] is not None: return dom(X[2])
    X1,X2=X[0],X[1]
    d2=dom(X2)
    if d2 is None:
        d1=dom(X1)
        if d1 is None or d1==t1: return X
        return d1
    if d2==t1 or d2==tw: return tw
    if Lcmp(d2,X)=='lt': return d2
    return tw
def isNum(t): return t is None or (t[0] is None and t[1] is None and isNum(t[2]))
def numVal(t):
    n=0
    while t is not None: n+=1; t=t[2]
    return n
def numPred(t): return None if t is None else t[2]
def numeral(n):
    r=None
    for _ in range(n): r=(None,None,r)
    return r
def rep(A,B,n):
    r=None
    for _ in range(n): r=(A,B,r)
    return r
def subOf(t): return None if t is None else t[0]
def fs(X,Y):
    if X is None: return None
    if X[2] is not None: return (X[0],X[1],fs(X[2],Y))
    X1,X2=X[0],X[1]
    d2=dom(X2)
    if d2 is None:
        d1=dom(X1)
        if d1 is None: return None
        if d1==t1: return Y
        return (fs(X1,Y),None,None)
    if d2==t1:
        return rep(X1,fs(X2,None),numVal(Y)) if isNum(Y) else None
    if d2==tw: return (X1,fs(X2,Y),None)
    if Lcmp(d2,X)=='lt': return (X1,fs(X2,Y),None)
    base=(fs(subOf(d2),None),None,None)
    if Y is not None and isNum(Y):
        prev=fs(X,numPred(Y))
        if prev is not None and prev[2] is None and prev[0]==X1:
            return (X1,fs(X2,(fs(subOf(d2),None),prev[1],None)),None)
    return (X1,fs(X2,base),None)
def size(t): return 0 if t is None else 1+size(t[0])+size(t[1])+size(t[2])
# enumerate all terms by size
by={0:[None]}
N=int(sys.argv[2]) if len(sys.argv)>2 else 8
for s in range(1,N+1):
    o=[]
    for i in range(s):
        for j in range(s-i):
            k=s-1-i-j
            for a in by[i]:
                for b in by[j]:
                    for t in by[k]: o.append((a,b,t))
    by[s]=o
ALL=[t for s in range(N+1) for t in by[s]]
# G, isOT (Std.lean)
def le(x,y): return Lcmp(x,y)!='gt'
def G(a,t):
    r=[]
    while t is not None:
        c,d,nx=t
        if le(a,c): r=r+[d]+G(a,c)+G(a,d)
        t=nx
    return r
@functools.lru_cache(maxsize=None)
def isOT(t):
    if t is None: return True
    a,b,nx=t
    if not(isOT(a) and isOT(b) and all(Lcmp(x,b)=='lt' for x in G(a,b)) and isOT(nx)): return False
    return nx is None or le((nx[0],nx[1],None),(a,b,None))
def h(c):
    if c[0]=='c0': return None
    if c[0]=='c1': return t1
    if c[0]=='cw': return tw
    return (sucT(c[1]),None,None)
stats=dict(terms=len(ALL),ot=0,cmp=0,cmpbad=0,dom=0,dombad=0,fsn=0,fsnbad=0,fsT=0,fsTbad=0,gamma=0)
ex=[]
etas=[t for s in range(0,4) for t in by[s]]
for t in ALL:
    if isOT(t): stats['ot']+=1
    stats['dom']+=1
    if dom(t)!=h(cof(t)): stats['dombad']+=1; ex.append(('dom',t))
    if t is None: continue
    for n in range(5):
        stats['fsn']+=1
        if fsn(t,n)!=fs(t,numeral(n)): stats['fsnbad']+=1; ex.append(('fsn',t,n))
    if cof(t)[0]=='cO':
        for eta in etas:
            stats['fsT']+=1
            if fsT(t,eta)!=fs(t,eta): stats['fsTbad']+=1; ex.append(('fsT',t,eta))
import random
random.seed(1)
for _ in range(200000):
    x,y=random.choice(ALL),random.choice(ALL)
    stats['cmp']+=1
    if cmpT(x,y)!=Lcmp(x,y): stats['cmpbad']+=1
print(stats); print(ex[:3])
# isOT^e from EBOI.lagda.md (Bool form) vs Lean isOT (list form)
def GE(X,Y,Z):
    return all(GEP(X,w,c,Z) for (w,c) in lst(Y))
def GEP(X,w,c,Z):
    return (Lcmp(c,Z)=='lt' and GE(X,w,Z) and GE(X,c,Z)) if Lcmp(X,w)!='gt' else True
def isOTe(t):
    L=lst(t)
    for i,(u,a) in enumerate(L):
        if not isOTe(u): return False
        if a is not None and not (isOTe(a) and GE(u,a,a)): return False
        if i+1<len(L):
            y=L[i+1]; x=L[i]
            if Lcmp(unl([y]),unl([x]))=='gt': return False
    return True
bad=sum(1 for t in ALL if isOTe(t)!=isOT(t)); print('isOTe vs isOT mismatches',bad,'of',len(ALL))
