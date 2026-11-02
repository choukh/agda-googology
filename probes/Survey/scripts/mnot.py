#!/usr/bin/env python3
# Independent transcription of Maksudov's recursive Mahlo notation (Google Sites image):
# terms, <| (Def 10), K, star, G, ominus, tp, a[x]. Test: closure under a[x] from seeds.
import sys, functools, os
PATCH=os.environ.get('PATCH','0')=='1'
PATCH2=os.environ.get('PATCH2','0')=='1'
sys.setrecursionlimit(1000000)
Z=('0',); M=('M',)
def S(*xs):
    fl=[]
    for x in xs:
        if x==Z: continue
        fl+= list(x[1:]) if x[0]=='+' else [x]
    if not fl: return Z
    return fl[0] if len(fl)==1 else ('+',)+tuple(fl)
def P(r,a): return ('p',r,a)
def X(a,b): return ('x',a,b)
def W(a): return ('w',a)
X00=X(Z,Z); ONE=P(X00,Z); OM=P(X00,ONE)
def nat(n): return S(*[ONE]*n)
def times(a,n): return S(*[a]*n)
cache=functools.lru_cache(maxsize=None)
@cache
def lt(a,b):
    if a==b: return False
    if a==Z: return True
    if b==Z: return False
    ta,tb=a[0],b[0]
    if ta=='+' and tb=='+':
        A,B=a[1:],b[1:]
        for x,y in zip(A,B):
            if x!=y: return lt(x,y)
        return len(A)<len(B)
    if ta=='+':            # 10.9 with b in P
        return lt(a[1],b)
    if tb=='+':
        return any(a==y or lt(a,y) for y in b[1:])
    if ta=='w' and tb=='w': return lt(a[1],b[1])
    if ta=='M' and tb=='w': return True
    if ta=='w' and tb=='M': return False
    if ta in 'px' and tb in 'Mw': return True
    if tb in 'px' and ta in 'Mw': return False
    if ta=='x' and tb=='x':
        A,B,C,D=a[1],a[2],b[1],b[2]
        if lt(A,C) and lt(B,b) and lt(star(A),b): return True
        if A==C: return lt(B,D)
        if lt(C,A) and (a==D or lt(a,D) or lt(a,star(C)) or (PATCH and a==star(C))): return True
        return False
    if ta=='x' and tb=='p':
        r,e=b[1],b[2]
        return lt(a,r) and all(lt(y,e) for y in K(r,a))
    if ta=='p' and tb=='x':
        return not lt(b,a)
    if ta=='p' and tb=='p':
        p,bb,r,aa=a[1],a[2],b[1],b[2]
        if lt(p,r) and lt(p,b): return True
        if p==r: return lt(bb,aa)
        if lt(r,p) and lt(a,r): return True
        return False
    raise Exception('lt? %r %r'%(a,b))
def le(a,b): return a==b or lt(a,b)
@cache
def star(a):
    if a==Z or a==M: return Z
    if a[0]=='+':
        m=Z
        for x in a[1:]:
            s=star(x)
            if lt(m,s): m=s
        return m
    if a[0]=='w': return star(a[1])
    return a
@cache
def inP(a): return a[0] in 'Mpxw' and inT(a)
def isL(a):
    if a==M: return True
    if a[0]=='+': return lt(ONE,a[-1])
    if a[0]=='x': return isL(a[2])
    if a[0]=='p': return a!=ONE
    if a[0]=='w': return True
    return False
def isR(a):
    return a[0]=='x' and not isL(a[2]) and inT(a)
@cache
def G(a,b):
    if b[0] not in 'pxMw': return True
    if b[0]=='x':
        return le(b[1],a) or le(b,star(a))
    if b[0]=='p':
        r,e=b[1],b[2]
        return le(r[1],a) or le(r,star(a)) or any(le(e,x) for x in K(r,a))
    raise Exception('G domain %r'%(b,))
@cache
def inT(a):
    t=a[0]
    if t=='0' or t=='M': return True
    if t=='+':
        xs=a[1:]
        return len(xs)>=2 and all(inT(x) and x[0] in 'Mpxw' for x in xs) and all(le(xs[i+1],xs[i]) for i in range(len(xs)-1))
    if t=='x':
        return inT(a[1]) and inT(a[2]) and lt(a[2],M) and G(a[1],a[2])
    if t=='p':
        if a==ONE: return True
        r,b=a[1],a[2]
        return inT(b) and isR(r) and lt(b,M) and all(lt(y,b) for y in K(r,b)) and not (r==X00 and b==Z)
    if t=='w': return inT(a[1]) and lt(M,a[1])
    raise Exception
@cache
def om(r):      # r^ominus
    a,b=r[1],r[2]
    if b==Z: return star(a)
    assert tp(b)==ONE
    b0=fs(b,Z)
    return X(a,b0) if G(a,b0) else b0
@cache
def K(r,a):
    t=a[0]
    if t in '0M': return frozenset()
    if t=='+': return frozenset().union(*[K(r,x) for x in a[1:]])
    if t=='x': return K(r,a[1])|K(r,a[2])
    if t=='w': return K(r,a[1])
    p,b=a[1],a[2]
    m=om(r)
    if le(a,m): return frozenset()
    if lt(p,r): return K(r,p)
    return frozenset([b])|K(r,p)|K(r,b)
@cache
def tp(a):
    t=a[0]
    if t=='0': return Z
    if a==ONE: return ONE
    if t=='+': return tp(a[-1])
    if t=='M': return M
    if t=='x':
        b,c=a[1],a[2]
        if tp(c) in (Z,ONE): return a
        return tp(c)
    if t=='w':
        b=a[1]
        if b==S(M,ONE) or (b[0]=='+' and b[-1]==ONE): return OM
        return tp(b)
    p,b=a[1],a[2]
    pb,pc=p[1],p[2]
    if pb==Z:
        if b==Z or tp(b)==ONE: return OM
    else:
        if b==Z or tp(b)==ONE:
            tb=tp(pb)
            if tb==ONE or tb==M: return OM
            return tb
    tb=tp(b)
    if lt(tb,p): return tb
    return OM
def unnat(x):
    if x==Z: return 0
    if x==ONE: return 1
    assert x[0]=='+' and all(y==ONE for y in x[1:]), x
    return len(x)-1
@cache
def fs(a,x):
    t=a[0]
    if t=='+':
        r=fs(a[-1],x)
        return S(*a[1:-1],r)
    if a==ONE: return Z
    if t=='M': return x
    if t=='x':
        b,c=a[1],a[2]
        if tp(c) in (Z,ONE): return x
        cx=fs(c,x)
        if PATCH2 and not G(b,cx): return cx
        return X(b,cx)
    if t=='w':
        b=a[1]
        if b==S(M,ONE): return times(M,unnat(x))
        if b[0]=='+' and b[-1]==ONE: return times(W(S(*b[1:-1])),unnat(x))
        bx=fs(b,x)
        if PATCH2 and not lt(M,bx): return M if bx==M else (P(X00,bx) if bx!=Z else ONE)
        return W(bx)
    p,b=a[1],a[2]
    pb,pc=p[1],p[2]
    if pb==Z and (b==Z or tp(b)==ONE):
        n=unnat(x)
        if b==Z: return times(om(p),n)            # rule 5
        return times(P(p,fs(b,Z)),n)              # rule 6
    if pb!=Z and (b==Z or tp(b)==ONE):
        tb=tp(pb)
        if tb==ONE or tb==M:
            n=unnat(x)
            if n==0:
                if b!=Z: return S(P(p,fs(b,Z)),ONE)    # 9, 15
                if pc!=Z: return S(om(p),ONE)          # 8, 14
                return Z                               # 7, 13
            prev=fs(a,nat(n-1))
            if tb==ONE: return X(fs(pb,Z),prev)        # 7,8,9
            return X(fs(pb,prev),Z)                    # 13,14,15
        if b==Z and pc==Z: return X(fs(pb,x),Z)        # 10
        if b==Z: return X(fs(pb,x),S(om(p),ONE))       # 11
        return X(fs(pb,x),S(P(p,fs(b,Z)),ONE))         # 12
    tb=tp(b)
    if lt(tb,p): return P(p,fs(b,x))                   # 21
    r=tb                                               # 22
    c=P(r,Z)
    for _ in range(unnat(x)):
        c=P(r,fs(b,c))
    return P(p,fs(b,c))
def size(a):
    return sum(size(y) if isinstance(y,tuple) else 1 for y in a[1:])+1 if a!=Z else 1
def show(a):
    t=a[0]
    if t=='0': return '0'
    if t=='M': return 'M'
    if a==ONE: return '1'
    if t=='+':return '+'.join(show(x) for x in a[1:])
    if t=='x':return 'X(%s,%s)'%(show(a[1]),show(a[2]))
    if t=='p':return 'P[%s](%s)'%(show(a[1]),show(a[2]))
    if t=='w':return 'W(%s)'%show(a[1])
two=nat(2)
Xs=[X(ONE,Z),X(ONE,ONE),X(two,Z),X(OM,Z),X(M,Z),X(S(M,ONE),Z),X(S(M,M),Z),X(W(S(M,ONE)),Z),X(W(W(S(M,ONE))),Z),
    X(ONE,X(ONE,Z)),X(M,ONE),X(X(M,Z),Z),X(S(X(M,Z),ONE),Z),X(S(M,X(ONE,Z)),Z), X(Z,OM),X(Z,X(Z,OM))]
seeds=[]
for x in Xs:
    for s in (x, P(X(x[1],S(x[2],ONE)) if x[2]==Z or tp(x[2])==ONE else X(x[1],Z), ONE)):
        seeds.append(P(X00,s))
        seeds.append(s)
    if x[2]==Z or tp(x[2])==ONE:
        seeds.append(P(x,Z)); seeds.append(P(x,ONE)); seeds.append(P(X00,P(x,Z)))
seeds=[s for s in seeds if inT(s)]
print('seeds',len(seeds))
CAP=int(sys.argv[1]) if len(sys.argv)>1 else 3000
SZ=int(sys.argv[2]) if len(sys.argv)>2 else 400
import heapq
seen=set();work=[(size(a),show(a),a) for a in seeds];heapq.heapify(work);fails={};count=0
def fail(kind,a,x,r=None):
    fails.setdefault(kind,[]).append((show(a),show(x),show(r) if r is not None else ''))
xsamples=[Z,ONE,two,OM,X00,S(X00,ONE)]
import collections
while work and len(seen)<CAP:
    a=heapq.heappop(work)[2]
    if a in seen or a==Z or size(a)>SZ: continue
    seen.add(a)
    try:
        ty=tp(a)
    except Exception as e:
        fail('tp-exc:'+type(e).__name__,a,Z); continue
    if ty==ONE:
        vals=[(Z,0)]
    elif ty==OM:
        vals=[(nat(n),n) for n in range(3)]
    else:
        vals=[(y,0) for y in xsamples+[P(X00,X00)] if lt(y,ty) and inT(y)]
        # include ty-relative samples
        if ty[0]=='x' or ty==M:
            vals+=[(P(ty,Z),0)] if (ty!=M and inT(P(ty,Z))) else []
    prev=None
    for x,_ in vals:
        try:
            r=fs(a,x)
        except Exception as e:
            fail('fs-exc:'+type(e).__name__,a,x); continue
        count+=1
        if not inT(r): fail('notT',a,x,r)
        if not lt(r,a): fail('notLess',a,x,r)
        if ty==OM and prev is not None and not lt(prev,r): fail('notMono',a,x,r)
        prev=r
        if r!=Z and inT(r) and lt(r,a):
            q=r[-1] if r[0]=='+' else r
            heapq.heappush(work,(size(q),show(q),q))
print('terms',len(seen),'steps',count)
for k,v in fails.items():
    print(k,len(v))
    for e in sorted(v,key=lambda e:len(e[0]))[:int(os.environ.get('SHOW','3'))]:
        print('  ',e[0][:150],'|',e[1][:40],'|',e[2][:150])
# --- coverage, order sanity, mutation ---
from collections import Counter
import random
def rule(a):
    t=a[0]
    if t=='+': return 'sum'
    if a==ONE: return '4'
    if t=='M': return '19M'
    if t=='x': return '19' if tp(a[2]) in (Z,ONE) else '20'
    if t=='w':
        b=a[1]
        return '16/17' if (b[0]=='+' and b[-1]==ONE) else '18'
    p,b=a[1],a[2]; pb,pc=p[1],p[2]
    if pb==Z and b==Z: return '5'
    if pb==Z and tp(b)==ONE: return '6'
    if b==Z or tp(b)==ONE:
        tb=tp(pb)
        key=('7' if pc==Z and b==Z else '8' if b==Z else '9') if tb==ONE else ('13' if pc==Z and b==Z else '14' if b==Z else '15') if tb==M else ('10' if pc==Z and b==Z else '11' if b==Z else '12')
        return key
    return '21' if lt(tp(b),p) else '22'
print(sorted(Counter(rule(a) for a in seen).items(), key=lambda kv: (len(kv[0]),kv[0])))
L=random.Random(1).sample(sorted(seen,key=show),min(300,len(seen)))
bad=0;tri=0
R=random.Random(2)
for _ in range(20000):
    a,b,c=R.choice(L),R.choice(L),R.choice(L)
    if lt(a,b) and lt(b,a): bad+=1
    if a!=b and not lt(a,b) and not lt(b,a): bad+=1
    if lt(a,b) and lt(b,c) and not lt(a,c): tri+=1
print('trichotomy bad',bad,'transitivity bad',tri)
def walk(a,rs,limit=200):
    n=0
    while a!=Z and n<limit:
        ty=tp(a)
        if ty==ONE: a=fs(a,Z)
        elif ty==OM: a=fs(a,nat(rs.randint(0,1)))
        else: a=fs(a,Z)
        n+=1
    return n,a==Z
for nm in ('X(M,0)','X(S(M,ONE),0)'):
    a=eval('P(X00,%s)'%nm.replace('0','Z').replace('X(','X('))
    print(show(a),'tp',show(tp(a)),[show(fs(a,x))[:90] for x in (Z,ONE,two)], 'inT',inT(a))
