#!/usr/bin/env python3
# Python transcription of EBOI (T^I): term = tuple of PT; PT = ('p',u,a) | ('L',a) [psi_I a] | ('I',)
import sys, functools, random
sys.setrecursionlimit(1000000)
Z=()
ONEP=('p',Z,Z); ONE=(ONEP,)
IP=('I',); I=(IP,)
def P(u,a): return (('p',u,a),)
def L(a): return (('L',a),)
LAM=L(Z)
def nat(n): return ONE*n
def suc(a): return a+ONE
def isFi(x): return x[0] in 'IL'
def then(a,b): return a if a else b
def c0(a): return 1 if a else 0
@functools.lru_cache(maxsize=None)
def cmpT(s,t):
    for x,y in zip(s,t):
        c=cmpP(x,y)
        if c: return c
    return (len(s)>len(t))-(len(s)<len(t))
@functools.lru_cache(maxsize=None)
def cmpP(x,y):
    if x[0]=='p' and y[0]=='p': return then(cmpT(x[1],y[1]),cmpT(x[2],y[2]))
    if x[0]=='p': return then(cmpT(x[1],(y,)),c0(x[2]))
    if y[0]=='p': return then(cmpT((x,),y[1]),-c0(y[2]))
    if x[0]=='L' and y[0]=='L': return cmpT(x[1],y[1])
    if x[0]=='L': return -1
    if y[0]=='L': return 1
    return 0
def pred(a):
    if not a: return a
    return a[:-1] if a[-1]==ONEP else a
def idx(r): return suc(r[1]) if r[0]=='O' else I
def reg(r): return P(suc(r[1]),Z) if r[0]=='O' else I
RI=('RI',)
@functools.lru_cache(maxsize=None)
def cof(t):
    if not t: return ('0',)
    x=t[-1]
    if x==ONEP: return ('1',)
    if x==IP: return RI
    if x[0]=='L':
        a=x[1]
        if not a: return ('w',)
        c=cof(a)
        if c[0] in '1w': return ('w',)
        return c if cmpT(idx(c),I)<0 else ('w',)
    u,a=x[1],x[2]
    if not a:
        c=cof(u)
        if c[0]=='1': return ('O',pred(u))
        return c
    c=cof(a)
    if c[0] in '1w': return ('w',)
    return c if cmpT(idx(c),u)<=0 else ('w',)
idx_=idx
def idx(c): return suc(c[1]) if c[0]=='O' else I
def Om(u):
    if len(u)==1 and isFi(u[0]): return u
    return P(u,Z)
def psi(u,a): return P(u,a) if a else Om(u)
def base(r): return Om(r[1]) if r[0]=='O' else LAM
def step(r,x): return psi(r[1],x) if r[0]=='O' else L(x)
def fsT(t,e):
    if not t: return Z
    x=t[-1]; h=t[:-1]
    if x==ONEP: return h
    if x==IP: return h+e
    if x[0]=='L': return h+L(fsT(x[1],e))
    u,a=x[1],x[2]
    if not a:
        if cof(u)[0]=='1': return h+e
        return h+Om(fsT(u,e))
    return h+psi(u,fsT(a,e))
def gam(b,r,k):
    g=base(r)
    for _ in range(k): g=step(r,fsT(b,g))
    return g
def tower(t,n):
    for _ in range(n): t=P(t,Z)
    return t
def fsn(t,n):
    if not t: return Z
    x=t[-1];h=t[:-1]
    if x==ONEP: return h
    if x==IP: return h+nat(n)
    if x[0]=='L':
        a=x[1]
        if not a: return h+tower(ONE,n)
        c=cof(a)
        if c[0]=='1': return h+tower(L(pred(a))+ONE,n)
        if c[0]=='w': return h+L(fsn(a,n))
        if cmpT(idx(c),I)<0: return h+L(fsT(a,nat(n)))
        return h+L(fsT(a,gam(a,c,n)))
    u,a=x[1],x[2]
    if not a:
        c=cof(u)
        if c[0]=='1': return h+nat(n)
        if c[0]=='w': return h+Om(fsn(u,n))
        return h+Om(fsT(u,nat(n)))
    c=cof(a)
    if c[0]=='1': return h+psi(u,pred(a))*n
    if c[0]=='w': return h+psi(u,fsn(a,n))
    if cmpT(idx(c),u)<=0: return h+psi(u,fsT(a,nat(n)))
    return h+psi(u,fsT(a,gam(a,c,n)))
# --- G and NF, transcribing Setzer Def 2.7 through tau
def ge_level(pi,v):   # pi <= level of psi_v(.)
    if pi is None: return cmpT(I,v)<=0        # pi = I, I <= Omega'_{v+1} iff I <= v
    return cmpT(pi,v)<=0                      # Omega'_{u+1} <= Omega'_{v+1} iff u<=v
def G(pi,t):
    out=[]
    for x in t:
        if x==ONEP or x==IP: continue
        if x[0]=='L':
            b=x[1]
            if pi is None: out+=[b]+G(pi,b)
            elif cmpT(pi,(x,))<0: out+=[b]+G(pi,b)
        else:
            v,b=x[1],x[2]
            if not b: out+=G(pi,v)
            elif ge_level(pi,v): out+=[b]+G(pi,v)+G(pi,b)
            elif pi is None: out+=G(pi,v)
    return out
@functools.lru_cache(maxsize=None)
def isNF(t):
    for i in range(len(t)-1):
        if cmpP(t[i+1],t[i])>0: return False
    for x in t:
        if x==ONEP or x==IP: continue
        if x[0]=='L':
            if not isNF(x[1]): return False
            if not all(cmpT(g,x[1])<0 for g in G(None,x[1])): return False
        else:
            u,a=x[1],x[2]
            if not isNF(u) or not isNF(a): return False
            if not a:
                if len(u)==1 and isFi(u[0]): return False
            elif not all(cmpT(g,a)<0 for g in G(u,a)): return False
    return True
# --- Setzer OT_I transcription, full Order/Closure with psi_I and I
ZS=(); ONES=(('phi',ZS,ZS),)
@functools.lru_cache(maxsize=None)
def tau(t):
    r=()
    for x in t:
        if x==ONEP: r+=ONES
        elif x==IP: r+=(('Ip',),)
        elif x[0]=='L': r+=(('psi',('IR',),tau(x[1])),)
        elif not x[2]: r+=(('Om',tau(x[1])),)
        else: r+=(('psi',('OR',tau(x[1])+ONES),tau(x[2])),)
    return r
@functools.lru_cache(maxsize=None)
def ltT(s,t):
    for p,q in zip(s,t):
        if p!=q: return ltP(p,q)
    return len(s)<len(t)
def leT(s,t): return s==t or ltT(s,t)
def regTm(r): return (('Ip',),) if r[0]=='IR' else (('Om',r[1]),)
def ltTP(t,p): return ltT(t,(p,))
def lePT(p,t): return ltT((p,),t) or t==(p,)
@functools.lru_cache(maxsize=None)
def ltP(p,q):
    a,b=p[0],q[0]
    IPs=('Ip',)
    if a=='phi' and b=='phi':
        return (ltT(p[1],q[1]) and ltTP(p[2],q)) or (p[1]==q[1] and ltT(p[2],q[2])) or (ltT(q[1],p[1]) and lePT(p,q[2]))
    if a=='phi': return ltTP(p[1],q) and ltTP(p[2],q)
    if a=='psi' and b=='psi':
        pi,ka=p[1],q[1]
        if pi==ka and ltT(p[2],q[2]): return True
        pI=pi[0]=='IR'; kI=ka[0]=='IR'
        if not pI and not kI: return ltT(regTm(pi),regTm(ka))
        if pI and not kI: return ltP(p,('Om',ka[1]))
        if not pI and kI: return ltTP(regTm(pi),q)
        return False
    if a=='psi' and b=='Om':
        if p[1][0]=='OR': return leT((('Om',p[1][1]),),(q,))
        return lePT(p,q[1])
    if a=='psi' and b=='Ip':
        if p[1][0]=='OR': return leT((('Om',p[1][1]),),(IPs,))
        return True
    if a=='psi' and b=='phi': return not (ltTP(q[1],p) and ltTP(q[2],p))
    if a=='Om' and b=='Om': return ltT(p[1],q[1])
    if a=='Om' and b=='Ip': return ltT(p[1],(IPs,))
    if a=='Om' and b=='phi': return not (ltTP(q[1],p) and ltTP(q[2],p))
    if a=='Om' and b=='psi':
        if q[1][0]=='OR': return not leT((('Om',q[1][1]),),(p,))
        return not lePT(q,p[1])
    if a=='Ip' and b=='Ip': return False
    if a=='Ip' and b=='phi': return not (ltTP(q[1],p) and ltTP(q[2],p))
    if a=='Ip' and b=='psi':
        if q[1][0]=='OR': return not leT((('Om',q[1][1]),),(IPs,))
        return False
    if a=='Ip' and b=='Om': return not ltT(q[1],(IPs,))
    raise Exception((a,b))
def GS(pi,t):
    out=[]
    for p in t:
        if p[0]=='phi': out+=GS(pi,p[1])+GS(pi,p[2])
        elif p[0]=='Om': out+=GS(pi,p[1])
        elif p[0]=='Ip': pass
        else:
            ka,b=p[1],p[2]
            if ka[0]=='IR':
                if pi[0]=='IR': out+=[b]+GS(pi,b)
                elif leT(regTm(pi),(p,)): out+=[b]+GS(pi,b)
            else:
                c=ka[1]
                if leT(regTm(pi),(('Om',c),)): out+=[b]+GS(pi,c)+GS(pi,b)
                elif pi[0]=='IR': out+=GS(pi,c)
    return out
def isFiS(t): return len(t)==1 and (t[0][0]=='Ip' or (t[0][0]=='psi' and t[0][1][0]=='IR'))
def isSucS(t): return bool(t) and t[-1]==ONES[0]
@functools.lru_cache(maxsize=None)
def isOT(t):
    if len(t)>1 and not all(leT((t[i+1],),(t[i],)) for i in range(len(t)-1)): return False
    for p in t:
        if p[0]=='Om':
            if not p[1] or isFiS(p[1]) or not isOT(p[1]): return False
        elif p[0]=='psi':
            b=p[2]
            if not isOT(b): return False
            if p[1][0]=='OR':
                c=p[1][1]
                if not isOT(c) or not isSucS(c) or isFiS(c): return False
            if not all(ltT(g,b) for g in GS(p[1],b)): return False
        elif p[0]=='phi':
            if p[1] or p[2]: return False
    return True
def show(t):
    if not t: return '0'
    o=[]
    for x in t:
        if x==ONEP:o.append('1')
        elif x==IP:o.append('I')
        elif x[0]=='L':o.append('pI(%s)'%show(x[1]))
        elif not x[2]:o.append('O[%s]'%show(x[1]))
        else:o.append('p[%s](%s)'%(show(x[1]),show(x[2])))
    return '+'.join(o)
