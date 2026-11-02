from eboi import *
import itertools, collections
O1=Om(ONE);O2=Om(nat(2));W=P(Z,ONE)
A=[LAM,LAM+ONE,Om(LAM+ONE),Om(LAM+nat(2)),Om(LAM+W),P(LAM,ONE),P(LAM,W),P(LAM,Om(LAM+ONE)),P(ONE,Om(LAM+ONE)),
   I,I+ONE,I+I,I+W,I+LAM,Om(I+ONE),Om(I+nat(2)),Om(I+W),Om(I+O1),Om(I+I),Om(Om(I+ONE)),P(I,ONE),P(I,W),P(I,I),P(I,I+ONE),P(I,Om(I+ONE)),P(I+ONE,Om(I+nat(2))),
   P(ONE,I),P(ONE,I+ONE),P(LAM,I),P(O1,I),P(ONE,Om(I+ONE)),
   L(ONE),L(nat(2)),L(W),L(O1),L(O2),L(LAM),L(LAM+ONE),L(Om(LAM+ONE)),L(L(ONE)),L(I),L(I+ONE),L(I+I),L(Om(I+ONE)),L(Om(I+W)),L(P(I,I)),L(P(I,Om(I+ONE))),L(Om(Om(I+ONE))),Om(L(ONE)+ONE),Om(L(W)+W),
   Om(Om(I+ONE)+Om(I+ONE))]
seeds=[P(Z,x) for x in A]+[x for x in A]
print('seeds NF',sum(isNF(s) for s in seeds),'of',len(seeds),'not NF:',[show(s) for s in seeds if not isNF(s)][:12])
print('seeds OT mismatch',[show(s) for s in seeds if isNF(s)!=isOT(tau(s))])
ETAS=[Z,ONE,nat(2),W,O1,LAM,L(ONE),I,P(I,I),Om(I+ONE),P(ONE,ONE),P(Z,O1),P(Z,I)]
seen=set();work=[s for s in seeds if isNF(s)];steps=[];exitsN=[];exitsO=[];notdec=[];nonmono=[];osteps=0
LIMIT=int(sys.argv[1]) if len(sys.argv)>1 else 6000
kinds=collections.Counter()
while work and len(seen)<LIMIT:
    t=work.pop(0)
    if t in seen or not t or len(repr(t))>1200: continue
    seen.add(t)
    c=cof(t)
    kinds[c[0]]+=1
    if c[0] in 'w1':
        ns=[0,1,2,3] if c[0]=='w' else [0]
        rs=[fsn(t,n) for n in ns]
        if c[0]=='w':
            for i in range(len(rs)-1):
                if cmpT(rs[i],rs[i+1])>=0: nonmono.append((t,i))
    else:
        rg=reg(c)
        rs=[fsT(t,e) for e in ETAS if cmpT(e,rg)<0 and isNF(e)]
        osteps+=len(rs)
    for r in rs:
        steps.append((t,r))
        if cmpT(r,t)>=0: notdec.append((t,r))
        if not isNF(r): exitsN.append((t,r))
        if not isOT(tau(r)): exitsO.append((t,r))
        if r and isNF(r): work.append(r)
print('terms',len(seen),'steps',len(steps),'of which Omega/I-indexed',osteps,'kinds',dict(kinds))
print('NF exits',len(exitsN),'OT exits',len(exitsO),'not decreasing',len(notdec),'non-monotone',len(nonmono))
for t,r in sorted(exitsN,key=lambda e:len(show(e[0])))[:6]: print('  NFX',show(t)[:90],'->',show(r)[:110])
for t,r in sorted(notdec,key=lambda e:len(show(e[0])))[:6]: print('  DEC',show(t)[:90],'->',show(r)[:110])
for t,i in sorted(nonmono,key=lambda e:len(show(e[0])))[:6]: print('  MONO',show(t)[:90],i,show(fsn(t,i))[:60],show(fsn(t,i+1))[:60])
L_=sorted(seen,key=repr);R=random.Random(11);bad=0;N=100000;ex=None;ot=0
print('NF/OT mismatch among closure',sum(1 for t in L_ if isNF(t)!=isOT(tau(t))))
for _ in range(N):
    s,t=R.choice(L_),R.choice(L_)
    a=cmpT(s,t);b=ltT(tau(s),tau(t));c=ltT(tau(t),tau(s))
    if (a<0)!=b or (a>0)!=c: bad+=1;ex=(s,t)
print('order disagreements',bad,'of',N, (show(ex[0])[:100],show(ex[1])[:100]) if ex else '')
print('t[n] below t in Setzer failures',sum(1 for t,r in steps if not ltT(tau(r),tau(t))))
# exhaustive small raw terms
def gen(sz):
    if sz==0: return [Z]
    ps=genP(sz);out=[]
    return ps
import functools as ft
@ft.lru_cache(maxsize=None)
def genT(n):
    # lists of total size n
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
allt=[t for n in range(0,6) for t in genT(n)]
print('raw terms size<=5',len(allt))
print('isNF vs isOT.tau mismatch',[show(t) for t in allt if isNF(t)!=isOT(tau(t))][:15], sum(1 for t in allt if isNF(t)!=isOT(tau(t))))
nf=[t for t in allt if isNF(t)];print('NF',len(nf));bad=[(s,t) for s in nf for t in nf if (cmpT(s,t)<0)!=ltT(tau(s),tau(t))]
print('order mismatch on all pairs of small NF',len(bad),[(show(a),show(b)) for a,b in bad[:6]])
eqbad=[(s,t) for s in nf for t in nf if cmpT(s,t)==0 and s!=t];print('cmp eq but distinct among NF',len(eqbad))
ex=[];d=[]
for t in nf:
    c=cof(t)
    if c[0] in 'w1':
        for n in (0,1,2):
            r=fsn(t,n)
            if not isNF(r): ex.append((t,n,r))
            if cmpT(r,t)>=0: d.append((t,n,r))
print('fsn exits NF on small',len(ex),[(show(a),n,show(b)) for a,n,b in ex[:8]],'not dec',len(d))
