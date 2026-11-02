#!/usr/bin/env python3
# Order-embedding tests of EBO terms: into Setzer OT_I (fragment of Order/Closure transcribed)
# and into the Maksudov Mahlo notation; FS agreement EBO vs Mahlo system.
import random, sys, functools, os
sys.setrecursionlimit(1000000)
src=open('cmp.py').read()
exec(src[:src.index('# T_W')])            # EBO: P,Z,ONE,cmp,fs,cof,add,succ,nat,Om,...
EBO=dict(P=P,Z=Z,ONE=ONE,cmp=cmp,fs=fs,cof=cof,add=add,succ=succ,nat=nat,Om=Om,is_succ=is_succ,pred=pred)
O1=Om(ONE);O2=Om(nat(2));O3=Om(nat(3));Wm=P(Z,ONE);Ow=Om(Wm);OO1=Om(O1);OOO=Om(OO1)
seeds=[P(Z,x) for x in [O1,add(O1,O1),P(ONE,ONE),P(ONE,O1),P(ONE,O2),P(ONE,add(O2,O2)),O2,O3,P(nat(2),O3),P(ONE,P(nat(2),O3)),Ow,P(Wm,Z),add(Ow,O1),OO1,OOO,Om(add(O1,O1)),Om(P(ONE,O1)),P(O1,Om(succ(O1))),Om(succ(O1)),P(ONE,Om(succ(O1))),add(OO1,O2),Om(Ow)]]
seen=set();work=list(seeds);om_step=[]
while work and len(seen)<2500:
    t=work.pop(0)
    if t in seen or not t or len(repr(t))>600: continue
    seen.add(t)
    if cof(t)[0]=='w':
        for n in range(3):
            r=fs(t,n);om_step.append((t,n,r))
            if r: work.append(r)
    elif cof(t)[0]=='1':
        work.append(fs(t,0))
terms=sorted(seen,key=repr); print('EBO terms',len(terms),'steps',len(om_step))
# --- Setzer OT_I
ZS=()
ONE_S=(('phi',ZS,ZS),)
@functools.lru_cache(maxsize=None)
def tauS(t):
    r=()
    for u,a in t:
        if not u and not a: r+=ONE_S
        elif not a: r+=(('Om',tauS(u)),)
        else: r+=(('psi',('OR',tauS(u)+ONE_S),tauS(a)),)
    return r
@functools.lru_cache(maxsize=None)
def ltT(s,t):
    for p,q in zip(s,t):
        if p!=q: return ltP(p,q)
    return len(s)<len(t)
def leT(s,t): return s==t or ltT(s,t)
def regTm(r): return (('Om',r[1]),)
def ltTP(t,p): return ltT(t,(p,))
def lePT(p,t): return ltT((p,),t) or t==(p,)
@functools.lru_cache(maxsize=None)
def ltP(p,q):
    a,b=p[0],q[0]
    if a=='phi' and b=='phi':
        return (ltT(p[1],q[1]) and ltTP(p[2],q)) or (p[1]==q[1] and ltT(p[2],q[2])) or (ltT(q[1],p[1]) and lePT(p,q[2]))
    if a=='phi': return ltTP(p[1],q) and ltTP(p[2],q)
    if a=='psi' and b=='psi':
        return p[1]==q[1] and ltT(p[2],q[2]) or ltT(regTm(p[1]),regTm(q[1]))
    if a=='psi' and b=='Om': return leT(((('Om',p[1][1])),),((q),))
    if a=='psi' and b=='phi': return not (ltTP(q[1],p) and ltTP(q[2],p))
    if a=='Om' and b=='Om': return ltT(p[1],q[1])
    if a=='Om' and b=='phi': return not (ltTP(q[1],p) and ltTP(q[2],p))
    if a=='Om' and b=='psi': return not leT(((('Om',q[1][1])),),(p,))
    raise Exception
def Gs(pi,t):
    out=[]
    for p in t:
        if p[0]=='phi': out+=Gs(pi,p[1])+Gs(pi,p[2])
        elif p[0]=='Om': out+=Gs(pi,p[1])
        else:
            c=p[1][1];b=p[2]
            if leT(regTm(pi),(('Om',c),)): out+=[b]+Gs(pi,c)+Gs(pi,b)
    return out
@functools.lru_cache(maxsize=None)
def isOT(t):
    if len(t)>1 and not all(leT((t[i+1],),(t[i],)) for i in range(len(t)-1)): return False
    for p in t:
        if p[0]=='Om':
            if not p[1] or not isOT(p[1]): return False
        elif p[0]=='psi':
            c=p[1][1];b=p[2]
            if not isOT(c) or not c or c[-1]!=ONE_S[0] or not isOT(b): return False
            if not all(ltT(g,b) for g in Gs(p[1],b)): return False
        elif p[0]=='phi':
            if p[1] or p[2]: return False
    return True
badOT=[t for t in terms if not isOT(tauS(t))]
print('Setzer: not in OT',len(badOT)); 
R=random.Random(5);bad=0;N=60000
for _ in range(N):
    s,t=R.choice(terms),R.choice(terms)
    if (cmp(s,t)<0)!=ltT(tauS(s),tauS(t)): bad+=1; ex=(s,t)
print('Setzer: order disagreements',bad,'of',N)
fixbad=[(t,n,r) for t,n,r in om_step if r and not ltT(tauS(r),tauS(t))]
print('Setzer: t[n] not below t',len(fixbad))

def show(t):
    if not t: return '0'
    out=[]
    for u,a in t:
        if not u and not a: out.append('1')
        elif not a: out.append('O[%s]'%show(u))
        else: out.append('p[%s](%s)'%(show(u),show(a)))
    return '+'.join(out)
def showS(t):
    if not t: return '0'
    o=[]
    for p in t:
        if p[0]=='phi': o.append('1')
        elif p[0]=='Om': o.append('Om[%s]'%showS(p[1]))
        else: o.append('psi[%s](%s)'%(showS(p[1][1]),showS(p[2])))
    return '+'.join(o)
badOT.sort(key=lambda t:len(show(t)))
def culprit(T):
    for p in T:
        if p[0]=='Om':
            c=culprit(p[1])
            if c: return c
        elif p[0]=='psi':
            c=culprit(p[1][1]) or culprit(p[2])
            if c: return c
            bad=[g for g in Gs(p[1],p[2]) if not ltT(g,p[2])]
            if bad: return (p,bad[0])
    return None
from collections import Counter
for t in badOT[:6]:
    c=culprit(tauS(t))
    print(show(t)[:110]);print('   culprit',showS((c[0],))[:110],' G-elt',showS(c[1])[:70]) if c else print('   other', isOT(tauS(t)))
print('--- closure from seeds whose image is in OT')
good=[s for s in seeds if isOT(tauS(s))]; print('seeds in OT',len(good),'of',len(seeds),'rejected:',[show(s)[:40] for s in seeds if not isOT(tauS(s))])
seen2=set();work=list(good);steps=[];exits=[]
while work and len(seen2)<3000:
    t=work.pop(0)
    if t in seen2 or not t or len(repr(t))>800: continue
    seen2.add(t)
    c=cof(t)[0]
    vals=[0,1,2] if c=='w' else ([0] if c=='1' else [])
    for n in vals:
        r=fs(t,n);steps.append((t,n,r))
        if r:
            if isOT(tauS(r)): work.append(r)
            else: exits.append((t,n,r))
print('terms',len(seen2),'steps',len(steps),'exits from OT',len(exits))
for t,n,r in sorted(exits,key=lambda e:len(show(e[0])))[:4]:
    print('  ',show(t)[:100],n,show(r)[:100])
L=sorted(seen2,key=repr);bad=0
for _ in range(60000):
    s,t=R.choice(L),R.choice(L)
    if (cmp(s,t)<0)!=ltT(tauS(s),tauS(t)): bad+=1
print('order disagreements',bad,'of 60000')
print('t[n] below t failures',sum(1 for t,n,r in steps if r and not ltT(tauS(r),tauS(t))))
print('EBO order: t[n] below t failures',sum(1 for t,n,r in steps if r and cmp(r,t)>=0))
print('--- into Maksudov Mahlo notation')
os.environ['PATCH']='1';os.environ['PATCH2']='1'
ms=open('mnot.py').read(); NS={}
exec(ms[:ms.index('two=nat(2)')],NS)
mZ,mONE,mX,mP,mS,mX00=NS['Z'],NS['ONE'],NS['X'],NS['P'],NS['S'],NS['X00']
mlt,minT,mfs,mtp,mnat=NS['lt'],NS['inT'],NS['fs'],NS['tp'],NS['nat']
def m1(t):
    if t==mONE: return mZ
    if t[0]=='+' and t[1]==mONE: return mS(*t[2:])
    return t
@functools.lru_cache(maxsize=None)
def tauM(t):
    r=[]
    for u,a in t:
        if not u and not a: r.append(mONE)
        elif not a: r.append(mX(mZ,m1(tauM(u))))
        elif not u: r.append(mP(mX00,tauM(a)))
        else: r.append(mP(mX(mZ,m1(mS(tauM(u),mONE))),m1(tauM(a))))
    return mS(*r)
L2=[t for t in L]
notT=[t for t in L2 if not minT(tauM(t))]
print('not in Mahlo T',len(notT),'of',len(L2),[show(t)[:50] for t in sorted(notT,key=lambda t:len(show(t)))[:3]])
bad=0;ex=None
for _ in range(40000):
    s,t=R.choice(L2),R.choice(L2)
    if (cmp(s,t)<0)!=mlt(tauM(s),tauM(t)): bad+=1;ex=(s,t)
print('order disagreements',bad,'of 40000',(show(ex[0])[:60],show(ex[1])[:60]) if ex else '')
same=diff=0;dx=[]
for t,n,r in steps:
    if cof(t)[0]!='w': continue
    a=tauM(r);b=mfs(tauM(t),mnat(n))
    if a==b: same+=1
    else:
        diff+=1;dx.append((t,n))
print('FS exact agreement',same,'disagree',diff)
for t,n in sorted(dx,key=lambda e:len(show(e[0])))[:4]:
    print('  ',show(t)[:70],n,'EBO->',NS['show'](tauM(fs(t,n)))[:70],'M->',NS['show'](mfs(tauM(t),mnat(n)))[:70])
