import sys,random; sys.path.insert(0,'.')
from ebo import *
N=int(sys.argv[1]); cap=int(sys.argv[2]); szcap=int(sys.argv[3])
def size(t):
    n=0;st=[t]
    while st:
        x=st.pop()
        if x is None: continue
        n+=1;st.extend(x)
    return n
tt=[t for s in range(N+1) for t in terms(s) if isOT(t) and cnt(t)]
lim_=[t for t in tt if cof(t)[0]=='cw']
def wkf(t):
    x=t;i=0
    while x is not None and i<cap:
        if size(x)>szcap: return None
        x=step(x,1);i+=1
    return i if x is None else None
W={t:wkf(t) for t in tt}
ok=[t for t in tt if W[t] is not None]
print('terms',len(tt),'wk known',len(ok),flush=True)
viol=[t for t in ok if size(t)>W[t]]
print('size>wk count',len(viol),'max(size-wk)',max(size(t)-W[t] for t in ok),'min wk/size ratio ex',flush=True)
for t in viol[:4]: print(' ',t,size(t),W[t])
print('max wk',max(W[t] for t in ok))
# lean bound: witness n<=size s+1; and first witness vs wk, vs size
random.seed(5); pairs=0;bad=0;maxgap=0;badwk=0
for _ in range(30000):
    s,t=random.choice(ok),random.choice(lim_)
    if cmpT(s,t)!='lt': continue
    M=size(s)+1
    c=fsn(t,M)
    if size(c)>szcap*8: continue
    pairs+=1
    if cmpT(s,c)=='gt': bad+=1
    w=W[s]
    if w+1<=M+40 and size(fsn(t,w+1))<szcap*8 and cmpT(s,fsn(t,w+1))=='gt': badwk+=1
print('pairs',pairs,'size-bound bad',bad,'wk-bound bad',badwk,flush=True)
# deterministic path: N=size s+1 walk t->t[N] passes s
hit=miss=over=0
for _ in range(4000):
    s,t=random.choice(ok),random.choice(lim_)
    if cmpT(s,t)!='lt': continue
    M=size(s)+1; x=t;i=0;r=None
    while True:
        if x==s: r='h';break
        if x is None: r='m';break
        if i>=2000 or size(x)>szcap*2: r='o';break
        x=step(x,M);i+=1
    if r=='h':hit+=1
    elif r=='m':
        miss+=1
        if miss<4: print(' MISS',s,t)
    else: over+=1
print('detpath hit',hit,'miss',miss,'over',over,flush=True)
