import sys; sys.path.insert(0,'.')
from ebo import *
N=int(sys.argv[1]); K=int(sys.argv[2]); cap=int(sys.argv[3])
all_=[t for s in range(N+1) for t in terms(s) if isOT(t) and cnt(t)]
print("NF countable",len(all_),flush=True)
bad=[];over=0;chk=0
for t in all_:
    if cof(t)[0]!='cw': continue
    for n in range(0,3):
        a,b=fsn(t,n),fsn(t,n+1)
        x=b;i=0;hit=False
        while x is not None and i<cap:
            x=step(x,K);i+=1
            if x==a: hit=True;break
        if a is None and x is None: hit=True
        if hit: chk+=1
        elif x is None: bad.append((t,n))
        else: over+=1
print('hit',chk,'over',over,'bad',len(bad))
for (t,n) in bad[:6]: print(t,n,'|',fsn(t,n),'|',fsn(t,n+1))
