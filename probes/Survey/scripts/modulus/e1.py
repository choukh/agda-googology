from ebo import *
import random
N=int(sys.argv[1]) if len(sys.argv)>1 else 6
K=int(sys.argv[2]) if len(sys.argv)>2 else 1
all_=[t for s in range(N+1) for t in terms(s) if isOT(t) and cnt(t)]
print('NF countable',len(all_))
bad=[];over=0;chk=0
for t in all_:
    if cof(t)[0]!='cw': continue
    for n in range(0,4):
        a,b=fsn(t,n),fsn(t,n+1)
        W=walk(b,K)
        if W is None: over+=1; continue
        chk+=1
        if a not in W[1:]: bad.append((t,n)) 
print('checked',chk,'over',over,'bad',len(bad))
for (t,n) in bad[:8]:
    print(t,n,fsn(t,n),fsn(t,n+1))
print('NF closure bad', sum(1 for t in all_ if cof(t)[0]=='cw' and not all(isOT(fsn(t,n)) for n in range(4))))
