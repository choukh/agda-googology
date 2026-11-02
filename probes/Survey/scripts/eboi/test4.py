# large closure with G-based NF; order vs Setzer transcription; order axioms on closure sample
from eboi import *
from closure import closure
import random
seen,steps=closure(int(sys.argv[1]),int(sys.argv[2]))
print('terms',len(seen),'steps',len(steps))
print('NF exits',sum(1 for t,r in steps if not isNF(r)),'OT exits',sum(1 for t,r in steps if not isOT(tau(r))),'not decreasing',sum(1 for t,r in steps if cmpT(r,t)>=0))
mono=0;n=0
for t in seen:
    if cof(t)[0]=='w':
        rs=[fsn(t,i) for i in range(5)];n+=1
        mono+=sum(1 for i in range(4) if cmpT(rs[i],rs[i+1])>=0)
print('w terms',n,'monotone failures',mono)
L=sorted(seen,key=repr);R=random.Random(3);bad=0
for _ in range(300000):
    s,t=R.choice(L),R.choice(L)
    a=cmpT(s,t)
    if (a<0)!=ltT(tau(s),tau(t)) or (a>0)!=ltT(tau(t),tau(s)): bad+=1
print('order disagree of 300000',bad)
tr=0;an=0
for _ in range(300000):
    a,b,c=R.choice(L),R.choice(L),R.choice(L)
    x,y,z=sorted([a,b,c],key=repr)
    for p,q,r in ((a,b,c),(b,c,a),(c,a,b),(a,c,b)):
        if cmpT(p,q)<0 and cmpT(q,r)<0 and not cmpT(p,r)<0: tr+=1
    if cmpT(a,b)!=-cmpT(b,a): an+=1
print('transitivity failures',tr,'antisym failures',an)
