from eboi import *
from test2data import base
def closure(limit,maxlen=900):
    O1=Om(ONE)
    ETAS=[Z,ONE,nat(2),P(Z,ONE),O1,LAM,L(ONE),I,P(I,I),Om(I+ONE),P(ONE,ONE),P(Z,O1),P(Z,I)]
    seen=set();work=[s for s in base if s and isNF(s)];steps=[]
    while work and len(seen)<limit:
        t=work.pop(0)
        if t in seen or not t or len(repr(t))>maxlen: continue
        seen.add(t);c=cof(t)
        if c[0] in 'w1': rs=[fsn(t,n) for n in ([0,1,2] if c[0]=='w' else [0])]
        else:
            rg=reg(c); rs=[fsT(t,e) for e in ETAS if cmpT(e,rg)<0 and isNF(e)]
        for r in rs:
            steps.append((t,r))
            if r and isNF(r): work.append(r)
    return seen,steps
