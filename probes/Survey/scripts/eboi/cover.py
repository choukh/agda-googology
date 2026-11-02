from eboi import *
from closure import closure
import collections
seen,steps=closure(20000,1500)
c=collections.Counter()
def visit(t):
    if not t: return
    for x in t:
        if x==IP or x==ONEP: continue
        if x[0]=='L':
            a=x[1]; k=cof(a) if a else None
            if not a: c['Λ']+=1
            elif k[0] in '1': c['ψI succ']+=1
            elif k[0]=='w': c['ψI cof ω']+=1
            elif k[0]=='RI': c['ψI ρ=I collapse']+=1
            else: c['ψI ρ<I penetrate' if cmpT(suc(k[1]),I)<0 else 'ψI ρ>I collapse']+=1
            visit(a)
        else:
            u,a=x[1],x[2]
            if a:
                k=cof(a)
                if k[0]=='1': c['ψu succ']+=1
                elif k[0]=='w': c['ψu cof ω']+=1
                elif k[0]=='RI': c['ψu ρ=I '+('penetrate' if cmpT(I,u)<=0 else 'collapse')]+=1
                else: c['ψu ρ=Ω '+('penetrate' if cmpT(suc(k[1]),u)<=0 else 'collapse')]+=1
            else:
                k=cof(u)
                c['Ω leaf '+k[0]]+=1
            visit(u);visit(a)
for t in seen: visit(t)
for k,v in sorted(c.items()): print(k,v)
