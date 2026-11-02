import sys,time,signal; sys.path.insert(0,'.')
from ebo import *
def P(u,a): return (u,a,None)
Z=None
one=P(Z,Z)
def O(u): return P(u,Z)
def psi0(a): return P(Z,a)
w=psi0(one); O1=O(one); O2=O(natT(2)); O3=O(natT(3))
def show(t):
    if t is None: return '0'
    L=lst(t); o=[]
    for (u,a) in L:
        if u is None and a is None: o.append('1')
        elif u is None: o.append('p('+show(a)+')')
        elif a is None: o.append('O['+show(u)+']')
        else: o.append('p['+show(u)+']('+show(a)+')')
    return '+'.join(o)
def size(t): return 0 if t is None else 1+size(t[0])+size(t[1])+size(t[2])
def trace(t,n,steps,K=1):
    a,b=fsn(t,n),fsn(t,n+1)
    print('t=',show(t),'n',n,'a=',show(a),'b=',show(b))
    x=b;i=0
    while x is not None and i<steps:
        x=step(x,K);i+=1
        if i<=14: print('  ',i,show(x)[:120],size(x) if x else 0)
        if x==a: print(' HIT at',i); return
    print(' none within',i, 'end' if x is None else 'size %d'%size(x))
trace(psi0(O(w)),0,200)
trace(psi0(O(w)),1,200)
trace(psi0(O2),0,200)
trace(psi0(O(w)),2,3000)
