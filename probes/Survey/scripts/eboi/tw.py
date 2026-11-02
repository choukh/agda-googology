# Compare EBOI with T_W rules (wiki rules 1-11, I_1 only) + corrections A,B,C; tau: psi_u(0)->Omega, psi_u(a)->psi_{Omega_{u+1}}(a), psiI a -> psi_I(1+a)
from eboi import *
from closure import closure
import collections
W1=('one',)
def tw(t):
    r=()
    for x in t:
        if x==ONEP: r+=(W1,)
        elif x==IP: r+=(('I',),)
        elif x[0]=='L': r+=(('pI',oneplus(tw(x[1]))),)
        elif not x[2]: r+=wOm(tw(x[1]))
        else: r+=(('p',tw(x[1]),tw(x[2])),)   # subscript stored as nu with pi=Omega_{nu+1}
    return r
def oneplus(g):
    return (W1,)+g if (not g or g[0]==W1) else g
def minus1(g):
    return g[1:] if g and g[0]==W1 else g
def un(g):
    r=()
    for x in g:
        if x==W1: r+=ONE
        elif x[0]=='I': r+=I
        elif x[0]=='pI':
            r+=L(un(minus1(x[1])))
        elif x[0]=='O': r+=Om(un(x[1])) 
        else: r+=P(un(x[1]),un(x[2]))
    return r
def wsucc(g): return g and g[-1]==W1
def wOm(b):
    if not b: return (W1,)
    if len(b)==1 and b[0][0] in('I','pI'): return b
    return (('O',b),)
def wcof(g):
    if not g: return ('0',)
    x=g[-1]
    if x==W1: return ('1',)
    if x[0]=='I': return ('RI',)
    if x[0]=='O':
        b=x[1]
        if wsucc(b): return ('O',b[:-1])
        return wcof(b)
    if x[0]=='p':
        c=wcof(x[2])
        if c[0] in '1w': return ('w',)
        ix=(un(c[1])+ONE) if c[0]=='O' else I
        return c if cmpT(ix,un(x[1]))<=0 else ('w',)
    c=wcof(x[1])
    if c[0] in '1w': return ('w',)
    ix=(un(c[1])+ONE) if c[0]=='O' else I
    return c if cmpT(ix,I)<0 else ('w',)
def wn(k): return (W1,)*k
def wfs(g,z,gam0I):
    x=g[-1];h=g[:-1]
    zz=wn(z) if isinstance(z,int) else z
    if x==W1: return h
    if x[0]=='I': return h+zz
    if x[0]=='O':
        b=x[1]
        if wsucc(b): return h+zz
        return h+wOm(wfs(b,z,gam0I))
    if x[0]=='p':
        nu,a=x[1],x[2]
        def mk(q): return (('p',nu,q),) if q else wOm(nu)
        if wsucc(a): return h+mk(a[:-1])*z
        c=wcof(a)
        if c[0]=='w': return h+mk(wfs(a,z,gam0I))
        ix=(un(c[1])+ONE) if c[0]=='O' else I
        if cmpT(ix,un(nu))<=0: return h+mk(wfs(a,z,gam0I))
        return h+mk(wfs(a,chain(a,c,z,gam0I),gam0I))
    a=x[1]
    def mi(q): return (('pI',q),) if q else (W1,)
    if a==(W1,):
        t=(W1,)
        for _ in range(z): t=wOm(t)
        return h+t
    if wsucc(a):
        t=mi(a[:-1])+(W1,)
        for _ in range(z): t=wOm(t)
        return h+t
    c=wcof(a)
    if c[0]=='w': return h+mi(wfs(a,z,gam0I))
    ix=(un(c[1])+ONE) if c[0]=='O' else I
    if cmpT(ix,I)<0: return h+mi(wfs(a,z,gam0I))
    return h+mi(wfs(a,chain(a,c,z,gam0I),gam0I))
def chain(a,c,z,gam0I):
    if c[0]=='O':
        mu=c[1]; g=wOm(mu) if mu else (W1,)
        for _ in range(z):
            q=wfs(a,g,gam0I); g=(('p',mu,q),) if q else wOm(mu)
    else:
        g=gam0I
        for _ in range(z):
            q=wfs(a,g,gam0I); g=(('pI',q),) if q else (W1,)
    return g
seen,steps=closure(int(sys.argv[1]),900)
LAMW=(('pI',(W1,)),)
for name,g0 in (('gamma0(I)=1 (T_W literal)',(W1,)),('gamma0(I)=Lambda',LAMW)):
    ag=dis=0;ex=[];kinds=collections.Counter()
    for t in seen:
        if cof(t)[0]!='w': continue
        for n in (0,1,2):
            a=tw(fsn(t,n));b=wfs(tw(t),n,g0)
            if a==b: ag+=1
            else:
                dis+=1;ex.append((t,n,un(a),un(b)))
    print(name,'agree',ag,'disagree',dis)
    for t,n,a,b in sorted(ex,key=lambda e:len(show(e[0])))[:9]: print('   ',show(t)[:50],n,'mine',show(a)[:50],'TW',show(b)[:50])
    print('   mismatches on terms containing no psi_I/I:',sum(1 for e in ex if 'L' not in repr(e[0]) and "'I'" not in repr(e[0])))
    print('   mismatch at n:',collections.Counter(e[1] for e in ex))
    print('   fine: order agree?',sum(1 for t,n,a,b in ex if cmpT(a,b)>0),'mine>TW',sum(1 for t,n,a,b in ex if cmpT(a,b)<0),'mine<TW')
ebo=[t for t in seen if 'L' not in repr(t) and "'I'" not in repr(t)]
print('EBO-only terms in sample',len(ebo))
