#!/usr/bin/env python3
# Compare EBO rules (extended Buchholz, as in EBO.lagda.md 5.1-5.3)
# with the community T_W rules (Googology Wiki list page, section on weakly
# inaccessibles), through the translation tau, on terms below psi_0(Lambda).
import sys
sys.setrecursionlimit(100000)

# EBO: term = tuple of (u, a) pairs, descending. () = 0.
Z = ()
def P(u, a): return ((u, a),)
ONE = P(Z, Z)
def add(s, t):
    # normal-form-aware sum: drop summands of s below t's head
    if not t: return s
    r = list(s)
    while r and cmp((r[-1],), (t[0],)) < 0: r.pop()
    return tuple(r) + t
def cmp(s, t):
    for x, y in zip(s, t):
        c = cmp(x[0], y[0]) or cmp(x[1], y[1])
        if c: return c
    return (len(s) > len(t)) - (len(s) < len(t))
def nat(n): return ONE * n
def succ(s): return add(s, ONE)
def is_succ(s): return s and s[-1] == (Z, Z)
def pred(s): return s[:-1]
def Om(u): return P(u, Z)

def cof(t):
    if not t: return ('0',)
    u, a = t[-1]
    if not a:
        if not u: return ('1',)
        if is_succ(u): return ('O', pred(u))     # Omega_{mu+1}
        return cof(u)
    if is_succ(a): return ('w',)
    c = cof(a)
    if c[0] == 'w': return c
    return ('O', c[1]) if cmp(succ(c[1]), u) <= 0 else ('w',)

def fs(t, z):
    """t[z]; z is a natural for cof=w, a term for cof=Omega."""
    if not t: return Z
    u, a = t[-1]
    head = t[:-1]
    if not a:
        if not u: return head
        if is_succ(u):
            return head + z_term(z)
        return head + Om(fs(u, z))
    if is_succ(a):
        return head + P(u, pred(a)) * z
    c = cof(a)
    if c[0] == 'w':
        return head + P(u, fs(a, z))
    if cmp(succ(c[1]), u) <= 0:
        return head + P(u, fs(a, z))
    mu = c[1]
    g = Om(mu)
    for _ in range(z):
        g = P(mu, fs(a, g))
    return head + P(u, fs(a, g))
def z_term(z): return nat(z) if isinstance(z, int) else z

# T_W: 0=(), sum of primitives ('p',pi,g) ('O',b) ('I',b)
def W_ONE(): return (('p', (('O', W_ONE_()),), ()),)
def W_ONE_(): return (('p', None, ()),)
W1 = (('p', None, ()),)  # psi_pi(0)=1, value independent of pi
def wadd(s, t): return s + t
def wnat(n): return W1 * n
def wsucc(s): return s + W1
def w_is_succ(s): return s and s[-1] == W1[0]
def wpred(s): return s[:-1]
def tau(t):
    r = ()
    for u, a in t:
        tu = tau(u)
        if not a:
            if not u: r += W1
            else: r += (('O', tu),)
        else:
            r += (('p', (('O', wsucc(tu)),), tau(a)),)
    return r
def wcmp(s, t):
    # order via key: reduce to EBO by inverse translation on the fragment
    return cmp(untau(s), untau(t))
def untau(s):
    r = ()
    for x in s:
        if x == W1[0]: r += ONE
        elif x[0] == 'O': r += P(untau(x[1]), Z)
        else:
            assert x[1][0][0] == 'O'
            r += P(pred(untau(x[1][0][1])), untau(x[2]))
    return r
def wcof(t):
    if not t: return ('0',)
    x = t[-1]
    if x == W1[0]: return ('1',)
    if x[0] == 'O':
        b = x[1]
        if w_is_succ(b): return ('O', wpred(b))
        return wcof(b)
    pi, g = x[1], x[2]
    if w_is_succ(g): return ('w',)
    c = wcof(g)
    if c[0] == 'w': return c
    rho = wsucc(c[1])
    if wcmp(rho, wpi_idx(pi)) < 0: return c
    return ('w',)
def wpi_idx(pi): return pi[0][1]
def wfs(t, z, g0_fixed=False):
    x = t[-1]; head = t[:-1]
    if x == W1[0]: return head
    if x[0] == 'O':
        b = x[1]
        if w_is_succ(b): return head + (wnat(z) if isinstance(z, int) else z)
        return head + (('O', wfs(b, z, g0_fixed)),)
    pi, g = x[1], x[2]
    if g == W1:
        nu = wpred(wpi_idx(pi))
        return head + (wnat(z) if not nu else (('O', nu),) * z)
    if w_is_succ(g):
        return head + (('p', pi, wpred(g)),) * z
    c = wcof(g)
    if c[0] == 'w':
        return head + (('p', pi, wfs(g, z, g0_fixed)),)
    rho_idx = wsucc(c[1])
    if wcmp(rho_idx, wpi_idx(pi)) < 0:
        return head + (('p', pi, wfs(g, z, g0_fixed)),)
    rho = (('O', rho_idx),)
    mu = c[1]
    gm = ((('O', mu),) if (g0_fixed and mu) else W1)
    for _ in range(z):
        gm = (('p', rho, wfs(g, gm, g0_fixed)),)
    return head + (('p', pi, wfs(g, gm, g0_fixed)),)

# Test set
O1 = Om(ONE); O2 = Om(nat(2)); O3 = Om(nat(3))
W = P(Z, ONE)            # omega
Ow = Om(W)
OO1 = Om(O1)
OOO = Om(OO1)
seeds = [P(Z, x) for x in [
    O1, add(O1, O1), P(ONE, ONE), P(ONE, O1), P(ONE, O2), P(ONE, add(O2, O2)),
    O2, O3, P(nat(2), O3), P(ONE, P(nat(2), O3)), Ow, P(W, Z), add(Ow, O1),
    OO1, OOO, Om(add(O1, O1)), Om(P(ONE, O1)), P(O1, Om(succ(O1))),
    Om(succ(O1)), P(ONE, Om(succ(O1))), add(OO1, O2), Om(Ow)]]

FIXB = False
FIXC = False
def nz(t):
    out = []
    for x in t:
        if x == ('O', ()): out.append(W1[0])
        elif x == W1[0]: out.append(x)
        elif x[0] == 'O': out.append(('O', nz(x[1])))
        else:
            if FIXC and not x[2]:
                idx = nz(x[1][0][1]); nu = idx[:-1]
                out.append(('O', nu) if nu else W1[0])
            else: out.append(('p', nz(x[1]), nz(x[2])))
    return tuple(out)
def run(g0_fixed):
    seen, agree, dis, ex = set(), 0, 0, []
    work = list(seeds)
    while work and len(seen) < 3000:
        t = work.pop()
        if t in seen or not t or len(repr(t)) > 700: continue
        seen.add(t)
        c = cof(t)
        if c[0] != 'w': continue
        for n in range(3):
            r = fs(t, n)
            if r:
                work.append(r)
            a = tau(r)
            b = wfs(tau(t), n, g0_fixed)
            if FIXB: b = nz(b)
            if a == b: agree += 1
            else:
                dis += 1
                if len(ex) < 4: ex.append((show(t), n, show(r), show(untau(b))))
    return len(seen), agree, dis, ex

def show(t):
    if not t: return '0'
    out = []
    for u, a in t:
        if not u and not a: out.append('1')
        elif not a: out.append('O[%s]' % show(u))
        else: out.append('p[%s](%s)' % (show(u), show(a)))
    return '+'.join(out)



for g, fb, fc in ((False,False,False),(True,False,False),(False,True,False),(False,False,True),(True,True,False),(True,True,True)):
    FIXB = fb or fc; FIXC = fc
    seen, ag, dis, ex = run(g)
    print('A gamma0=Omega_mu', g, '| B Omega_0=1', fb, '| C psi_pi(0)=Omega_nu', fc, '| terms', seen, 'agree', ag, 'disagree', dis)
