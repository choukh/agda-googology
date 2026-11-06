import re, os, sys
import os; R=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','..'))
roots=[(R+'/probes','/probes/_build/2.8.0.2/agda'),(R+'/src','/src/_build/2.8.0.2/agda')]
imp=re.compile(r'^\s*(?:open\s+)?import\s+([A-Za-z0-9_.\u0080-￿\']+)',re.M)
def find(m):
    p=m.replace('.','/')
    for r,b in roots:
        for ext in ('.lagda.md','.agda'):
            f=r+'/'+p+ext
            if os.path.exists(f): return f, R+b+'/'+p+'.agdai'
    return None,None
memo={}
def clo(m,seen):
    if m in seen: return
    f,a=find(m)
    if f is None: return
    seen[m]=(f,a)
    for d in imp.findall(open(f,encoding='utf8').read()):
        clo(d,seen)
for m in sys.argv[1:]:
    s={}; clo(m,s)
    stale=[]; missing=[]
    for k,(f,a) in s.items():
        if not os.path.exists(a): missing.append(k)
        elif os.path.getmtime(f)>os.path.getmtime(a): stale.append(k)
    big=[k for k in s if re.search(r'OCF\.Align\.(LadderOrd|CrossM|CrossNext|WorldTH|WeakBridgeOp)',k)]
    fams=sorted(set(re.sub(r'(LadderOrd|CrossM|CrossNext|WorldTH|WeakBridgeOp).*',r'\1',b) for b in big))
    print(f"{m}: closure={len(s)} missing={len(missing)} {missing[:6]} stale={len(stale)} {stale[:6]} bigdeps={len(big)} {fams}")
