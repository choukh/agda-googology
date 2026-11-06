import re, os, sys
import os; R=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','..'))
imp=re.compile(r'^\s*(?:open\s+)?import\s+([^\s;()]+)',re.M)
def find(m):
    p=m.replace('.','/')
    for r in (R+'/probes',R+'/src'):
        for ext in ('.lagda.md','.agda'):
            f=r+'/'+p+ext
            if os.path.exists(f): return f
def clo(m,seen):
    if m in seen: return
    f=find(m)
    if f is None: return
    seen.add(m)
    for d in imp.findall(open(f,encoding='utf8').read()): clo(d,seen)
passed=[l.split('\t')[0] for l in open(sys.argv[1]) if l.split('\t')[1]=='0']
cov=set()
for e in passed: clo('OCF.Align.'+e,cov)
print('covered modules',len(cov))
for d in sys.argv[2:]:
    s=set(); clo('OCF.Align.'+d,s)
    un=sorted(x[10:] for x in s-cov)
    print(f"{d}: closure {len(s)}, loaded-by-others {len(s&cov)}, not-loaded {len(un)}: {' '.join(un)}")
