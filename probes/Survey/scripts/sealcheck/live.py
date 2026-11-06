import re, os, sys
sys.path.insert(0,'')
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
A=os.listdir(R+'/probes/OCF/Align')
live_pref=sys.argv[1].split(',')
live=[ 'OCF.Align.'+x[:-10] for x in A if x.endswith('.lagda.md') and any(re.match(p+r'([A-Z0-9].*)?\.lagda\.md$',x) for p in live_pref)]
s=set()
for m in live: clo(m,s)
fam={'§1':r'(LadderNF|LadderInf|LadderOrd|LadderMono|LadderLab|CrossM|CrossNext|TLOne|TLCode|EmbVV|OrdLab|ValLab)',
 '§2':r'(GuardTight|GuardRead|GuardWeak|GuardCert|GuardBridge|WeakBridge)',
 '§3':r'(CumRead|CumUp|CumVal|CumHt|Om1Cum|WorldTH|BTBOVal|BTBOFull)',
 '§4':r'(NoCum(?!sum)|NoCumHn|Om1Hn|NoCumNode|TLOps|TLPrefix|CtxMono)',
 '§5':r'(LevelFix|LevelNoK|NoKCert)',
 '§6':r'(TreeJudge|ValueJudge|TLEnd|TLBehave|AddClo|AddTwo)',
 '§8':r'(SumHt|SumClimb|SumVar)'}
print('live modules',len(live),'closure',len(s))
for k,v in fam.items():
    hit=sorted(x[10:] for x in s if x.startswith('OCF.Align.') and re.match(v,x[10:]))
    print(k,len(hit),hit)
