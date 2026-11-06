# -*- coding: utf-8 -*-
# 四层表 (切片口径, 2026-11-04). 用法: agda --html --html-highlight=all --html-dir=<H> 编译 BTBOFull, Label, NoCumsum,
# HtFeedGrow, HtFeedClosed, WfTauNF, WfFsn (后两者要归档副本 -i <ARCH>), 再 python3 locslice_four.py <H> <ARCH>.
import os,sys,io,collections
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
ARCH=sys.argv[2]
_src=src
def src(mod):
    p=_src(mod)
    if p: return p
    for ext in ('.lagda.md','.agda'):
        q=os.path.join(ARCH,*mod.split('.'))+ext
        if os.path.exists(q): return q
    return None
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def all_(P): return sum(lines(n) for n in P)
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def arch(P): return sum(lines(n) for n in P if n[0].startswith('Mahlo.'))
def bymod(P,top=10):
    c=collections.Counter()
    for n in P: c[n[0].replace('OCF.Align.','').replace('OCF.','')]+=lines(n)
    return ', '.join('%s %d'%kv for kv in c.most_common(top))
def show(name,layers):
    acc=set(); print('==',name)
    for i,(lab,roots) in enumerate(layers,1):
        if roots is None: print('  层%d %s: 同上一层'%(i,lab)); continue
        acc=acc|C(roots)
        print('  层%d %s: 全部 %d | 树侧 %d | 记号模块 %d | 归档 %d'%(i,lab,all_(acc),tree(acc),note(acc),arch(acc)))
        print('      ',bymod(acc))
E='OCF.Align.EBO'
show('记号 EBO',[('定义',[(E,'T'),(E,'PT'),(E,'_<ᵀ_'),(E,'cmpᵀ'),(E,'fsn'),(E,'pred'),(E,'EBOψ')]),
                 ('+FGH',[(E,'Acc'),(E,'FGH')]),
                 ('+可数标准形良基',[(A+'WfTauNF','wfNF'),('Mahlo.Inacc.FactsImpl','facts')]),
                 ('(层3续) +基本列封闭, 带标签的树与 FGH',[(A+'WfFsn','fgh-EBO'),(A+'WfFsn','lab-NF'),(A+'WfFsn','ebo-lab'),(A+'WfFsnClosure','cl-fsn'),('Mahlo.Inacc.FactsImpl','facts')])])
show('src BTBO (累加)',[('定义',[('OCF.BTBO','Ord'),('OCF.BTBO','Ord₀'),('OCF.BTBO','Ordᴰ')]),
                 ('+折叠 FGH',[('OCF.BTBO','BTBO'),('OCF.BTBO','FGH')]),
                 ('+合法性',None),
                 ('+强度',[(A+'BTBOFull','BTBO≈'),(A+'Label','BTBO-label')])])
show('BTBOᴵ (不累加, Level)',[('定义',[('OCF.Align.Level','Ordᴵ'),('OCF.Align.Level','_<ᴵ_'),('OCF.Align.Level','Ordᶜ'),('OCF.Align.Level','_◃_'),('OCF.Align.Level','HS')]),
                 ('+折叠 FGH',[(A+'NoCumsum','BTBOᴵ'),('OCF.Align.Level','FGH')]),
                 ('+合法性',[(A+'NoCumsum','BTBO-HS')]),
                 ('+强度',[(A+'Label','BTBO-label')])])
show('HtFeed',[('定义',[(A+'HtFeedTree','D₊'),(A+'HtFeedTree','D'),(A+'HtFeedTree','H'),(A+'CumReadCF','A'),(A+'CumReadCF','Lg')]),
                 ('+折叠 FGH',[(A+'HtFeedClosed','fgh'),(A+'HtFeedClosed','TΛ'),(A+'HtFeedClosed','T-Ω'),(A+'HtFeedClosed','T-Ωk')]),
                 ('+合法性',[(A+'HtFeedClosed','Lg-TΛ')]),
                 ('+严格增长(不是层4)',[(A+'HtFeedGrow',n) for n in ['Sup-Ω','Sup-Ω·2','Sup-ΩΩk','feed']])])
