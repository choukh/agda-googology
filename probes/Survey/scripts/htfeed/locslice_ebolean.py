# -*- coding: utf-8 -*-
# EboLean (精简版 EBO-tree′) 的四层切片, 2026-11-05. 口径同 locslice_four.py (定义级切片, 按到达的块计 agda 非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> -i src -i probes probes/OCF/Align/EboLeanLab.lagda.md, 再 python3 locslice_ebolean.py <H>.
# 补了切片的两处盲区: (1) 模块应用 `import M facts` 看不见 facts 的实现, 所以把 FactsImpl.facts 列为根;
# (2) 带参数的模块别名 `module At ... = L417b h … (Ex̃ ax)` 的参数看不见, 所以把 Ex̃, E⁺ 列为根 (删死代码后编译报缺, 由此发现).
import os,sys,io,collections
import os; here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'; E=A+'EBO'; D=A+'EboLeanDef'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
layers=[('1 定义',[(E,'T'),(E,'PT'),(E,'_<ᵀ_'),(E,'cmpᵀ'),(D,'fsn'),(E,'pred'),(E,'EBOψ')]),
 ('2 +FGH',[(D,'HC'),(D,'fgh')]),
 ('3a +可数标准形良基',[(A+'EboLeanTau','wfNF′'),(A+'EboLean.OT.FactsImpl','facts'),(A+'EboLean.OT.WO.Lemma423','Ex̃'),(A+'EboLean.OT.WO.Lemma423c','E⁺')]),
 ('3b +基本列封闭, 树与 fgh-EBO′',[(A+'EboLeanClosure','cl-fsn-NF'),(A+'EboLeanTree','hc'),(A+'EboLeanTree','EBO-tree′'),(A+'EboLeanTree','fgh-EBO′')]),
 ('+标签',[(A+'EboLeanLab','lab-NF′'),(A+'EboLeanLab','ebo-lab′')])]
acc=set(); prev=collections.Counter()
for lab,r in layers:
    acc|=C(r); c=collections.Counter()
    for n in acc: c[n[0]]+=lines(n)
    print('%-28s %5d  (+%d)'%(lab,sum(c.values()),sum(c.values())-sum(prev.values())))
    print('    ',', '.join('%s %d'%(k.replace('OCF.Align.',''),v) for k,v in c.most_common(80)))
    prev=c
if len(sys.argv)>2:
    # 列出到达的 OTFacts 字段名
    import re
    used=set()
    for n in acc:
        if n[0].startswith(A+'EboLean.OT.WO') or n[0].startswith(A+'EboLeanTau'):
            used|=set(re.findall(r'[^\s(){};.@"]+','\n'.join(chunk(n[0]).chunks[n[1]]['text'])))
    print('USED-TOKENS',len(used))
    io.open(sys.argv[2],'w',encoding='utf-8').write('\n'.join(sorted(used)))

# 分组
G=collections.OrderedDict([('EBO 定义 (EBO, EboLeanDef)',lambda m:m in (E,D)),
 ('Setzer 句法与序 (OT/*.lagda.md 非 Facts)',lambda m:m.startswith(A+'EboLean.OT.') and '.WO.' not in m and 'Facts' not in m),
 ('Setzer 58→44 条句法事实 (Facts1/2/2b/3, FactsImpl, WO.Facts)',lambda m:m.startswith(A+'EboLean.OT.') and 'Facts' in m),
 ('Setzer 突出集 (OT/WO 其余)',lambda m:m.startswith(A+'EboLean.OT.WO.') and 'Facts' not in m),
 ('τ 与拉回 (EboLeanTau)',lambda m:m==A+'EboLeanTau'),
 ('封闭性 (Base, View, Trian, Omega, Bach, Closure)',lambda m:m in [A+'EboLean'+x for x in ['Base','View','Trian','Omega','Bach','Closure']]),
 ('树与 fgh (EboLeanTree)',lambda m:m==A+'EboLeanTree'),
 ('标签 (EboLeanLab)',lambda m:m==A+'EboLeanLab')])
c=collections.Counter()
for n in acc: c[n[0]]+=lines(n)
for g,f in G.items(): print('%-60s %5d'%(g,sum(v for k,v in c.items() if f(k))))
