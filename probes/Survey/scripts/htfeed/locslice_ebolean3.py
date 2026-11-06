# -*- coding: utf-8 -*-
# EboLean3 (EBO-tree″, 直接突出集路线) 的四层切片, 2026-11-05. 口径同 locslice_ebolean.py / locslice_four.py
# (定义级切片, 按到达的块计 agda 非空非注释行; 导入行不数).
# 用法: agda --html --html-highlight=all --html-dir=<H> -i src -i probes probes/OCF/Align/EboLean3Lab.lagda.md,
#       再 python3 locslice_ebolean3.py <H>.
# 切片盲区的处理: 带参数的模块别名 `module S = AgL agS` 的参数只出现在别名那一行, 而 `S.A⊆W` 的链接指向 AgL 的原定义,
# 所以别名行不会被到达 (agS 因此会漏数). 把 EboLean3* 里一切别名块 (`module X = ...`) 列为根; 同时打印每个别名块,
# 供核对. 模块应用 `open L417 Y Y.h l (Y.E yΩ)` 写在 where 里, 属于被到达的块, 参数可见; 本路线没有记录字段间接 (OTFacts 那类).
import os,sys,io,collections
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'; E=A+'EBO'; D=A+'EboLeanDef'
MINE=[A+'EboLean3'+x for x in ['Base','Close','Dist','Omega','Tree','Lab']]
aliases=[]
for m in MINE:
    f=chunk(m)
    for i,c in enumerate(f.chunks):
        if c['name'].startswith('module ') and any(' = ' in l for l in c['text'][:1]):
            aliases.append((m,c['name'])); print('ALIAS-ROOT',m.replace(A,''),c['name'],'|',c['text'][0].strip())
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
layers=[('1 定义',[(E,'T'),(E,'PT'),(E,'_<ᵀ_'),(E,'cmpᵀ'),(D,'fsn'),(E,'pred'),(E,'EBOψ')]),
 ('2 +FGH',[(D,'HC'),(D,'fgh')]),
 ('3a +标准形良基',[(A+'EboLean3Omega','wf')]+[a for a in aliases if a[0]!=A+'EboLean3Lab']),
 ('3b +基本列封闭, 树与 fgh-EBO″',[(A+'EboLeanClosure','cl-fsn-NF'),(A+'EboLean3Tree','hc'),(A+'EboLean3Tree','EBO-tree″'),(A+'EboLean3Tree','fgh-EBO″')]),
 ('+标签',[(A+'EboLean3Lab','lab-NF″'),(A+'EboLean3Lab','ebo-lab″')])]
acc=set(); prev=collections.Counter()
for lab,r in layers:
    acc|=C(r); c=collections.Counter()
    for n in acc: c[n[0]]+=lines(n)
    print('%-28s %5d  (+%d)'%(lab,sum(c.values()),sum(c.values())-sum(prev.values())))
    print('    ',', '.join('%s %d'%(k.replace('OCF.Align.',''),v) for k,v in c.most_common(80)))
    prev=c
bad=[n for n in acc if 'EboLean.OT' in n[0] or n[0] in (A+'EboLeanTau',A+'EboLeanTree',A+'EboLeanLab')]
print('reached Setzer OT_I / τ-route chunks:',len(bad))
G=collections.OrderedDict([('EBO 定义 (EBO, EboLeanDef)',lambda m:m in (E,D)),
 ('序, 标准形, G (EboLeanBase)',lambda m:m==A+'EboLeanBase'),
 ('突出集的定义 (EboLean2 §1)',lambda m:m==A+'EboLean2'),
 ('良基: 层号与 C/𝒲 引理 (EboLean3Base)',lambda m:m==A+'EboLean3Base'),
 ('良基: 4.17 (b)(c) (EboLean3Close)',lambda m:m==A+'EboLean3Close'),
 ('良基: 突出集通用层 (EboLean3Dist)',lambda m:m==A+'EboLean3Dist'),
 ('良基: 4.23c, 4.30, 4.31a, 组装 (EboLean3Omega)',lambda m:m==A+'EboLean3Omega'),
 ('封闭性 (View, Trian, Omega, Bach, Closure)',lambda m:m in [A+'EboLean'+x for x in ['View','Trian','Omega','Bach','Closure']]),
 ('树与 fgh (EboLean3Tree)',lambda m:m==A+'EboLean3Tree'),
 ('标签 (EboLean3Lab)',lambda m:m==A+'EboLean3Lab')])
c=collections.Counter()
for n in acc: c[n[0]]+=lines(n)
tot=0
for g,f in G.items():
    v=sum(v for k,v in c.items() if f(k)); tot+=v; print('%-50s %5d'%(g,v))
print('%-50s %5d'%('(合计)',tot))
# 核对: 本路线各文件的物理代码行 (agda 块非空非注释, 含导入) 与切片行
for m in MINE:
    f=chunk(m); phys=sum(1 for i in range(len(f.chunks)) for l in f.chunks[i]['text'] if l.strip() and not l.strip().startswith('--'))
    print('%-22s slice %4d / chunks-total %4d'%(m.replace(A,''),c[m],phys))
if len(sys.argv)>2:
    for m in MINE:
        f=chunk(m)
        for i,ch in enumerate(f.chunks):
            if (m,i) not in acc:
                k=sum(1 for l in ch['text'] if l.strip() and not l.strip().startswith('--'))
                if k: print('UNREACHED',m.replace(A,''),ch['name'],k)
