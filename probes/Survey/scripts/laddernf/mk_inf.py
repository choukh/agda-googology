# 由 LadderNF* 生成对高度结构参数化的 LadderInf*: 换导入, 换高度的类型, 再加逐模块的补丁. 补丁是手写的数学内容, 其余行逐字.
import re,os,sys
R=os.environ.get('REPO') or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','..'))
A=R+'/probes/OCF/Align/'
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from inf_patches import PATCHES
MODS='Rel Cx Rules Rules2 Rules3 Strict Strict2 Strict3 Class ClassF Good Vis Read Iota Tr Add Psi PsiH Eval Tail Mono Root Omega'.split()
HDR={}
def dedupe(t):
    # 带参数的模块每 open import 一次就是一个新的实例, 名字会歧义: 同一模块只留一行
    pat=re.compile(r'^open import (OCF\.Align\.LadderInf\w+) 𝕊( using \(([^)]*)\))?[ \t]*$',re.M)
    info={}
    for m in pat.finditer(t):
        d=info.setdefault(m.group(1),{'full':False,'names':[]})
        if m.group(2) is None: d['full']=True
        else: d['names']+= [x.strip() for x in m.group(3).split(';') if x.strip()]
    seen=set()
    def rep(m):
        X=m.group(1)
        if X in seen: return '-- (同上)'
        seen.add(X)
        d=info[X]
        if d['full']: return f'open import {X} 𝕊'
        ns=list(dict.fromkeys(d['names']))
        return f'open import {X} 𝕊 using ('+'; '.join(ns)+')'
    return pat.sub(rep,t)
def clone(M):
    t=open(A+'LadderNF'+M+'.lagda.md',encoding='utf-8').read()
    title=t.split('\n',1)[0]
    t=t.split('\n',1)[1]
    t=re.sub(r'^\n?> 结论写在 \[LadderNF\]\(LadderNF\.lagda\.md\)\.','\n> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderInf](LadderInf.lagda.md). 对高度结构 `HtS` 参数化, 由 `Survey/scripts/laddernf/mk_inf.py` 从 [LadderNF'+M+'](LadderNF'+M+'.lagda.md) 生成, 下面的说明是原文件的.',t,count=1)
    title=re.sub(r'^# 阶梯去记号[^:]*:','# 高度抽象:',title)
    t=title+'\n'+t
    t=t.replace('module OCF.Align.LadderNF'+M+' where','open import OCF.Align.LadderInfBase\nmodule OCF.Align.LadderInf'+M+' (𝕊 : HtS) where')
    t=re.sub(r'open import OCF\.Align\.LadderNF(\w+)',lambda m:'open import OCF.Align.LadderInf'+m.group(1)+' 𝕊',t)
    t=t.replace('Eh zero','Eh h₀')
    for a,b in PATCHES.get(M,[]):
        if callable(a):
            t=a(t)
        elif a not in t:
            print('PATCH MISS',M,repr(a[:90]))
        else:
            t=t.replace(a,b)
    t=dedupe(t)
    open(A+'LadderInf'+M+'.lagda.md','w',encoding='utf-8').write(t)
for M in (sys.argv[1:] or MODS):
    clone(M)
