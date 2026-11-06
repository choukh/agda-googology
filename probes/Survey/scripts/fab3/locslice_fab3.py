# -*- coding: utf-8 -*-
# Fab3Typed 一路的分层行数 (同 fab2/locslice_fab2.py, strattw/locslice_strattw.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Align.Fab3Typed, 再 python3 locslice_fab3.py <H> [-v].
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前).
# 参数化模块 (Fold, Fold.Thm, Step*) 的模块内定义手工列为根. 手工根可能有遗漏, 是近似.
import os,sys,io,collections
here=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..')
s=io.open(os.path.join(here,'locslice.py'),encoding='utf-8').read().split("\nB4=")[0]
__file__=os.path.join(here,'locslice.py')
exec(s)
A='OCF.Align.'
def C(ms):
    for m,n in ms:
        if not find(m,n): print('MISSING',m,n)
    return closure(ms)
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'Fab3'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [(A+m,n) for n in ns.split()]
L1=(M('Fab3Typed','LS Lg* ls⊥ LgW⁺* LgE⁺* lgBd⁺* step* T ℓT Ω W')+
    M('LFReTy','S⊥')+
    M('HtTowerTy','KS HB _⊲[_]_ step up _⊞_'))
L2=(M('Fab3Typed','L mul chain Ψ fold TΩ Σ⊥ TΩω ord⊥ fghΩ fghΩω'))
L3=(M('Fab3Typed','lg*⊲ Lg*-⊞ Lg*-up ℓ⁺ mul-fst Lg*-mul Ψ-mono Ψ-lg Lg*-Ω lW Lg*-fold Lg-TΩ Lg-Σ⊥ Lg-TΩω lgB⊥ LgB-TΩ LgB-TΩω')+
    M('HtTowerTy','⊲ᴮ-tr ⊞-fst ⊞-⊲ up-⊲'))
L4=(M('Fab3Typed','feed-id feed-suc feed-Ω LgB-Ω'))
acc=set(); print('== 无条件闭项 TΩ n, TΩω (后继层的塔 T n = stepⁿ S⊥, 带类型的一层折叠 Fold.Ψ)')
labs=['定义','折叠 (带类型, 回灌恒等, 闭项, FGH)','证书','形状']
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots)
    print('  层%d %s: 本路新增 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),tree(acc),note(acc)))
    if i==3: P3=set(acc)
    if '-v' in sys.argv:
        c=collections.Counter()
        for n in acc: c[n[0].replace(A,'')]+=lines(n)
        print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
print('== 前 3 层闭包里的 GenFold*, KindLv*, StratTw*, NewTwr* 块:', sorted((n[0].replace(A,''),n[1]) for n in P3 if any(n[0].startswith(A+p) for p in ('GenFold','KindLv','StratTw','NewTwr'))) or '无')
