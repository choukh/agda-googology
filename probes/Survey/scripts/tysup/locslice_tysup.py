# -*- coding: utf-8 -*-
# TySup 一路的分层行数 (同 fab3/locslice_fab3.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译 OCF.Align.TySup, 再 python3 locslice_tysup.py <H> [-v].
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前).
# 参数化模块 TySupFold (R) 经 `open F ICd` 应用, 切片看不见模块应用, 模块内定义手工列为根. 手工根可能有遗漏, 是近似.
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'TySup'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [(A+m,n) for n in ns.split()]
L1=(M('TySupIf','AccR Dc TySupIf')+
    M('TySupC','Cd ofC LC _⊑ᶜ_ _⊏ᶜ_ lvC posC toC topC')+
    M('LFReTy','S⊥ Lv')+
    M('HtTowerTy','KS HB _⊲[_]_ step up _⊞_ sup ι LgB'))
L2=(M('TySupFold','mul chain Σ⁺ caseDc Φ')+
    M('TySupC','wfC goC ⊏→⊑ᶜ lgC↓ᶜ along frA pick decC noKC ICd')+
    M('TySup','TC nat ωc lg-nat lg-ω Tn Tω ord⊥ fghω'))
L3=(M('TySupFold','Sh Sh-⊞ Sh-mul Sh-mulL Sh-chain Sh-Σ Sh-case Sh-Φ')+
    M('TySup','sh→lgB LgB-TC yΩ lg-yΩ TΩΩ LgB-TΩΩ TΩΩ′ fghΩΩ'))
L4=(M('TySup','feed-id above-2 code-feed'))
acc=set(); print('== 无条件闭项 Tn, Tω, TΩΩ (可数层号的 sup 层, 带类型折叠 TySupFold.Φ)')
labs=['定义','折叠 (带类型, 留/坍缩由 cmpB 带公共上界决定, 闭项 Tn/Tω, FGH)','证书 (形状; 回灌作层号的对角 TΩΩ 要证书才能定义)','形状']
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots)
    print('  层%d %s: 本路新增 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),tree(acc),note(acc)))
    if i==3: P3=set(acc)
    if '-v' in sys.argv:
        c=collections.Counter()
        for n in acc: c[n[0].replace(A,'')]+=lines(n)
        print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
print('== 前 3 层闭包里的 GenFold*, KindLv*, StratTw*, NewTwr*, Fab3* 块:', sorted((n[0].replace(A,''),n[1]) for n in P3 if any(n[0].startswith(A+p) for p in ('GenFold','KindLv','StratTw','NewTwr','Fab3'))) or '无')
