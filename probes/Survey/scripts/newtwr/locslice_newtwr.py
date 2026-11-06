# -*- coding: utf-8 -*-
# NewTwr 一路的分层行数 (同 genfold/locslice_genfold.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译一个导入 OCF.Align.NewTwr 的模块, 再 python3 locslice_newtwr.py <H> [-v].
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前), 同 dnfold 脚本.
# 模块应用 NT = Twr N₀ 的实参 N₀ 与参数化模块 (Twr, At, GenFoldRun, GenFoldRd, NewTwrRd, EvAt, Tree, Om) 的模块内定义手工列为根.
# 另外检查: 闭项前 3 层的闭包里是否出现读进 Ht 的定义 (rd₂, evAt, evB, T⁺, TΛ, HtTowerFFold 的模块).
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'NewTwr'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [(A+m,n) for n in ns.split()]
L1=(M('NewTwrIf','LvV RdK RdTower CollK CollGenTy NewTw')+
    M('GenFoldIf','StH NZ NZ₁ AccY DG₊ D Vs Vc ZK DK TopG FBA GenK LgDn FbLgAt FbLg Tg Df St Ig LW')+
    M('HtTowerTy','KS S₀ HB _⊲[_]_ LgB step sup Lev up ι _⊞_')+M('LvKtIf','FN nxt Kc KΛc emb injL ιΛ'))
L2=(M('NewTwrRd','toDᵀ qy cumT flatT rdG rdpG')+
    M('NewTwrColl','Act Y₀ W₁ ΔΩ ΨΩ Tψ one⊞ collG GΛ collΛ')+
    M('NewTwrEv','out₂N evN ρ′ ρ rdN')+
    M('NewTwrK','ordN B inc Bᴧ ΛB Lf TN fghN N₀')+
    M('GenFoldTree','S→⊲ Kup Sk NZ-S nz⊲ nz₁→nz NZ₁-S zkS zΩ outC inC outS inS drp pt sum toD₀ Ωd Pre mkOf Int topStepG ≤rf ≤tr')+
    M('GenFoldRd','nbA lgW≤ rd₁ rdp₁ drp₁')+
    M('GenFoldRun','ω⋅ tg↑ τ₀ τ₁ zeroD _⨾ᴰ_ nlᴰ _⊕⟨_⟩_ cv Stp Ig↾ kk Bu Rk rkS rkT Cl₁ ClA Run Rpt RunNi Ai BNi Chn RKi RunC RKc RKk κc₁ κΔ₁ RKa κcA κΔA')+
    M('GenFoldInst','fbS₀ genS₀ liftFB liftS genStep topSupG genSupNo upd liftℕ liftSℕ genSupℕ genLev genFN genNxt liftL liftSL updL genKc')+
    M('NewTwrEv','two LX W₀X ΩX Act Y₀ out₂'))
L3=(M('NewTwrRd','lWy Lg-cumT Lg-flatT rdG-fst Lg-rdG Lg-rdpG')+
    M('NewTwrColl','lW₁ Lg-Tψ LdΛ flΛ')+M('NewTwrEv','lg-evN lρ′')+M('NewTwrK','lB linc lBᴧ lΛB lLf Lg-TN')+
    M('GenFoldTree','accL accC accᴸ sum-fst Lg-sum Lg-pt')+
    M('GenFoldRd','nbA-mono nbA-fst Lg-nbA rd₁-fst Lg-rd₁ Lg-rdp₁')+
    M('GenFoldInst','ldS₀ ldStep ldSup ldLev flS₀ flLift flStep flSupNo flLiftℕ flSupℕ flLev upd-R upd-Q upd-at ldFN ldNxt flLiftL flNxt ldKc flKc')+
    M('NewTwrEv','lLX oLX eLX lW₀X'))
L4=(M('NewTwrK','B-fst stage-in X B-zero B-suc rd-zero rd-suc B-suc-ev Bᴧ-suc TN-def rd-head0 rd-head rd-not-two cod-suc coord-new twB cod-no-ret hasΛ fin-no-ret lossy-rd base-bot')+
    M('NewTwrEv','evN-head')+M('NewTwrColl','bdΛ')+
    M('NewTwrObs','Kp kp-rf keepSL keepKc keepAt keepSℕ keepΛ OnlyA onlyA-nbA onlyA-rd₁ onlyA-rdp₁ aKΛ')+
    M('NewTwrCmp','coll≡ev₀ LX≡ W₀X≡ ΩX≡ out₂≡'))
acc=set(); print('== 无条件闭项 TN (NT = Twr N₀; 下降 rdN, 坍缩 collΛ)')
labs=['定义','折叠 (读回, 一般折叠, 实例, 下降, 塔, 对角, 闭项, FGH)','证书','律/形状/类型事实/障碍/对照']
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots)
    print('  层%d %s: 本路新增 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),tree(acc),note(acc)))
    if '-v' in sys.argv:
        c=collections.Counter()
        for n in acc: c[n[0].replace(A,'')]+=lines(n)
        print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
    if i==3:
        P3=set(acc)
def names(P): return {(n[0].replace(A,''),chunk(n[0]).chunks[n[1]]['name']) for n in P}
nm=names(P3)
bad=[x for x in nm if x[1] in ('rd₂','rdp₂','evAt','evB','T⁺','TΛ','encH','toD₁') or x[0] in ('HtTowerFFold','HtTowerFClosed','HtTowerFRead')]
print('== 前 3 层闭包里读进 Ht 的定义:', sorted(bad) if bad else '无')
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['NewTwrIf','NewTwrRd','NewTwrColl','NewTwrEv','NewTwrK','NewTwrObs','NewTwrCmp','NewTwr']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
