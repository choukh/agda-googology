# -*- coding: utf-8 -*-
# StratTw 一路的分层行数 (同 kindlv/locslice_kindlv.py 口径: 定义级切片, 计 agda 块里非空非注释行).
# 用法: agda --html --html-highlight=all --html-dir=<H> 编译一个导入 OCF.Align.StratTw 的模块, 再 python3 locslice_strattw.py <H> [-v].
# 基础函数 (chunk, closure, lines, find, NOT) 取 locslice.py 的前半段 (到 B4= 之前), 同 kindlv 脚本.
# 闭项 TS = ColS.Tψ GU LdU flU Λ lΛ one⊲ lvU (模块应用的实参在定义里, 切片看得见; ColS 的模块内定义手工列为根).
# 参数化模块 (StratTwRd.SR, KindLvRun, ColS, EvK, NewTwrRd, GenFoldRd, Tree, Om) 的模块内定义手工列为根.
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
def new(P): return sum(lines(n) for n in P if n[0].startswith(A+'StratTw'))
def kl(P): return sum(lines(n) for n in P if n[0].startswith(A+'KindLv'))
def tree(P): return sum(lines(n) for n in P if n[0] not in NOT)
def note(P): return sum(lines(n) for n in P if n[0] in NOT)
def M(m,ns): return [(A+m,n) for n in ns.split()]
L1=(M('StratTwIf','KMap Sim')+
    M('KindLvIf','Emb lyL KLv LvFb CollLvFbTy')+
    M('GenFoldIf','StH NZ NZ₁ AccY DG₊ D Vs Vc ZK DK TopG FBA GenK LgDn FbLgAt FbLg Tg Df St Ig LW')+
    M('HtTowerTy','KS S₀ HB _⊲[_]_ LgB step sup Lev up ι _⊞_'))
L2=(M('KindLvEmb','idE stepE supE _∘E_ nbJ')+
    M('StratTwRd','lgW≤ Br readS readSp rdSS wrS wrKS')+
    M('KindLvRun','ω⋅ tg↑ τ₀ τ₁ zeroD _⨾ᴰ_ nlᴰ _⊕⟨_⟩_ cv Stp Ig↾ kk Bu Rk rkS rkT Cl₁ ClA Run Rpt RunNi Ai BNi Chn RKi RunC RKc RKk κc₁ κΔ₁ RKv RKa κcL κcA κΔA')+
    M('StratTwTw','Act Y₀ W₁ ΔΩ ΨΩ Tψ Stg QF nxtS st P X C U jP cvP MP Y Sim-⊞ Sim-up Sim-new sim Λ genC GU nw⁺ KA KT lvU TS ordS fghS')+
    M('KindLvEv','Act Y₀ out₂ out₂K evK')+
    M('NewTwrRd','toDᵀ qy cumT flatT rdG rdpG')+
    M('NewTwrEv','two LX W₀X ΩX')+
    M('GenFoldTree','S→⊲ Kup Sk NZ-S nz⊲ nz₁→nz NZ₁-S zkS zΩ outC inC outS inS drp pt sum toD₀ Ωd Pre mkOf Int topStepG ≤rf ≤tr')+
    M('GenFoldRd','nbA lgW≤ rd₁ rdp₁ drp₁')+
    M('GenFoldInst','fbS₀ genS₀ liftFB liftS genStep topSupG genSupNo upd liftℕ liftSℕ genSupℕ genLev'))
L3=(M('KindLvEmb','nbJ-mono nbJ-fst Lg-nbJ LgΩ')+
    M('StratTwRd','readS-fst rdSS-fst Lg-readS Lg-readSp Lg-rdSS')+
    M('KindLvEv','lg-evK')+
    M('StratTwTw','lW₁ Lg-Tψ lY Yfst lΛ one⊲ ldC flC LdU flU Lg-TS')+
    M('NewTwrRd','lWy Lg-cumT Lg-flatT rdG-fst Lg-rdG Lg-rdpG')+
    M('NewTwrEv','lLX oLX eLX lW₀X')+
    M('GenFoldTree','accL accC accᴸ sum-fst Lg-sum Lg-pt')+
    M('GenFoldRd','nbA-mono nbA-fst Lg-nbA rd₁-fst Lg-rd₁ Lg-rdp₁')+
    M('GenFoldInst','ldS₀ ldStep ldSup ldLev flS₀ flLift flStep flSupNo flLiftℕ flSupℕ flLev upd-R upd-Q upd-at'))
L4=(M('StratTwIf','RdSTy WrSTy StratTw Bᴧ ΛS OwnHd')+M('StratTwRd','rdST wrST')+M('StratTwTw','hd StU ownU')+
    M('StratTwCmp','all-heads head-fed KT-ℓ KT-diag KT-ℓ⊲ KT-E KT-rd KT-sees lossy-inner hd-occ start-hd Y-lim KT-top-lossy idM Sim-rf'))
acc=set(); print('== 无条件闭项 TS (分层塔 st, C, U, Y, sim; 坍缩 ColS GU LdU flU Λ lΛ one⊲ lvU)')
labs=['定义','折叠 (沿同形的级读回, 嵌入, 按级回灌的折叠, 分层塔, 对角, 每站求值, 闭项, FGH)','证书','对照, 形状']
for i,(lab,roots) in enumerate(zip(labs,[L1,L2,L3,L4]),1):
    acc=acc|C(roots)
    print('  层%d %s: 本路新增 %d | KindLv 文件 %d | 树侧全部 %d | 记号模块 %d'%(i,lab,new(acc),kl(acc),tree(acc),note(acc)))
    if i==3: P3=set(acc)
    if '-v' in sys.argv:
        c=collections.Counter()
        for n in acc: c[n[0].replace(A,'')]+=lines(n)
        print('      ',', '.join('%s %d'%kv for kv in c.most_common(40)))
R=os.path.abspath(os.path.join(here,'..','..','..'))
print('== 前 3 层闭包里的 GenFoldRun 块:', sorted(n[1] for n in P3 if n[0]==A+'GenFoldRun') or '无')
print('== 前 3 层闭包里的 KindLvRd, LvKtIf, NewTwrColl 块:', sorted((n[0].replace(A,''),n[1]) for n in P3 if n[0] in (A+'KindLvRd',A+'LvKtIf',A+'NewTwrColl')) or '无')
print('== 前 3 层闭包里读进 Ht 的模块块 (HtTowerFTree, HtTowerFFold, HtTowerFClosed, GenFoldEv, GenFoldK, GenFoldRd 的 rd₂):', sorted((n[0].replace(A,''),n[1]) for n in P3 if n[0] in (A+'HtTowerFTree',A+'HtTowerFFold',A+'HtTowerFClosed',A+'GenFoldEv',A+'GenFoldK') or n==(A+'GenFoldRd','rd₂')) or '无')
print('== 各文件代码行 (agda 块非空非注释)')
for m in ['StratTwIf','StratTwRd','StratTwTw','StratTwCmp','StratTw']:
    p=os.path.join(R,'probes','OCF','Align',m+'.lagda.md')
    if not os.path.exists(p): continue
    t=io.open(p,encoding='utf-8').read().split('\n')
    inc=False; n=0
    for l in t:
        st=l.strip()
        if st.startswith('```'): inc=st.startswith('```agda'); continue
        if inc and st and not st.startswith('--'): n+=1
    print('  ',m,n,'/',len(t))
